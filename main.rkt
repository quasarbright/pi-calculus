#lang racket

(module+ test
  (require rackunit))
(provide)

(require (for-syntax syntax/parse))

#|
pi calculus
<process> := noop
           | (out <expr> <expr> <process>)
           | (in <expr> <id> <process>)
           | (branch <process> <process>)
           | (duplicate <process>)
           | (with-channel <id> <process>)

For the runtime, I'm thinking of having a list of processes and doing a scheduler.
The state can be described by a collection of processes and a collection of channels.
A channel is a queue, and the elements of a collection correspond to processes which are executing concurrently.
A process is a sequence of instructions, kind of.
I want the runtime to be synchronous and not rely on racket's async.
I'll keep track of processes waiting on a channel's input.
I could just keep running a process until it blocks, then try other blocked processes and see if anything has been
sent on the channels they are blocking on. But you don't want to leave unblocked threads dead either. That could get complicated.
You could do a thing where you have an instruction queue and you throw the next instruction from each concurrent process into the queue.
And if one is blocked, it stays at the front of the queue.


|#
; rough sketch
#;
(define (run process-queue)
  ; also have to track the updated process queue
  (match (get-next-unblocked-process process-queue)
    [noop (void)]
    [(in chan var proc)
     ; suspend and push this new proc
     ; guaranteed that there will be something in chan,
     ; since this process in unblocked
     (let ([var (channel-pop! chan)])
       proc)]
    [(out chan val proc)
     (channel-push! chan val)
     (process-queue-push! process-queue proc)]
    [(branch proc1 proc2)
     ; push both
     ]
    [(duplicate proc)
     ; push proc and suspended duplicate proc
     ]
    [(with-channel var proc)
     ; suspend and push this
     (let ([var new-channel] proc))]
    [#f (deadlock)]))
#|
idea for representation:
a process is one of
(in channel? (-> any/c process?))
(out channel? any/c)
(with-channel (-> channel? process?))
(branch process? process?)
(duplicate proccess?)

You don't need suspensions because of the lambdas.
There is a global process queue, could be implemented as a parameter.
Channels exist on their own, we don't need to keep track of them. The lambdas will keep track of them.
|#
; sketch with this representation:
; now assuming there is a global/parameter for process queue
#;
(define (run)
  (match (pop-next-unblocked-process!)
    [(noop) (void)]
    [(in chan val->proc)
     (push-process! (val->proc (channel-pop! chan)))]
    [(out chan val proc)
     (channel-push! chan val)
     (push-process! proc)]
    [(with-channel chan->proc)
     (push-process! (chan->proc (new-channel)))]
    [(branch proc1 proc2)
     (push-process! proc1)
     (push-process! proc2)]
    [(duplicate proc)
     (push-process! proc)
     (push-process! (duplicate proc))]))
#|
You can probably just do this with macros only, but i'll do structs to keep it simple.
Macros are still an option though, they'll just expand to code that builds a struct.
Now that I think of it, for use with bindingspec, the struct thing could be nice. You could separate the business
logic from the compile-binder! and the compile-reference stuff.
|#

#;(define process? (or/c #%noop? #%in? #%out? #%with-channel? #%branch? #%duplicate?))
; Represents a concurrent process.

(struct #%noop [] #:transparent)
(define-syntax noop
  (make-set!-transformer
   (syntax-parser
     [noop:id #'(#%noop)])))

(struct #%in [chan val->proc] #:transparent)
(define-syntax-rule (in chan var body ...) (#%in chan (λ (var) body ...)))

(struct #%out [chan val proc] #:transparent)
(define-syntax-rule (out chan val body ...) (#%out chan val (let () body ...)))

(struct #%with-channel [chan->proc] #:transparent)
(define-syntax-rule (with-channel var body ...) (#%with-channel (λ (var) body ...)))

(struct #%branch [proc1 proc2] #:transparent)
(define (branch . procs)
  (foldl #%branch noop procs))

(struct #%duplicate [proc] #:transparent)
(define duplicate #%duplicate)

; examples
(define simple-in-out
  (branch (with-channel chan (branch (in chan x (out out-channel x noop))
                                     (out chan 42 noop)))))

(struct channel [[for-push #:mutable] [for-pop #:mutable]] #:transparent #:constructor-name make-channel)
; Represents a communicateion channel between threads.
; The first element of for-pop is the oldest value and the first element of for-push is the newest value.

; Represents a collection of processes waiting to be ran.
(struct process-queue [processes] #:transparent #:constructor-name make-process-queue)

(define (run proc)
  (channel-clear! out-channel)
  (parameterize ([current-process-queue (make-process-queue (list proc))])
    (let loop ()
      (cond
        [(process-queue-empty? (current-process-queue))
         (void)]
        [(process-queue-all-blocked? (current-process-queue))
         (error 'run "deadlock")]
        [else
         (step!)
         (loop)])))
  (channel->list out-channel))

(define current-process-queue (make-parameter #f))

(define (process-queue-empty? pq)
  (null? (process-queue-processes pq)))

(define (process-queue-all-blocked? pq)
  (for/and ([proc (process-queue-processes pq)])
    (process-blocked? proc)))

; assumes not in deadlock
(define (step!)
  (match (pop-unblocked-process!)
    [(#%noop)
     (void)]
    [(#%in chan val->proc)
     (push-process! (val->proc (channel-pop! chan)))]
    [(#%out chan val proc)
     (channel-push! chan val)
     (push-process! proc)]
    [(#%with-channel chan->proc)
     (push-process! (chan->proc (new-channel)))]
    [(#%branch proc1 proc2)
     (push-process! proc1)
     (push-process! proc2)]
    [(#%duplicate proc)
     (push-process! proc)
     (push-process! (#%duplicate proc))]))

(define (pop-unblocked-process!)
  (let-values ([(proc pq) (process-queue-pop-unblocked (current-process-queue))])
    (current-process-queue pq)
    proc))

(define (push-process! proc)
  (current-process-queue (process-queue-push (current-process-queue) proc)))

(define (new-process-queue)
  (make-process-queue '()))

(define (process-queue-push pq proc) (make-process-queue (append (process-queue-processes pq) (list proc))))

(define (process-queue-pop-unblocked pq)
  (let loop ([skipped-rev '()] [processes (process-queue-processes pq)])
    (cond
      [(null? rest) (error 'process-queue-pop-unblocked "cannot pop from empty process queue")]
      [(process-blocked? (first processes)) (loop (cons (first processes) skipped-rev) (rest processes))]
      [else (values (first processes) (make-process-queue (append (reverse skipped-rev) (rest processes))))])))

; branches aren't blocked, even if all alternatives are blocked.
; This is because the act of branching is a non-blocking instruction.
(define (process-blocked? proc)
  (match proc
    [(#%in chan _) (channel-empty? chan)]
    [else #f]))

(define (new-channel) (make-channel '() '()))

(define (channel-clear! channel)
  (set-channel-for-pop! channel '())
  (set-channel-for-push! channel '()))

; this channel's contents will be returned when a process completes.
(define out-channel (new-channel))

(define (channel->list chan)
  (channel-transfer! chan)
  (channel-for-pop chan))

(define (channel-pop! chan)
  (when (channel-empty? chan)
    (error 'channel-pop! "cannot pop from empty channel"))
  (when (null? (channel-for-pop chan))
    (channel-transfer! chan))
  (match (channel-for-pop chan)
    [(cons val for-pop^)
     (set-channel-for-pop! chan for-pop^)
     val]))

(define (channel-empty? chan)
  (and (null? (channel-for-pop chan)) (null? (channel-for-push chan))))

(define (channel-transfer! chan)
  (match chan
    [(channel for-pop for-push)
     (set-channel-for-pop! chan (append for-pop (reverse for-push)))
     (set-channel-for-push! chan '())]))

(define (channel-push! chan val)
  (set-channel-for-push! chan (cons val (channel-for-push chan))))

(define-syntax-rule (for/branch clauses body ...) (apply branch (for/list clauses body ...)))



(module+ test
  (check-equal? (run noop) '())
  (check-equal? (run (with-channel chan noop)) '())
  (check-equal? (run simple-in-out) '(42))
  (check-exn #rx"deadlock" (thunk (run (with-channel chan (in chan x noop)))))
  (check-exn #rx"deadlock" (thunk (run (with-channel chan (in chan x (out chan 42 noop))))))
  ; this loops
  ; I don't think it's possible to write this in a way that makes it terminate. Furthermore, I can't think of a non-trivial terminating example
  ; using 'duplicate' at all without cheating.
  ; The reason this doesn't terminate is because even when the list is empty, duplicate will still try to read input. It'll noop if it's
  ; empty, but the 'in' will still get duplicated.
  #;(check-equal? (run (with-channel chan (branch (out chan '(1 2 3 4) noop)
                                                (duplicate (in chan nums (if (null? nums)
                                                                             noop
                                                                             (out out-channel (first nums)
                                                                                  (out chan (rest nums) noop))))))))
                '(1 2 3 4))
  (check-equal? (run (with-channel chan (branch (out chan '(1 2 3 4) noop)
                                                (in chan nums (apply branch (map (λ (num) (out out-channel num noop)) nums))))))
                '(1 2 3 4))
  (check-equal? (run (with-channel chan (branch (out chan '(1 2 3 4) noop)
                                                (in chan nums (for/branch ([num nums]) (out out-channel num noop))))))
                '(1 2 3 4)))
