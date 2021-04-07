;{{{ Macro
(define-syntax defopt
  (syntax-rules ()
    [(_ (p x ... [y e]) b1 b2 ...)
     (define p
       (case-lambda
         [(x ...) (p x ... e)]
         [(x ... y) b1 b2 ...]))]))
;}}}

;{{{ Skew Heap
(module sh%
    (make-sh sh-show sh-empty? sh-merge! sh-push! sh-pop!
     sh-node sh-mutate! sh-delete! list->sh)
;{{{ New heap
(defopt (make-sh [p <])
  (list p))
;}}}
;{{{ Print tree
(defopt (sh-show sh [tab '(1 3 1)])
  (let* ([h #\x2500] [v #\x2502] [u #\x250c] [d #\x2514]
         ;[h #\-] [v #\|] [u #\/] [d #\\]
         [s #\space] [str "~a\x1b;[1m~a\x1b;[m~%"]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [sp (make-string (+ nps ns nss) s)] [hh (make-string (1- ns) h)]
         [ps (make-string nps s)] [ss (make-string nss s)]
         [uh (string-append ps (make-string 1 u) hh ss)]
         [dh (string-append ps (make-string 1 d) hh ss)]
         [vs (string-append ps (make-string 1 v) (make-string (1- ns) s) ss)])
    (let loop ([st (cdr sh)] [lsp ps] [csp ps] [rsp ps])
      (unless (null? st)
        (loop (cadr st)
              (string-append lsp sp)
              (string-append lsp uh)
              (string-append lsp vs))
        (printf str csp (car st))
        (loop (cddr st)
              (string-append rsp vs)
              (string-append rsp dh)
              (string-append rsp sp))))))
;}}}
;{{{ Empty test
(define (sh-empty? sh)
  (null? (cdr sh)))
;}}}
;{{{ Merge heap
(define ($sh-merge! sh dt)
  (let ([lt? (car sh)])
    (unless (null? dt)
      (set-cdr! sh
        (let ([n1 (cons '() (cons '() (cdr sh)))])
          (let loop ([n1 n1] [n2 dt])
            (let ([nr (cddr n1)])
              (set-cdr! (cdr n1) (cadr n1))
              (if (null? nr) (set-car! (cdr n1) n2)
                (let-values ([(n2 nr)
                      (if (lt? (car n2) (car nr))
                        (values n2 nr) (values nr n2))])
                  (set-car! (cdr n1) n2)
                  (loop n2 nr)))))
          (cadr n1)))))
  sh)

(define (sh-merge! s1 s2)
  (if (not (equal? (car s1) (car s2)))
    (error 'sh-merge! "Incompatible order type"))
  ($sh-merge! s1 (cdr s2)))
;}}}
;{{{ Push to heap
(define (sh-push! sh x)
  ($sh-merge! sh (list x '())))
;}}}
;{{{ Pop from heap
(define (sh-pop! sh)
  (let ([n (cdr sh)])
    (if (null? n)
      (error 'sh-pop! "Empty heap"))
    (set-cdr! sh (cadr n))
    ($sh-merge! sh (cddr n))
    (car n)))
;}}}
;{{{ Search for a node in heap
(define (sh-node sh p?)
  (let loop ([n (cdr sh)])
    (if (null? n) #f
      (if (p? (car n)) n
        (or (loop (cadr n))
            (loop (cddr n)))))))

(define ($sh-trace sh p?)
  (let loop ([n (cdr sh)])
    (if (null? n) '()
      (if (p? (car n)) (list n)
        (let ([l (loop (cadr n))])
          (if (null? l)
            (let ([l (loop (cddr n))])
              (if (null? l) '()
                (cons n l)))
            (cons n l)))))))
;}}}
;{{{ Mutate a node in heap
(define ($sh-adjust-increase! tr lt?)
  (let* ([mh (car (last-pair tr))] [m (car mh)])
    (let loop ([mh mh])
      (let ([l (cadr mh)] [r (cddr mh)])
        (cond [(cond
            [(and (null? l) (null? r)) #f]
            [(null? l) r] [(null? r) l]
            [else (if (lt? (car r) (car l)) r l)])
          => (lambda (d)
               (when (lt? (car d) m)
                 (set-car! mh (car d))
                 (set-car! d m)
                 (loop d)))])))))

(define ($sh-adjust-decrease! tr lt?)
  (let* ([l (reverse tr)] [m (caar l)])
    (let loop ([l l])
      (let ([ll (cdr l)])
        (if (and (not (null? ll)) (lt? m (caar ll)))
          (begin
            (set-car! (car l) (caar ll)) (loop ll))
          (set-car! (car l) m))))))

(define (sh-mutate! sh p? mutator)
  (let ([tr ($sh-trace sh p?)])
    (if (null? tr) #f
      (let ([lt? (car sh)] [t0 (car (last-pair tr))])
        (cond [(let-values ([(v mutate) (mutator (car t0))])
            (let-syntax ([prog1 (syntax-rules ()
                [(_ v body ...) (let ([v& v]) body ... v&)])])
              (cond
                [(not mutate) (prog1
                 (cond [(lt? (car t0) v) $sh-adjust-increase!]
                       [(lt? v (car t0)) $sh-adjust-decrease!]
                       [else #f])
                 (set-car! t0 v))]
                [(procedure? mutate) (prog1
                 (let ([v0 ((mutate 'accessor) (car t0))]
                       [lt? (mutate 'lt)])
                   (cond [(lt? v0 v) $sh-adjust-increase!]
                         [(lt? v v0) $sh-adjust-decrease!]
                         [else #f]))
                 ((mutate 'mutator) (car t0) v))]
                [(real? mutate)
                 (cond [(positive? mutate) $sh-adjust-increase!]
                       [(negative? mutate) $sh-adjust-decrease!]
                       [else #f])]
                [else $sh-adjust-decrease!])))
          => (lambda (f) (f tr lt?))])
        sh))))
;}}}
;{{{ Delete a node in heap
(define (sh-delete! sh p?)
  (let ([tr ($sh-trace sh p?)])
    (if (null? tr) #f
      (let ([n (cdr sh)])
        (let loop ([l (reverse! tr)])
          (let ([ll (cdr l)])
            (unless (null? ll)
              (set-car! (car l) (caar ll))
              (loop ll))))
        (set-cdr! sh (cadr n))
        ($sh-merge! sh (cddr n))
        sh))))
;}}}
;{{{ Make heap from list
(defopt (list->sh l [op #f])
  (fold-left (lambda (x y) (sh-push! x y))
    (if op (make-sh op) (make-sh)) l))
;}}}
)
;}}}
;{{{ Leftist Heap
(module lh%
    (make-lh lh-show lh-empty? lh-merge! lh-push! lh-pop!
     lh-node lh-mutate! lh-delete! list->lh)
;{{{ Macro
(define-syntax level-left
  (syntax-rules ()
    [(_ n)
     (if (null? (cadr n)) -1
       (cdaadr n))]))

(define-syntax level-right
  (syntax-rules ()
    [(_ n)
     (if (null? (cddr n)) -1
       (cdaddr n))]))
;}}}

;{{{ New heap
(defopt (make-lh [p <])
  (list p))
;}}}
;{{{ Print tree
(defopt (lh-show lh [tab '(1 3 1)])
  (let* ([h #\x2500] [v #\x2502] [u #\x250c] [d #\x2514]
         ;[h #\-] [v #\|] [u #\/] [d #\\]
         [s #\space] [str "~a\x1b;[3~d;1m~a\x1b;[m~%"]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [sp (make-string (+ nps ns nss) s)] [hh (make-string (1- ns) h)]
         [ps (make-string nps s)] [ss (make-string nss s)]
         [uh (string-append ps (make-string 1 u) hh ss)]
         [dh (string-append ps (make-string 1 d) hh ss)]
         [vs (string-append ps (make-string 1 v) (make-string (1- ns) s) ss)])
    (let loop ([st (cdr lh)] [lsp ps] [csp ps] [rsp ps])
      (unless (null? st)
        (loop (cadr st)
              (string-append lsp sp)
              (string-append lsp uh)
              (string-append lsp vs))
        (printf str csp
                (let ([delta (- (level-left st) (level-right st))])
                  (cond [(positive? delta) 3] [(zero? delta) 9] [else 0]))
                (caar st))
        (loop (cddr st)
              (string-append rsp vs)
              (string-append rsp dh)
              (string-append rsp sp))))))
;}}}
;{{{ Empty test
(define (lh-empty? lh)
  (null? (cdr lh)))
;}}}
;{{{ Merge heap
(define ($lh-merge! lh dt)
  (let ([lt? (car lh)])
    (set-cdr! lh
      (let loop ([n1 (cdr lh)] [n2 dt])
        (cond [(null? n1) n2] [(null? n2) n1] [else
            (let-values ([(n1 n2)
                (if (lt? (caar n1) (caar n2))
                  (values n1 n2) (values n2 n1))])
              (let* ([v0 (level-right n1)]
                     [n (loop (cddr n1) n2)]
                     [v (cdar n)])
                (if (< (level-left n1) v)
                  (begin
                    (set-cdr! (cdr n1) (cadr n1))
                    (set-car! (cdr n1) n))
                  (set-cdr! (cdr n1) n))
                (unless (= v0 v)
                  (set-cdr! (car n1)
                    (1+ (level-right n1)))))
              n1)]))))
  lh)

(define (lh-merge! l1 l2)
  (if (not (equal? (car l1) (car l2)))
    (error 'lh-merge! "Incompatible order type"))
  ($lh-merge! l1 (cdr l2)))
;}}}
;{{{ Push to heap
(define (lh-push! lh x)
  ($lh-merge! lh (list (cons x 0) '())))
;}}}
;{{{ Pop from heap
(define (lh-pop! lh)
  (let ([n (cdr lh)])
    (if (null? n)
      (error 'lh-pop! "Empty heap"))
    (set-cdr! lh (cadr n))
    ($lh-merge! lh (cddr n))
    (caar n)))
;}}}
;{{{ Search for a node in heap
(define (lh-node lh p?)
  (let loop ([n (cdr lh)])
    (if (null? n) #f
      (if (p? (caar n)) n
        (or (loop (cadr n))
            (loop (cddr n)))))))

(define ($lh-trace lh p?)
  (let loop ([n (cdr lh)])
    (if (null? n) '()
      (if (p? (caar n)) (list n)
        (let ([l (loop (cadr n))])
          (if (null? l)
            (let ([l (loop (cddr n))])
              (if (null? l) '()
                (cons n l)))
            (cons n l)))))))
;}}}
;{{{ Mutate a node in heap
(define ($lh-adjust-increase! tr lt?)
  (let* ([mh (car (last-pair tr))] [m (caar mh)])
    (let loop ([mh mh])
      (let ([l (cadr mh)] [r (cddr mh)])
        (cond [(cond
            [(and (null? l) (null? r)) #f]
            [(null? l) r] [(null? r) l]
            [else (if (lt? (caar r) (caar l)) r l)])
          => (lambda (d)
               (when (lt? (caar d) m)
                 (set-car! (car mh) (caar d))
                 (set-car! (car d) m)
                 (loop d)))])))))

(define ($lh-adjust-decrease! tr lt?)
  (let* ([l (reverse tr)] [m (caaar l)])
    (let loop ([l l])
      (let ([ll (cdr l)])
        (if (and (not (null? ll)) (lt? m (caaar ll)))
          (begin
            (set-car! (caar l) (caaar ll)) (loop ll))
          (set-car! (caar l) m))))))

(define (lh-mutate! lh p? mutator)
  (let ([tr ($lh-trace lh p?)])
    (if (null? tr) #f
      (let ([lt? (car lh)] [t0 (car (last-pair tr))])
        (cond [(let-values ([(v mutate) (mutator (caar t0))])
            (let-syntax ([prog1 (syntax-rules ()
                [(_ v body ...) (let ([v& v]) body ... v&)])])
              (cond
                [(not mutate) (prog1
                 (cond [(lt? (caar t0) v) $lh-adjust-increase!]
                       [(lt? v (caar t0)) $lh-adjust-decrease!]
                       [else #f])
                 (set-car! (car t0) v))]
                [(procedure? mutate) (prog1
                 (let ([v0 ((mutate 'accessor) (caar t0))]
                       [lt? (mutate 'lt)])
                   (cond [(lt? v0 v) $lh-adjust-increase!]
                         [(lt? v v0) $lh-adjust-decrease!]
                         [else #f]))
                 ((mutate 'mutator) (caar t0) v))]
                [(real? mutate)
                 (cond [(positive? mutate) $lh-adjust-increase!]
                       [(negative? mutate) $lh-adjust-decrease!]
                       [else #f])]
                [else $lh-adjust-decrease!])))
          => (lambda (f) (f tr lt?))])
        lh))))
;}}}
;{{{ Delete a node in heap
(define (lh-delete! lh p?)
  (let ([tr ($lh-trace lh p?)])
    (if (null? tr) #f
      (let ([n (cdr lh)])
        (let loop ([l (reverse! tr)])
          (let ([ll (cdr l)])
            (unless (null? ll)
              (set-car! (caar l) (caaar ll))
              (loop ll))))
        (set-cdr! lh (cadr n))
        ($lh-merge! lh (cddr n))
        lh))))
;}}}
;{{{ Make heap from list
(defopt (list->lh l [op #f])
  (fold-left (lambda (x y) (lh-push! x y))
    (if op (make-lh op) (make-lh)) l))
;}}}
)
;}}}
;{{{ Binomial Heap
(module bh%
    (make-bh bh-show bh-empty? bh-merge! bh-push! bh-pop!
     bh-node bh-mutate! bh-delete! list->bh)
;{{{ New heap
(defopt (make-bh [p <])
  (list p))
;}}}
;{{{ Print heap
(defopt (bh-show bh [tab '(1 3 1)])
  (let* ([h #\x2500] [v #\x2502] [u #\x251c] [d #\x2514]
         ;[h #\-] [v #\|] [u #\|] [d #\\]
         [s #\space] [str "~a\x1b;[1m~a\x1b;[m~%"]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [sp (make-string (+ nps ns nss) s)] [hh (make-string (1- ns) h)]
         [ps (make-string nps s)] [ss (make-string nss s)]
         [uh (string-append ps (make-string 1 u) hh ss)]
         [dh (string-append ps (make-string 1 d) hh ss)]
         [vs (string-append ps (make-string 1 v) (make-string (1- ns) s) ss)])
    (unless (null? (cdr bh))
      (let loop ([st (cdr bh)] [par (cons ps ps)] [pdr (cons ps ps)])
        (let count ([st st])
          (let* ([f (null? (cdr st))] [pr (if f par pdr)])
            (printf str (car pr) (caar st))
            (unless (null? (cdar st))
              (loop (cdar st)
                    (cons (string-append (cdr pr) dh)
                          (string-append (cdr pr) sp))
                    (cons (string-append (cdr pr) uh)
                          (string-append (cdr pr) vs))))
            (unless f (count (cdr st)))))))))
;}}}
;{{{ Empty test
(define (bh-empty? bh)
  (null? (cdr bh)))
;}}}
;{{{ Merge heap
(define ($bh-merge! bh dt)
  (let ([lt? (car bh)])
    (set-cdr! bh
      (let loop ([n1 (cdr bh)] [n2 dt] [f #f])
        (cond [(null? n1) n2] [(null? n2) n1]
              [else
          (let ([s1 (length (cdar n1))] [s2 (length (cdar n2))])
            (if (= s1 s2)
              (cons
                (let-values ([(t1 t2)
                    (if (lt? (caar n1) (caar n2))
                      (values (car n1) (car n2))
                      (values (car n2) (car n1)))])
                  (set-cdr! t1 (cons t2 (cdr t1)))
                  t1)
                (loop (cdr n1) (cdr n2) #f))
              (let-values ([(n1 n2)
                  (if (< s1 s2) (values n2 n1) (values n1 n2))])
                (let ([n (loop (cdr n1) n2 #f)])
                  (if f
                    (begin (set-cdr! n1 n) n1)
                    (loop (list (car n1)) n #t))))))]))))
  bh)

(define (bh-merge! b1 b2)
  (if (not (equal? (car b1) (car b2)))
    (error 'bh-merge! "Incompatible order type"))
  ($bh-merge! b1 (cdr b2)))
;}}}
;{{{ Push to heap
(define (bh-push! bh x)
  ($bh-merge! bh (list (list x))))
;}}}
;{{{ Pop from heap
(define ($bh-min bh lt?)
  (let ([m #f] [mt '()])
    (let loop ([last bh])
      (let ([tree (cdr last)])
        (unless (null? tree)
          (let ([v (caar tree)])
            (when (or (null? mt) (lt? v m))
              (set! mt last) (set! m v)))
          (loop tree))))
    (values m mt)))

(define (bh-pop! bh)
  (let-values ([(m mt) ($bh-min bh (car bh))])
    (if (null? mt)
      (error 'bh-pop! "Empty heap"))
    (let ([d (cdadr mt)])
      (set-cdr! mt (cddr mt))
      ($bh-merge! bh d))
    m))
;}}}
;{{{ Search for a node in heap
(define (bh-node bh p?)
  (let loop ([n (cdr bh)])
    (let count ([n n])
      (if (null? n) #f
        (if (p? (caar n)) n
          (or (loop (cdar n))
              (count (cdr n))))))))

(define ($bh-trace bh p?)
  (let loop ([last bh])
    (let count ([last last])
      (let ([n (cdr last)])
        (if (null? n) '()
          (if (p? (caar n)) (list last)
            (let ([l (loop (car n))])
              (if (null? l) (count n)
                (cons last l)))))))))
;}}}
;{{{ Mutate a node in heap
(define ($bh-adjust-increase! tr lt?)
  (let* ([mh (cadar (last-pair tr))] [mm (car mh)])
    (let loop ([mh mh])
      (let-values ([(m mt) ($bh-min mh lt?)])
        (if (and (not (null? mt)) (lt? m mm))
          (let ([mt (cadr mt)])
            (set-car! mh m) (loop mt))
          (set-car! mh mm))))))

(define ($bh-adjust-decrease! tr lt?)
  (let* ([l (reverse! (map cadr tr))] [m (caar l)])
    (let loop ([l l])
      (let ([ll (cdr l)])
        (if (and (not (null? ll)) (lt? m (caar ll)))
          (begin
            (set-car! (car l) (caar ll)) (loop ll))
          (set-car! (car l) m))))))

(define (bh-mutate! bh p? mutator)
  ;;     `mutator` is a procedure that takes in an argument `v0`
  ;; standing for the data to be mutated and returns multi-values
  ;; `v mutate`.
  ;;     If `mutate` is `#f`, then `v` is treated as the new data.
  ;;     If `mutate` is a procedure, then it takes in a symbol and
  ;; returns a procedure:
  ;;   * `(mutate 'accessor)` gives the accessor of the priority
  ;;     value of data;
  ;;   * `(mutate 'mutator)` gives the mutator of the priority
  ;;     value of data;
  ;;   * `(mutate 'lt)` gives the less-than predicate of the priority
  ;;     value;
  ;; and `v` is treated as the new priority value.
  ;;     In the cases below, the data should be mutated by the
  ;; procedure `mutator`.
  ;;     If `mutate` is a real number, then its sign is used to
  ;; determine whether the priority value is to be increased or
  ;; decreased.
  ;;     In other cases, the priority value is viewed to be decreased.
  (let ([tr ($bh-trace bh p?)])
    (if (null? tr) #f
      (let ([lt? (car bh)] [adjust! $bh-adjust-decrease!]
            [t0 (cadar (last-pair tr))])
        (let-values ([(v mutate) (mutator (car t0))])
          (cond
            [(not mutate)
             (if (lt? (car t0) v)
               (set! adjust! $bh-adjust-increase!)
               (if (not (lt? v (car t0)))
                 (set! adjust! #f)))
             (set-car! t0 v)]
            [(procedure? mutate)
             (let ([v0 ((mutate 'accessor) (car t0))]
                   [lt? (mutate 'lt)])
               (if (lt? v0 v)
                 (set! adjust! $bh-adjust-increase!)
                 (if (not (lt? v v0))
                   (set! adjust! #f))))
             ((mutate 'mutator) (car t0) v)]
            [(real? mutate)
             (if (positive? mutate)
               (set! adjust! $bh-adjust-increase!)
               (if (zero? mutate)
                 (set! adjust! #f)))]))
        (if adjust! (adjust! tr lt?))
        bh))))
;}}}
;{{{ Delete a node in heap
(define (bh-delete! bh p?)
  (let ([tr ($bh-trace bh p?)])
    (if (null? tr) #f
      (let ([mt (car tr)] [d (cdadar tr)])
        (let loop ([l (reverse! (map cadr tr))])
          (let ([ll (cdr l)])
            (unless (null? ll)
              (set-car! (car l) (caar ll))
              (loop ll))))
        (set-cdr! mt (cddr mt))
        ($bh-merge! bh d)
        bh))))
;}}}
;{{{ Make heap from list
(defopt (list->bh l [op #f])
  (fold-left (lambda (x y) (bh-push! x y))
    (if op (make-bh op) (make-bh)) l))
;}}}
)
;}}}
;{{{ Fibonacci Heap
(module fh%
    (make-fh fh-show fh-empty? fh-merge! fh-push! fh-pop!
     fh-node fh-mutate! fh-delete! list->fh)
;{{{ Macro
(define-syntax list*&
  (lambda (x)
    (syntax-case x ()
      [(_ head) #'(list* head)]
      [(name head remain ...)
       (with-syntax ([& (datum->syntax #'name '&)])
         #'(let* ([& (list '())] [head& head]
                  [remain& (list* remain ...)])
             (set-car! & head&)
             (set-cdr! & remain&)
             &))])))
(define-syntax list&
  (lambda (x)
    (syntax-case x ()
      [(name elems ...)
       (datum->syntax #'name (syntax->datum
         #'(list*& elems ... '())))])))
(define-syntax cons&
  (lambda (x)
    (syntax-case x ()
      [(name a b)
       (datum->syntax #'name (syntax->datum
         #'(list*& a b)))])))

(define-syntax make-lr
  (syntax-rules (nil)
    [(_ nil r)
     (set-car! (cddr r) '())]
    [(_ l nil)
     (set-cdr! (cddr l) '())]
    [(_ l r)
     (let ([l& l] [r& r])
       (set-cdr! (cddr l&) r&)
       (set-car! (cddr r&) l&))]))
(define-syntax make-ud
  (syntax-rules (nil)
    [(_ nil d)
     (set-car! (cadr d) '())]
    [(_ u nil)
     (set-cdr! (cadr u) '())]
    [(_ u d)
     (let ([u& u] [d& d])
       (set-cdr! (cadr u&) d&)
       (set-car! (cadr d&) u&))]))
;}}}
;{{{ Reusable vector
(define ($make-rvector n)
  (let ([i 0] [vec '#()])
    (lambda (operation)
      (case operation
        [size (lambda (size)
          (let ([old-size (vector-length vec)])
            (if (and (<= size old-size) (< i (1- n)))
              (set! i (1+ i))
              (let ([new-size
                  (if (or (zero? old-size)
                          (<= size old-size))
                    size
                    (let loop ([s old-size])
                      (if (>= s size) s
                        (loop (ceiling (* s 3/2))))))])
                (set! i 0)
                (set! vec (make-vector new-size #f))))))]
        [ref (lambda (index)
          (let ([l (vector-ref vec index)])
            (and l (= i (car l)) (cdr l))))]
        [set! (lambda (index v)
          (vector-set! vec index (cons i v)))]))))
(define $rvector ($make-rvector 1024))
(define $rvector-size ($rvector 'size))
(define $rvector-ref ($rvector 'ref))
(define $rvector-set! ($rvector 'set!))
;}}}

;{{{ New heap
(defopt (make-fh [p <])
  (list (cons p 0)))
;}}}
;{{{ Print heap
(defopt (fh-show fh [tab '(1 3 1)])
  (let* ([h #\x2500] [v #\x2502] [u #\x251c] [d #\x2514]
         ;[h #\-] [v #\|] [u #\|] [d #\\]
         [s #\space] [str "~a\x1b;[3~d;1m~a\x1b;[m~%"]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [sp (make-string (+ nps ns nss) s)] [hh (make-string (1- ns) h)]
         [ps (make-string nps s)] [ss (make-string nss s)]
         [uh (string-append ps (make-string 1 u) hh ss)]
         [dh (string-append ps (make-string 1 d) hh ss)]
         [vs (string-append ps (make-string 1 v) (make-string (1- ns) s) ss)])
    (unless (null? (cdr fh))
      (let loop ([head (cdr fh)] [par (cons ps ps)] [pdr (cons ps ps)])
        (let count ([st head])
          (let* ([f (eq? (cdddr st) head)] [pr (if f par pdr)])
            (printf str (car pr) (if (cddar st) 3 9) (caar st))
            (unless (null? (cdadr st))
              (loop (cdadr st)
                    (cons (string-append (cdr pr) dh)
                          (string-append (cdr pr) sp))
                    (cons (string-append (cdr pr) uh)
                          (string-append (cdr pr) vs))))
            (unless f (count (cdddr st)))))))))
;}}}
;{{{ Empty test
(define (fh-empty? fh)
  (null? (cdr fh)))
;}}}
;{{{ Merge heap
(define ($fh-merge! fh dt)
  (unless (null? dt)
    (let ([lt? (caar fh)] [n1 (cdr fh)] [n2 dt])
      (if (null? n1) (set-cdr! fh n2)
        (let-values ([(n1 n2)
            (if (lt? (caar n1) (caar n2)) (values n1 n2)
              (begin (set-cdr! fh n2) (values n2 n1)))])
          (let ([n1t (caddr n1)] [n2t (caddr n2)])
            (make-lr n2t n1)
            (make-lr n1t n2))))))
  fh)

(define (fh-merge! f1 f2)
  (if (not (equal? (caar f1) (caar f2)))
    (error 'fh-merge! "Incompatible order type"))
  (set-cdr! (car f1) (+ (cdar f1) (cdar f2)))
  ($fh-merge! f1 (cdr f2)))
;}}}
;{{{ Push to heap
(define (fh-push! fh x)
  (set-cdr! (car fh) (1+ (cdar fh)))
  ($fh-merge! fh (list*& (list* x 0 #f) (list '()) & &)))
;}}}
;{{{ Pop from heap
(define ($fh-extract! mt)
  (let ([mtd (cdadr mt)])
    (let-values ([(ml mr) (if (eq? (caddr mt) mt)
        (values (caddr mtd) mtd)
        (values (caddr mt) (cdddr mt)))])
      (if (null? mtd)
        (make-lr ml mr)
        (begin
          (make-lr ml mtd)
          (let loop ([n mtd])
            (make-ud nil n)
            (set-cdr! (cdar n) #f)
            (if (eq? (cdddr n) mtd)
              (make-lr n mr)
              (loop (cdddr n))))))
      mr)))

(define ($fh-consolidate! fh)
  (let ([lt? (caar fh)] [mt (cdr fh)])
    ($rvector-size (1+ (exact (floor
                   (log (cdar fh) (/ (1+ (sqrt 5)) 2))))))
    (let loop ([n mt])
      (let* ([r (cdddr n)] [f (eq? r mt)] [nr (let loop ([n n])
          (cond [($rvector-ref (cadar n))
            => (lambda (m)
                 (let-values ([(n1 n2)
                     (if (lt? (caar n) (caar m))
                       (values n m) (values m n))])
                   (let ([n (cadar n1)])
                     ($rvector-set! n #f)
                     (set-car! (cdar n1) (1+ n)))
                   (let ([n1d (cdadr n1)])
                     (make-ud n1 n2)
                     (set-cdr! (cdar n2) #f)
                     (make-lr (caddr n2) (cdddr n2))
                     (if (eq? n2 mt)
                       (set! mt (cdddr n2)))
                     (if (null? n1d)
                       (make-lr n2 n2)
                       (begin
                         (make-lr (caddr n1d) n2)
                         (make-lr n2 n1d))))
                   (loop n1)))]
                [else ($rvector-set! (cadar n) n) n]))])
        (if (and (eq? nr n) (lt? (caar n) (caadr fh)))
          (set-cdr! fh n))
        (if (not f) (loop r))))))

(define (fh-pop! fh)
  (let ([mt (cdr fh)])
    (if (null? mt)
      (error 'fh-pop! "Empty heap"))
    (let ([m (caar mt)] [n (1- (cdar fh))])
      (set-cdr! (car fh) n)
      (if (zero? n) (set-cdr! fh '())
        (begin
          (set-cdr! fh ($fh-extract! mt))
          ($fh-consolidate! fh)))
      m)))
;}}}
;{{{ Search for a node in heap
(define (fh-node fh p?)
  (let loop ([head (cdr fh)])
    (let count ([n head])
      (if (null? n) #f
        (if (p? (caar n)) n
          (or (loop (cdadr n))
              (if (eq? (cdddr n) head) #f
                (count (cdddr n)))))))))
;}}}
;{{{ Mutate a node in heap
(define ($fh-cut! fh node)
  (unless (null? (caadr node))
    (let loop ([node node])
      (let ([p (caadr node)])
        (let ([deg (1- (cadar p))])
          (set-car! (cdar p) deg)
          (if (eq? (cdadr p) node)
            (if (zero? deg)
              (make-ud p nil)
              (make-ud p (cdddr node))))
          (if (positive? deg)
            (make-lr (caddr node) (cdddr node))))
        (set-cdr! (cdar node) #f)
        (make-ud nil node)
        (make-lr (cadddr fh) node)
        (make-lr node (cdr fh))
        (unless (null? (caadr p))
          (if (cddar p) (loop p)
            (set-cdr! (cdar p) #t)))))))

(define ($fh-adjust-increase! fh node)
  (let ([s (cdadr node)] [lt? (caar fh)] [m (caar node)])
    (unless (null? s)
      (let loop ([n (cdddr s)])
        (let ([r (cdddr n)])
          (if (lt? (caar n) m)
            ($fh-cut! fh n))
          (if (not (eq? n s))
            (loop r)))))
    (if (eq? (cdr fh) node)
      ($fh-consolidate! fh))))

(define ($fh-adjust-decrease! fh node)
  (let ([p (caadr node)] [lt? (caar fh)] [m (caar node)])
    (unless (null? p)
      (if (lt? m (caar p))
        ($fh-cut! fh node)))
    (if (lt? m (caadr fh))
      (set-cdr! fh node))))

(define ($fh-mutate! fh node mutator)
  (let ([lt? (caar fh)])
    (cond [(let-values ([(v mutate) (mutator (caar node))])
        (let-syntax ([prog1 (syntax-rules ()
            [(_ v body ...) (let ([v& v]) body ... v&)])])
          (cond
            [(not mutate) (prog1
             (cond [(lt? (caar node) v) $fh-adjust-increase!]
                   [(lt? v (caar node)) $fh-adjust-decrease!]
                   [else #f])
             (set-car! (car node) v))]
            [(procedure? mutate) (prog1
             (let ([v0 ((mutate 'accessor) (caar node))]
                   [lt? (mutate 'lt)])
               (cond [(lt? v0 v) $fh-adjust-increase!]
                     [(lt? v v0) $fh-adjust-decrease!]
                     [else #f]))
             ((mutate 'mutator) (caar node) v))]
            [(real? mutate)
             (cond [(positive? mutate) $fh-adjust-increase!]
                   [(negative? mutate) $fh-adjust-decrease!]
                   [else #f])]
            [else $fh-adjust-decrease!])))
      => (lambda (f) (f fh node))])
    fh))

(define (fh-mutate! fh p? mutator)
  (let ([node (fh-node fh p?)])
    (and node ($fh-mutate! fh node mutator))))
;}}}
;{{{ Delete a node in heap
(define ($fh-delete! fh node)
  (if (eq? (cdr fh) node)
    (fh-pop! fh)
    (begin
      ($fh-cut! fh node)
      (set-cdr! (car fh) (1- (cdar fh)))
      ($fh-extract! node)))
  fh)

(define (fh-delete! fh p?)
  (let ([node (fh-node fh p?)])
    (and node ($fh-delete! fh node))))
;}}}
;{{{ Make heap from list
(defopt (list->fh l [op #f])
  (fold-left (lambda (x y) (fh-push! x y))
    (if op (make-fh op) (make-fh)) l))
;}}}
)
;}}}
;{{{ Pairing Heap
(module ph%
    (make-ph ph-show ph-empty? ph-merge! ph-push! ph-pop!
     ph-node ph-mutate! ph-delete! list->ph)
;{{{ New heap
(defopt (make-ph [p <])
  (cons p #f))
;}}}
;{{{ Print heap
(defopt (ph-show ph [tab '(1 3 1)])
  (let* ([h #\x2500] [v #\x2502] [u #\x251c] [d #\x2514]
         ;[h #\-] [v #\|] [u #\|] [d #\\]
         [s #\space] [str "~a\x1b;[1m~a\x1b;[m~%"]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [sp (make-string (+ nps ns nss) s)] [hh (make-string (1- ns) h)]
         [ps (make-string nps s)] [ss (make-string nss s)]
         [uh (string-append ps (make-string 1 u) hh ss)]
         [dh (string-append ps (make-string 1 d) hh ss)]
         [vs (string-append ps (make-string 1 v) (make-string (1- ns) s) ss)])
    (when (cdr ph)
      (let loop ([st (cdr ph)] [par ps] [pdr ps])
        (printf str par (car st))
        (let count ([st (cdr st)])
          (unless (null? st)
            (let-values ([(ar dr) (if (null? (cdr st))
                                    (values dh sp) (values uh vs))])
              (loop (car st) (string-append pdr ar) (string-append pdr dr)))
            (count (cdr st))))))))
;}}}
;{{{ Empty test
(define (ph-empty? ph)
  (not (cdr ph)))
;}}}
;{{{ Merge heap
(define ($ph-pair! cl lt?)
  (if (null? cl) #f
    (let loop ([cl cl])
      (if (null? (cdr cl)) (car cl)
        (loop
          (let loop ([cl cl] [rl '()])
            (cond [(null? cl) rl]
                  [(null? (cdr cl)) (cons (car cl) rl)]
                  [else
              (let-values ([(a b) (if (lt? (caadr cl) (caar cl))
                  (values (cadr cl) (car cl))
                  (values (car cl) (cadr cl)))])
                (set-cdr! a (cons b (cdr a)))
                (loop (cddr cl) (cons a rl)))])))))))

(define ($ph-merge! ph dt)
  (when dt
    (let ([n1 (cdr ph)] [n2 dt])
      (set-cdr! ph
        (if (not n1) n2
          ($ph-pair! (list n1 n2) (car ph))))))
  ph)

(define (ph-merge! p1 p2)
  (if (not (equal? (car p1) (car p2)))
    (error 'ph-merge! "Incompatible order type"))
  ($ph-merge! p1 (cdr p2)))
;}}}
;{{{ Push to heap
(define (ph-push! ph x)
  ($ph-merge! ph (list x)))
;}}}
;{{{ Pop from heap
(define (ph-pop! ph)
  (if (not (cdr ph))
    (error 'ph-pop! "Empty heap"))
  (let ([m (cadr ph)])
    (set-cdr! ph ($ph-pair! (cddr ph) (car ph)))
    m))
;}}}
;{{{ Search for a node in heap
(define (ph-node ph p?)
  (and (cdr ph)
    (let loop ([n (cdr ph)])
      (if (p? (car n)) n
        (let count ([n (cdr n)])
          (if (null? n) #f
            (or (loop (car n))
                (count (cdr n)))))))))

(define ($ph-trace ph p?)
  (let ([r (and (cdr ph)
      (let loop ([p #f] [b (list #f (cdr ph))] [n (cdr ph)])
        (if (p? (car n)) (cons p b)
          (let count ([l n])
            (if (null? (cdr l)) #f
              (or (loop n l (cadr l))
                  (count (cdr l))))))))])
    (if r (values (car r) (cdr r))
      (values #f #f))))
;}}}
;{{{ Mutate a node in heap
(define ($ph-adjust-increase! ph p b)
  (let* ([n (cadr b)] [v (car n)] [lt? (car ph)])
    (set-cdr! ph ($ph-pair!
        (let loop ([l n] [r (list (cdr ph))])
          (if (null? (cdr l)) r
            (if (lt? (caadr l) v)
              (let ([n (cadr l)])
                (set-cdr! l (cddr l))
                (loop l (cons n r)))
              (loop (cdr l) r))))
        lt?))))

(define ($ph-adjust-decrease! ph p b)
  (let ([n (cadr b)])
    (when (and p ((car ph) (car n) (car p)))
      (set-cdr! b (cddr b))
      ($ph-merge! ph n)
      (void))))

(define (ph-mutate! ph p? mutator)
  (let-values ([(p b) ($ph-trace ph p?)])
    (and b
      (let ([lt? (car ph)] [t0 (cadr b)])
        (cond [(let-values ([(v mutate) (mutator (car t0))])
            (let-syntax ([prog1 (syntax-rules ()
                [(_ v body ...) (let ([v& v]) body ... v&)])])
              (cond
                [(not mutate) (prog1
                 (cond [(lt? (car t0) v) $ph-adjust-increase!]
                       [(lt? v (car t0)) $ph-adjust-decrease!]
                       [else #f])
                 (set-car! t0 v))]
                [(procedure? mutate) (prog1
                 (let ([v0 ((mutate 'accessor) (car t0))]
                       [lt? (mutate 'lt)])
                   (cond [(lt? v0 v) $ph-adjust-increase!]
                         [(lt? v v0) $ph-adjust-decrease!]
                         [else #f]))
                 ((mutate 'mutator) (car t0) v))]
                [(real? mutate)
                 (cond [(positive? mutate) $ph-adjust-increase!]
                       [(negative? mutate) $ph-adjust-decrease!]
                       [else #f])]
                [else $ph-adjust-decrease!])))
          => (lambda (f) (f ph p b))])
        ph))))
;}}}
;{{{ Delete a node in heap
(define (ph-delete! ph p?)
  (let-values ([(p b) ($ph-trace ph p?)])
    (and b
      (begin
        (if (not p) (ph-pop! ph)
          (let ([n (cadr b)])
            (set-cdr! b (cddr b))
            (set-cdr! ph ($ph-pair!
                (cons (cdr ph) (cdr n))
                (car ph)))))
        ph))))
;}}}
;{{{ Make heap from list
(defopt (list->ph l [op #f])
  (fold-left (lambda (x y) (ph-push! x y))
    (if op (make-ph op) (make-ph)) l))
;}}}
)
;}}}
;{{{ Priority-Queue Type
;{{{ Operations Based On Skew Heap
(module $pqueue-sh%
    (pqueue $ds-tag make-pqueue pqueue? $pqueue-length pqueue-op
     pqueue-empty? pqueue-merge! pqueue-push! pqueue-pop!
     pqueue-memp pqueue-mutate! pqueue-delete!)
    (import sh%) (define $ds-tag "sh")
;{{{ Definition
(define-record-type (pqueue $make-pqueue pqueue?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-pqueue
  (case-lambda
    [() ($make-pqueue (make-sh))]
    [(l) ($make-pqueue (list->sh l))]
    [(l op) ($make-pqueue (list->sh l op))]))
;}}}
;{{{ Operations
(define ($pqueue-length q)
  (let loop ([t (cdr (pqueue-data q))])
    (if (null? t) 0
      (+ 1 (loop (cadr t))
           (loop (cddr t))))))

(define (pqueue-op q)
  (car (pqueue-data q)))

(define (pqueue-empty? q)
  (sh-empty? (pqueue-data q)))

(define (pqueue-merge! q1 q2)
  (sh-merge! (pqueue-data q1)
             (pqueue-data q2))
  (set-cdr! (pqueue-data q2) '()))

(define (pqueue-push! q x)
  (sh-push! (pqueue-data q) x)
  (void))

(define (pqueue-pop! q)
  (sh-pop! (pqueue-data q)))

(define (pqueue-memp q p)
  (let ([node (sh-node (pqueue-data q) p)])
    (cond [node => car] [else #f])))

(define (pqueue-mutate! q p m)
  (and (sh-mutate! (pqueue-data q) p m) #t))

(define (pqueue-delete! q p)
  (and (sh-delete! (pqueue-data q) p) #t))
;}}}
)
;}}}
;{{{ Operations Based On Leftist Heap
(module $pqueue-lh%
    (pqueue $ds-tag make-pqueue pqueue? $pqueue-length pqueue-op
     pqueue-empty? pqueue-merge! pqueue-push! pqueue-pop!
     pqueue-memp pqueue-mutate! pqueue-delete!)
    (import lh%) (define $ds-tag "lh")
;{{{ Definition
(define-record-type (pqueue $make-pqueue pqueue?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-pqueue
  (case-lambda
    [() ($make-pqueue (make-lh))]
    [(l) ($make-pqueue (list->lh l))]
    [(l op) ($make-pqueue (list->lh l op))]))
;}}}
;{{{ Operations
(define ($pqueue-length q)
  (let loop ([t (cdr (pqueue-data q))])
    (if (null? t) 0
      (+ 1 (loop (cadr t))
           (loop (cddr t))))))

(define (pqueue-op q)
  (car (pqueue-data q)))

(define (pqueue-empty? q)
  (lh-empty? (pqueue-data q)))

(define (pqueue-merge! q1 q2)
  (lh-merge! (pqueue-data q1)
             (pqueue-data q2))
  (set-cdr! (pqueue-data q2) '()))

(define (pqueue-push! q x)
  (lh-push! (pqueue-data q) x)
  (void))

(define (pqueue-pop! q)
  (lh-pop! (pqueue-data q)))

(define (pqueue-memp q p)
  (let ([node (lh-node (pqueue-data q) p)])
    (cond [node => caar] [else #f])))

(define (pqueue-mutate! q p m)
  (and (lh-mutate! (pqueue-data q) p m) #t))

(define (pqueue-delete! q p)
  (and (lh-delete! (pqueue-data q) p) #t))
;}}}
)
;}}}
;{{{ Operations Based On Binomial Heap
(module $pqueue-bh%
    (pqueue $ds-tag make-pqueue pqueue? $pqueue-length pqueue-op
     pqueue-empty? pqueue-merge! pqueue-push! pqueue-pop!
     pqueue-memp pqueue-mutate! pqueue-delete!)
    (import bh%) (define $ds-tag "bh")
;{{{ Definition
(define-record-type (pqueue $make-pqueue pqueue?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-pqueue
  (case-lambda
    [() ($make-pqueue (make-bh))]
    [(l) ($make-pqueue (list->bh l))]
    [(l op) ($make-pqueue (list->bh l op))]))
;}}}
;{{{ Operations
#;(define ($pqueue-length q)
  (let loop ([t (cdr (pqueue-data q))])
    (let count ([t t])
      (if (null? t) 0
        (+ 1 (loop (cdar t))
           (count (cdr t)))))))
(define ($pqueue-length q)
  (let loop ([t (cdr (pqueue-data q))])
    (if (null? t) 0
      (+ (expt 2 (length (cdar t)))
         (loop (cdr t))))))

(define (pqueue-op q)
  (car (pqueue-data q)))

(define (pqueue-empty? q)
  (bh-empty? (pqueue-data q)))

(define (pqueue-merge! q1 q2)
  (bh-merge! (pqueue-data q1)
             (pqueue-data q2))
  (set-cdr! (pqueue-data q2) '()))

(define (pqueue-push! q x)
  (bh-push! (pqueue-data q) x)
  (void))

(define (pqueue-pop! q)
  (bh-pop! (pqueue-data q)))

(define (pqueue-memp q p)
  (let ([node (bh-node (pqueue-data q) p)])
    (and node (caar node))))

(define (pqueue-mutate! q p m)
  (and (bh-mutate! (pqueue-data q) p m) #t))

(define (pqueue-delete! q p)
  (and (bh-delete! (pqueue-data q) p) #t))
;}}}
)
;}}}
;{{{ Operations Based On Fibonacci Heap
(module $pqueue-fh%
    (pqueue $ds-tag make-pqueue pqueue? $pqueue-length pqueue-op
     pqueue-empty? pqueue-merge! pqueue-push! pqueue-pop!
     pqueue-memp pqueue-mutate! pqueue-delete!)
    (import fh%) (define $ds-tag "fh")
;{{{ Definition
(define-record-type (pqueue $make-pqueue pqueue?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-pqueue
  (case-lambda
    [() ($make-pqueue (make-fh))]
    [(l) ($make-pqueue (list->fh l))]
    [(l op) ($make-pqueue (list->fh l op))]))
;}}}
;{{{ Operations
(define ($pqueue-length q)
  (cdar (pqueue-data q)))

(define (pqueue-op q)
  (caar (pqueue-data q)))

(define (pqueue-empty? q)
  (fh-empty? (pqueue-data q)))

(define (pqueue-merge! q1 q2)
  (fh-merge! (pqueue-data q1)
             (pqueue-data q2))
  (set-cdr! (pqueue-data q2) '())
  (set-cdr! (car (pqueue-data q2)) 0))

(define (pqueue-push! q x)
  (fh-push! (pqueue-data q) x)
  (void))

(define (pqueue-pop! q)
  (fh-pop! (pqueue-data q)))

(define (pqueue-memp q p)
  (let ([node (fh-node (pqueue-data q) p)])
    (and node (caar node))))

(define (pqueue-mutate! q p m)
  (and (fh-mutate! (pqueue-data q) p m) #t))

(define (pqueue-delete! q p)
  (and (fh-delete! (pqueue-data q) p) #t))
;}}}
)
;}}}
;{{{ Operations Based On Pairing Heap
(module $pqueue-ph%
    (pqueue $ds-tag make-pqueue pqueue? $pqueue-length pqueue-op
     pqueue-empty? pqueue-merge! pqueue-push! pqueue-pop!
     pqueue-memp pqueue-mutate! pqueue-delete!)
    (import ph%) (define $ds-tag "ph")
;{{{ Definition
(define-record-type (pqueue $make-pqueue pqueue?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-pqueue
  (case-lambda
    [() ($make-pqueue (make-ph))]
    [(l) ($make-pqueue (list->ph l))]
    [(l op) ($make-pqueue (list->ph l op))]))
;}}}
;{{{ Operations
(define ($pqueue-length q)
  (let loop ([t (cdr (pqueue-data q))])
    (if (not t) 0
      (let count ([t (cdr t)])
        (if (null? t) 1
          (+ (loop (car t))
             (count (cdr t))))))))

(define (pqueue-op q)
  (car (pqueue-data q)))

(define (pqueue-empty? q)
  (ph-empty? (pqueue-data q)))

(define (pqueue-merge! q1 q2)
  (ph-merge! (pqueue-data q1)
             (pqueue-data q2))
  (set-cdr! (pqueue-data q2) #f))

(define (pqueue-push! q x)
  (ph-push! (pqueue-data q) x)
  (void))

(define (pqueue-pop! q)
  (ph-pop! (pqueue-data q)))

(define (pqueue-memp q p)
  (let ([node (ph-node (pqueue-data q) p)])
    (and node (car node))))

(define (pqueue-mutate! q p m)
  (and (ph-mutate! (pqueue-data q) p m) #t))

(define (pqueue-delete! q p)
  (and (ph-delete! (pqueue-data q) p) #t))
;}}}
)
;}}}
;{{{ Data-Structure-Independent Operations
(module pqueue%
    (make-pqueue pqueue? pqueue-op pqueue-empty?
     pqueue-merge! pqueue-push! pqueue-pop!
     pqueue-memp pqueue-mutate! pqueue-delete!)
    (import $pqueue-bh%)
;{{{ Definition
(module ()
  (record-writer (type-descriptor pqueue)
    (lambda (x p wr)
      (format p "#<pqueue #[~a ~d ~a]>"
              $ds-tag
              ($pqueue-length x)
              (pqueue-op x)))))
;}}}
)
;}}}
;}}}
;{{{ Test Utilities
(module (sh-demo lh-demo bh-demo fh-demo ph-demo)
;{{{ Macro
(define-syntax with-demo
  (lambda (x)
    (syntax-case x ()
      [(_ body ...)
       (if (file-exists? "libdemo.so")
         #'(letrec
               ([demo-init (lambda () ((foreign-procedure "demo_init" () void)))]
                [demo-exit (lambda () ((foreign-procedure "demo_exit" () void)))]
                [iclean (lambda () (keyboard-interrupt-handler kbdi))]
                [isetup (lambda () (keyboard-interrupt-handler kbdi@))]
                [kbdi (keyboard-interrupt-handler)]
                [kbdi@ (lambda () (iclean) (kbdi) (demo-init) (isetup))])
             (load-shared-object "./libdemo.so")
             (isetup) (demo-init) body ... (demo-exit) (iclean))
         #'(begin (display "\x1b;[2J") body ...  (void)))])))

(define-syntax make-demo
  (lambda (x)
    (syntax-case x ()
      [(md name)
       (let* ([obj (syntax->datum #'name)]
              [argl (syntax->list (datum->syntax #'md
                      (if (pair? obj) (cdr obj) '())))]
              [prefix (symbol->string
                        (if (pair? obj) (car obj) obj))])
         (with-syntax
             ([% (datum->syntax #'md
                   (string->symbol
                     (string-append prefix "%")))]
              [fun
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-demo")))]
              [show
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-show")))]
              [push!
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-push!")))]
              [pop!
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-pop!")))]
              [delete!
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-delete!")))]
              [node
               (datum->syntax #'md
                 (string->symbol
                   (string-append "make-" prefix)))])
           #`(defopt (fun n [opt '(4 0.3)])
               (import %)
               (with-demo
                 (let* ([m (car opt)] [t (cadr opt)] [z (exact (floor t))]
                        [f (exact (floor (* (- t z) 1e9)))]
                        [pops (lambda (n)
                                (shuffle
                                  (let loop ([n n] [l '()])
                                    (if (positive? n)
                                      (loop (1- n) (cons n l)) l))))]
                        [mops (lambda (n)
                                (let ([l (pops n)])
                                  (let loop ([l l] [r n] [t n])
                                    (unless (zero? r)
                                      (if (positive? (car l))
                                        (let ([ins (list-tail l (random t))])
                                          (set-cdr! ins (cons (- (car l)) (cdr ins)))
                                          (loop (cdr l) (1- r) t))
                                        (loop (cdr l) r (1- t)))))
                                  l))]
                        [pre (lambda (x)
                               (display "\x1b;[1J\x1b;[H") (show x)
                               (sleep (make-time 'time-duration f z)) x)]
                        [gen (lambda (f)
                               (lambda (r l)
                                 (fold-left
                                   (lambda (x y)
                                     (pre (f x y))) r l)))]
                        [pdemo (let ([f #f] [ins (gen push!)] [del
                                   (let ([f #f]
                                         [pop (gen
                                                (lambda (x y) (pop! x) x))]
                                         [rem (gen
                                                (lambda (x y)
                                                  (delete! x (lambda (x) (= x y)))))])
                                      (lambda (x y)
                                        (set! f (not f))
                                        (if f (pop x y) (rem x y))))])
                                 (lambda (x y)
                                   (set! f (not f))
                                   (if f (ins x y) (del x y))))]
                        [mdemo (let* ([f #f] [ins push!] [del #f]
                                      [pop (lambda (x y) (pop! x) x)]
                                      [rem (lambda (x y)
                                             (delete! x (lambda (x) (= x y))))]
                                      [mix (gen
                                             (lambda (x y)
                                               (if (positive? y)
                                                 (ins x y) (del x (- y)))))])
                                 (lambda (x y)
                                   (set! f (not f))
                                   (set! del (if f pop rem))
                                   (mix x y)))])
                   (let-values ([(n demo ops) (if (negative? n)
                       (values (- n) mdemo mops) (values n pdemo pops))])
                     (fold-left demo (node #,@argl)
                                (map ops (make-list m n)))))))))]
      [(md name names ...)
       #'(begin
           (md name)
           (md names ...))])))
;}}}

(define (shuffle l)
  (let* ([n (length l)] [ind (make-vector n)])
    (let loop ([i 0])
      (when (< i n)
        (vector-set! ind i i) (loop (1+ i))))
    (let loop ([i n] [ll '()])
      (if (positive? i)
        (let ([j (random i)])
          (set! i (1- i))
          (unless (= i j)
            (let ([x (vector-ref ind i)] [y (vector-ref ind j)])
              (vector-set! ind i y) (vector-set! ind j x)))
          (loop i (cons (list-ref l (vector-ref ind i)) ll)))
        ll))))

(make-demo sh lh bh fh ph))
;}}}

(random-seed (time-nanosecond (current-time)))
(import pqueue%)
