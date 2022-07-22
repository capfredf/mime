#lang racket/base
(require syntax/parse
         racket/dict
         racket/match
         racket/list
         "internal-type-rep.rkt"
         "simplifier.rkt"
         syntax/id-table
         (for-syntax racket/base))
(provide (all-defined-out))
(define-syntax (rcd stx)
  (error 'hi "don't call me"))

(define-syntax (sel stx)
  (error 'hi "don't call me"))

(define (do-type-infer term env [lvl 0]  [var-ctbl (make-immutable-hash)])
  (define (recur term [env env] [lvl lvl] #:var-ctbl [var-ctbl var-ctbl])
    (do-type-infer term env lvl var-ctbl))

  (define-syntax-rule (I expr)
    (values var-ctbl expr))

  (syntax-parse term
    #:literals (lambda let rcd sel if)
    [var:id
     (define-values (cs ty-v) (instantiate var-ctbl (lookup-env env #'var) lvl))
     (values cs ty-v)]
    [_:nat
     (I (prim 'nat))]
    [_:boolean
     (I (prim 'bool))]
    [(rcd (f:id e:expr) ...)
     (for/fold ([var-ctbl var-ctbl]
                [fs '()]
                #:result (values var-ctbl (record fs)))
               ([n (syntax->list #'(f ...))]
                [e (syntax->list #'(e ...))])
       (define-values (cs ty) (recur e #:var-ctbl var-ctbl))
       (values cs (cons (cons (syntax-e n) ty)
                        fs)))]
    [(lambda (x:id) body:expr)
     (define ty^ (fresh-var! 'abs))
     (define-values (cs ty^^)
       (recur #'body
              (extend-env env #'x ty^)))
     (values cs (arrow ty^ ty^^))]
    [(f arg)
     (define ty (fresh-var! 'app))
     (define-values (cs^ ty^) (recur #'f))
     (define-values (cs^^ ty^^) (recur #'arg #:var-ctbl cs^))
     (values (constrain cs^^ ty^ (arrow ty^^ ty)) ty)]
    [(if cond-expr then-expr else-expr)
     (define-values (cs-c ty-c) (recur #'cond-expr))
     (define-values (cs-th ty-th) (recur #'then-expr #:var-ctbl (constrain cs-c ty-c (prim 'bool))))
     (define ty^^ (fresh-var! 'br))
     (define-values (cs-el ty-el) (recur #'else-expr #:var-ctbl (constrain cs-th ty-th ty^^)))
     (values (constrain cs-el ty-el ty^^) ty^^)]
    [(let ([x rhs]) body)
     (define-values (cs-rhs ty^) (recur #'rhs env (add1 lvl)))
     (define-values (cs-b ty^^) (recur #'body (extend-env env #'x (poly-type lvl ty^)) #:var-ctbl cs-rhs))
     (values cs-b ty^^)]
    [(letrec ([x rhs]) body)
     (define rhs-ty (fresh-var! 'letrec))
     (define-values (cs-rhs ty^) (recur #'rhs (extend-env env #'x rhs-ty) (add1 lvl)))
     (define cs-rhs^ (constrain cs-rhs ty^ rhs-ty))
     (define-values (cs-b ty^^) (recur #'body (extend-env env #'x (poly-type lvl rhs-ty)) #:var-ctbl cs-rhs^))
     (values cs-b ty^^)]
    [(sel rcd name)
     (define ty (fresh-var! 'sel))
     (define-values (cs ty^^) (recur #'rcd env #:var-ctbl var-ctbl))
     (values (constrain cs ty^^ (record (list (cons syntax-e #'name) ty))) ty)]))

;; (do-type-infer #'(lambda (x) 10) (new-env))

(define (new-env-with-primitives)
  (define primitives (list
                      (cons #'add1 (arrow (prim 'nat) (prim 'nat)))
                      (cons #'sub1 (arrow i:nat i:nat))
                      (cons #'zero? (arrow i:nat i:bool))))
  (define env (new-env))
  (for/fold ([env env])
            ([(k v) (in-dict primitives)])
    (extend-env env k v)))

(define (type-infer term)
  (let-values ([(cs ty) (do-type-infer term (new-env-with-primitives))])
    (uty->sexp (coalesce-type cs ty))))


;; (let-values ([(cs ty) (do-type-infer #'(lambda (p)
;;                                          (if (p 10) #t
;;                                              42))
;;                                      (new-env))])
;;   (for ([(k v) (in-hash cs)])
;;     (printf "~a : ~nconstrain state ~a ~n~n" k
;;             v)))


(module+ test
  (require rackunit)

  ;; (define (alpha-eq? t1 t2)
  ;;   (match* (t1 t2)
  ;;     [((? var?) (? var?)) #t]
  ;;     [((? poly-type?) (? poly-type?))
  ;;      (alpha-eq? (poly-type-body t1)
  ;;                 (poly-type-body t2))]
  ;;     [((? arrow?) (? arrow?))
  ;;      (and (alpha-eq? (arrow-arg-type t1)
  ;;                      (arrow-arg-type t2))
  ;;           (alpha-eq? (arrow-ret-type t1)
  ;;                      (arrow-ret-type t2)))]
  ;;     [((struct prim [a]) (struct prim [b]))
  ;;      (and (equal? a b) a b)]))

  (define-syntax-rule (tc given expected)
    (check-equal? (type-infer (syntax given))
                  expected))

  ;; (define-syntax-rule (tc-match given expected)
  ;;   (check-match (type-infer given)
  ;;                 expected))

  ;; (define-syntax-rule (tc-alpha given expected)
  ;;   (check-true (alpha-eq? (type-infer given)
  ;;                          expected)))

  (check-true
   (and (member (type-infer #'(lambda (p)
                                (if (p 10) #t
                                    24)))
                (list '(-> (-> nat bool) (⊔ nat bool))
                      '(-> (-> nat bool) (⊔ bool nat))))
        #t))

  (tc (lambda (x) x)
   '(-> α α))

  (tc
   (lambda (a)
     (lambda (b)
       (if #t a
           b)))
   '(-> α (-> α α)))

  (tc (lambda (x) (add1 x))
      '(-> nat nat))
  (tc (lambda (x) (zero? x))
      '(-> nat bool))

  (tc 10 'nat)
  (tc #t 'bool)
  (tc (if #t 42 24) 'nat)

  (tc (letrec ([sum (lambda (x)
                              (if (zero? x)
                                  0
                                  (add1 (sum (sub1 x)))))])
        sum)
      '(-> nat nat))

  ;; (a -> a & b) -> a -> b ∀<=> (a | b -> b) -> a -> b
  (check-true
   (and (member (type-infer #'(lambda (f)
                                (lambda (x)
                                  (f (f x)))))
                (list '(-> (-> α (⊓ α β)) (-> α β))
                      '(-> (-> α (⊓ β α)) (-> α β))))
        #t))

  ;; (a -> bool) -> a -> b -> a | b ∀<=> (a -> bool) -> a ⊓ b -> b -> b
  (check-true
   (and (member (type-infer #'(lambda (p)
                                (lambda (v)
                                  (lambda (d)
                                    (if (p v) v
                                        d)))))
                (list '(-> (-> α bool) (-> (⊓ β α) (-> β β)))
                      '(-> (-> α bool) (-> (⊓ α β) (-> β β)))))
        #t)))
