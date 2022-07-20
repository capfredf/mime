#lang racket/base
(require syntax/parse
         racket/match
         racket/list
         "internal-type-rep.rkt"
         "user-facing-type-rep.rkt"
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
     ;; (eprintf "cs^ ~a ~a ~a ~n" cs^ ty^ (constrain cs^^ ty^ (arrow ty^^ ty)))
     (values (constrain cs^^ ty^ (arrow ty^^ ty)) ty)]
    [(if cond-expr then-expr else-expr)
     (define-values (cs-c ty-c) (recur #'cond-expr))
     (define-values (cs-th ty-th) (recur #'then-expr #:var-ctbl (constrain cs-c ty-c (prim 'bool))))
     (define ty^^ (fresh-var! 'br))
     ;; (eprintf "=============~ncs-c ~a ~n=============== cs-th ~a ~n~n" cs-c cs-th)
     (define-values (cs-el ty-el) (recur #'else-expr #:var-ctbl (constrain cs-th ty-th ty^^)))
     (values (constrain cs-el ty-el ty^^) ty^^)]
    [(let ([x rhs]) body)
     (define-values (cs-rhs ty^) (recur #'rhs env (add1 lvl)))
     (define-values (cs-b ty^^) (recur #'body (extend-env env #'x (poly-type lvl ty^)) #:var-ctbl cs-rhs))
     (values cs-b ty^^)]
    [(sel rcd name)
     (define ty (fresh-var! 'sel))
     (define-values (cs ty^^) (recur #'rcd env #:var-ctbl var-ctbl))
     (values (constrain cs ty^^ (record (list (cons syntax-e #'name) ty))) ty)]))

;; (do-type-infer #'(lambda (x) 10) (new-env))

(define (type-infer term)
  (let-values ([(cs ty) (do-type-infer term (new-env))])
    (let ([uty (coalesce-type cs ty)])
      (uty->sexp uty))))


;; (let-values ([(cs ty) (do-type-infer #'(lambda (p)
;;                                          (if (p 10) #t
;;                                              42))
;;                                      (new-env))])
;;   (for ([(k v) (in-hash cs)])
;;     (printf "~a : ~nconstrain state ~a ~n~n" k
;;             v)))



(module+ test
  (require rackunit)

  (define (alpha-eq? t1 t2)
    (match* (t1 t2)
      [((? var?) (? var?)) #t]
      [((? poly-type?) (? poly-type?))
       (alpha-eq? (poly-type-body t1)
                  (poly-type-body t2))]
      [((? arrow?) (? arrow?))
       (and (alpha-eq? (arrow-arg-type t1)
                       (arrow-arg-type t2))
            (alpha-eq? (arrow-ret-type t1)
                       (arrow-ret-type t2)))]
      [((struct prim [a]) (struct prim [b]))
       (and (equal? a b) a b)]))

  (define-syntax-rule (tc given expected)
    (check-equal? (type-infer given)
                  expected))

  (define-syntax-rule (tc-match given expected)
    (check-match (type-infer given)
                  expected))

  (define-syntax-rule (tc-alpha given expected)
    (check-true (alpha-eq? (type-infer given)
                           expected)))

  (check-equal?
   (type-infer #'(lambda (p)
                   (if (p 10) #t
                       24)))
   '(-> (-> nat bool) (⊔ nat bool)))

  (check-equal?
   (type-infer #'(lambda (x)
                   x))
   '(-> α α))

  (check-equal?
   (type-infer #'(lambda (a)
                   (lambda (b)
                     (if #t a
                         b))))
   '(-> α (-> α α)))



  ;; TODO
  ;; (uty->sexp (coalesce-type (type-infer #'(lambda (f)
  ;;                                        (lambda (x)
  ;;                                          (f (f x))))
  ;;                                       (new-env))))

  ;; (uty->sexp (coalesce-type (type-infer #'(lambda (p)
  ;;                                           (lambda (v)
  ;;                                             (lambda (d)
  ;;                                               (if (p v) v
  ;;                                                   d))))
  ;;                                    (new-env))))
  (tc #'10 'nat)
  (tc #'#t 'bool)
  (tc #'(if #t 42 24) 'nat)
  (tc #'(rcd [a 10]) '{[a : nat]})

  #;
  (tc-match #'(let ([f (lambda (x) x)])
                (f 42))
            (var _ (variable-state _
                                   (list (prim 'nat))
                                   null)))

  #;
  (tc-match #'((lambda (a) a)
               42)
            ;; we know the result type is at least a Nat, i.e, alpha V Nat
            (var _ (variable-state _
                                   (list (prim 'nat))
                                   null))))
