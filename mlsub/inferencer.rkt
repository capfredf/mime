#lang racket/base
(require syntax/parse
         racket/match
         "internal-type-rep.rkt"
         "user-facing-type-rep.rkt"
         (for-syntax racket/base))
(provide (all-defined-out))
(define-syntax (rcd stx)
  (error 'hi "don't call me"))

(define-syntax (sel stx)
  (error 'hi "don't call me"))

(define (do-type-infer term env [lvl 0])
  (define (recur term [env env] [lvl lvl])
    (do-type-infer term env lvl))

  (syntax-parse term
    #:literals (lambda let rcd sel if)
    [var:id
     (instantiate (lookup-env env #'var) lvl)]
    [_:nat
     (prim 'nat)]
    [_:boolean
     (prim 'bool)]
    [(rcd (f:id e:expr) ...)
     (record (map (lambda (n e)
                    (cons (syntax-e n) (recur e)))
                  (syntax->list #'(f ...))
                  (syntax->list #'(e ...))))]
    [(lambda (x:id) body:expr)
     (define ty^ (fresh-var! 'abs))
     (arrow ty^ (recur #'body
                       (extend-env env #'x ty^)))]
    [(f arg)
     (define ty (fresh-var! 'app))
     (constrain! (recur #'f)
                 (arrow (recur #'arg) ty))
     ty]
    [(if cond-expr then-expr else-expr)
     (constrain! (recur #'cond-expr)
                 (prim 'bool))
     (define ty^^ (fresh-var! 'br))
     (constrain! (recur #'then-expr) ty^^)
     (constrain! (recur #'else-expr) ty^^)
     ty^^]
    [(let ([x rhs]) body)
     (define ty^ (recur #'rhs env (add1 lvl)))
     (recur #'body (extend-env env #'x (poly-type lvl ty^)))]
    [(sel rcd name)
     (define ty (fresh-var! 'sel))
     (constrain! (recur #'rcd env)
                 (record (list (cons (syntax-e #'name) ty))))
     ty]))

(define (type-infer term)
  (uty->sexp (coalesce-type (do-type-infer term (new-env)))))


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
