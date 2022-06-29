#lang racket/base
(module typed-me typed/racket/base
  (require racket/match)

  (define-type Type (Union PolyType MonoType))
  (define-type Env (Listof (Pairof Identifier Type)))

  (provide (all-defined-out))

  (: lookup-env (-> Env Identifier Type))
  (define (lookup-env env var)
    (cond
      [(assoc var env free-identifier=?)
       =>
       cdr]
      [else (error (format "~a is unbound" var))]))

  (: new-env (-> Env))
  (define (new-env)
    (list (cons #'add1 (make-arrow Int Int))))

  (: extend-env (-> Env Identifier Type Env))
  (define (extend-env env var ty)
    (cons (cons var ty) env))

  (struct mono-type () #:transparent #:type-name MonoType)
  (struct free-var mono-type ([n : Symbol]) #:transparent
    #:property prop:equal+hash
    [list (lambda (me other _)
            (free-var? other))
          (lambda (me f)
            (f (free-var-n me)))
          (lambda (me f)
            (f (free-var-n me)))])
  (struct arrow mono-type ([arg-type : MonoType] [ret-type : MonoType]) #:transparent #:constructor-name make-arrow
    #:type-name Arrow)
  (struct int mono-type () #:transparent #:constructor-name make-int)

  (struct poly-type ([var : Symbol] [body : MonoType]) #:transparent #:type-name PolyType #:constructor-name make-poly)

  (define (fresh-free-var!)
    (free-var (gensym 'var)))

  (define Int (make-int))

  (define (type-eq? ty1 ty2)
    (equal? ty1 ty2))

  (define (forall-I [arr : Arrow])
    (if (free-var? (arrow-arg-type arr))
        (make-poly (free-var-n (arrow-arg-type arr))
                   arr)
        arr))


  (define (forall-E [poly-arr : PolyType] [ty : MonoType]) : Type
    (match-define (struct poly-type [n (? arrow? arr)]) poly-arr)
    (define (subst [input : MonoType] [n : Symbol] [ty : MonoType]) : MonoType
      (match input
        [(struct arrow [arg-ty ret-ty])
         (make-arrow (subst arg-ty n ty)
                     (subst ret-ty n ty))]
        [(struct free-var [m])
         #:when (equal? n m)
         ty]
        [o o]))
    (subst arr n ty))

  (: base-type (-> Symbol (Option MonoType)))
  (define (base-type a)
    (match a
      ['Int Int]
      [_ #f])))

(module parser racket/base
  (require (submod ".." typed-me)
           syntax/parse
           racket/match
           racket/format)

  (define (parse-type ty-term)
    ;; (define (bound? v)
    ;;   (and (member v env)))

    (syntax-parse ty-term
      #:datum-literals (-> forall)
      [identifier:id
       #:do [(define rr (base-type (syntax-e #'identifier)))]
       #:when rr
       rr]
      [identifier:id
       ;; #:when (bound? (syntax-e #'identifier))
       (free-var (syntax-e #'identifier))]
      [(forall (var:id) body)
       (make-poly (syntax-e #'var) (parse-type #'body))]
      [(-> arg-type ret-type) (make-arrow (parse-type #'arg-type) (parse-type #'ret-type))]))

  (define (typecheck term env)
    (syntax-parse term
      #:literals (lambda let)
      [var:id
       (lookup-env env #'var)]
      [n:nat
       Int]
      [(lambda (x) body)
       (define ty (fresh-free-var!))
       (make-arrow ty (typecheck #'body (extend-env env #'x ty)))]
      [(rator rand)
       (define given-arg-ty (typecheck #'rand env))
       (match (typecheck #'rator env)
         [(struct arrow [expected-arg-ty ret-ty])
          (if (type-eq? expected-arg-ty ret-ty)
              ret-ty
              (error 'hi (~a "expected: " expected-arg-ty
                             "~n"
                             "given: " given-arg-ty)))]
         [(and (? poly-type? f-ty))
          (arrow-ret-type (forall-E f-ty given-arg-ty))]
         [_ (error 'hi (~a "not a function:" (syntax-e #'rator)))])]
      [(let ([var rhs])
         body)
       (define ty (match (typecheck #'rhs env)
                    [(? arrow? (app forall-I res))
                     res]
                    [t t]))
       (typecheck #'body (extend-env env #'var ty))]))

  (module+ test
    (require rackunit)
    (check-equal? (parse-type #'(-> Int Int)) (make-arrow Int Int))
    (check-equal? (parse-type #'(-> a a)) (make-arrow (free-var 'a) (free-var 'a)))
    (check-equal? (parse-type #'(forall (a) (-> a a)))
                  (make-poly 'a (make-arrow (free-var 'a) (free-var 'a))))
    (check-equal? (typecheck #'(lambda (x) x) (new-env))
                  (make-arrow (free-var 'a)
                              (free-var 'a)))
    (check-equal? (typecheck #'(let ([id (lambda (x) x)])
                                 (id 10))
                             (new-env))
                  Int)
    (check-equal? (typecheck #'(let ([id (lambda (x) x)])
                                 (id (id 10)))
                             (new-env))
                  Int)))
