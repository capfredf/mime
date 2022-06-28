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
  (struct free-var mono-type ([n : Symbol]) #:transparent)
  (struct arrow mono-type ([arg-type : MonoType] [ret-type : MonoType]) #:transparent #:constructor-name make-arrow)
  (struct int mono-type () #:transparent #:constructor-name make-int)

  (struct poly-type ([var : Symbol] [body : MonoType]) #:transparent #:type-name PolyType #:constructor-name make-poly)
  (define Int (make-int))

  (define (type-eq? ty1 ty2)
    (equal? ty1 ty2))

  (: base-type (-> Symbol (Option MonoType)))
  (define (base-type a)
    (match a
      ['Int Int]
      [_ #f])))

(module parser racket/base
  (require (submod ".." typed-me)
           syntax/parse)
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

  (module+ test
    (require rackunit)
    (check-equal? (parse-type #'(-> Int Int)) (make-arrow Int Int))
    (check-equal? (parse-type #'(-> a a)) (make-arrow (free-var 'a) (free-var 'a)))
    (check-equal? (parse-type #'(forall (a) (-> a a)))
                  (make-poly 'a (make-arrow (free-var 'a) (free-var 'a))))))
