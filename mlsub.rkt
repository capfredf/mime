#lang racket/base


(module typed-me typed/racket/base
  (require racket/match)
  (provide (all-defined-out))
  (define-type MonoType (U Var Prim Arrow Record))

  (define-type Env (Listof (Pairof Identifier MonoType)))

  (: lookup-env (-> Env Identifier MonoType))
  (define (lookup-env env var)
    (cond
      [(assoc var env free-identifier=?)
       =>
       cdr]
      [else (error (format "~a is unbound" var))]))

  (: new-env (-> Env))
  (define (new-env)
    null)

  (: extend-env (-> Env Identifier MonoType Env))
  (define (extend-env env var ty)
    (cons (cons var ty) env))


  (struct variable-state ([lbs : (Listof MonoType)]
                          [ubs : (Listof MonoType)]) #:type-name VariableState #:transparent)
  (struct var ([state : VariableState]) #:type-name Var #:transparent)
  (struct arrow ([arg-type : MonoType] [ret-type : MonoType]) #:type-name Arrow #:transparent)
  (struct prim ([name : Symbol]) #:type-name Prim #:transparent)
  (struct record ([fields : (Listof (Pairof Symbol MonoType))]) #:type-name Record #:transparent)


  (define (fresh-var! [debug-symbol : Symbol]) : Var
    (var (variable-state null null))))


(module infer racket/base
  (require syntax/parse
           racket/match
           (submod ".." typed-me))
  (provide (all-defined-out))
  (define (type-infer term env)
    (syntax-parse term
      #:literals (lambda let)
      [var:id
       (lookup-env env #'var)]
      [var:nat
       (prim 'nat)])))


(module+ test
  (require rackunit)
  (require (submod ".." infer)
           (submod ".." typed-me))
  (define-syntax-rule (tc given expected)
    (check-equal? (type-infer given (new-env))
                  expected))
  (tc 10 (prim 'nat)))
