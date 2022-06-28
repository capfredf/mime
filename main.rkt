#lang racket/base

(require racket/format
         rackunit
         racket/match
         (rename-in syntax/parse
                    [nat sp:nat]))

(module typed-me typed/racket/base
  (require racket/match)

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
    (list (cons #'add1 (make-arrow Nat Nat))))

  (: extend-env (-> Env Identifier Type Env))
  (define (extend-env env var ty)
    (cons (cons var ty) env))

  (struct type () #:transparent #:type-name Type)
  (struct arrow type ([arg-type : Type] [ret-type : Type]) #:transparent #:constructor-name make-arrow)
  (struct nat type () #:transparent #:constructor-name make-nat)
  (define Nat (make-nat))

  (define (type-eq? ty1 ty2)
    (equal? ty1 ty2))

  (: base-type (-> Symbol (Option Type)))
  (define (base-type a)
    (match a
      ['Nat Nat]
      [_ #f])))

(require 'typed-me)

(define (parse-type ty-stx)
  (syntax-parse ty-stx
    #:datum-literals (->)
    [identifier:id
     #:do [(define rr (base-type (syntax-e #'identifier)))]
     #:when rr
     rr]
    [(-> arg-type ret-type)
     (make-arrow (parse-type #'arg-type)
                 (parse-type #'ret-type))]))

(define (type-check e env)
  (syntax-parse e
    #:datum-literals (:)
    [var:id (lookup-env env #'var)]
    [(lambda (x:id : ty:id) body:expr) (make-arrow (parse-type #'ty)
                                                   (type-check #'body (extend-env env #'x (parse-type #'ty))))]
    [(rator rand) (match-define (struct arrow [expected-arg-ty ret-ty]) (type-check #'rator env))
                  (define given-arg-ty (type-check #'rand env))
                  (if (type-eq? expected-arg-ty given-arg-ty)
                      ret-ty
                      (error 'no (~a "expected:" expected-arg-ty
                                     "~n"
                                     "given:" given-arg-ty)))]))

(module+ test
  (check-equal? (parse-type #'Nat) Nat)
  (check-equal? (parse-type #'(-> Nat Nat)) (make-arrow Nat Nat))
  (check-equal? (type-check #'(lambda (x : Nat) x)
                            (new-env))
                (make-arrow Nat Nat))
  (check-equal? (type-check #'(lambda (x : Nat) (add1 x))
                            (new-env))
                (make-arrow Nat Nat)))
