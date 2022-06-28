#lang racket/base

(require racket/match
         racket/format
         rackunit
         syntax/parse)

(define (lookup-env env var)
  (cdr (assoc var env free-identifier=?)))

(define (new-env)
  (list (cons #'add1 (make-arrow Nat Nat))))

(define (extend-env env var ty)
  (cons (cons var ty) env))

(struct type () #:transparent)
(struct arrow type (arg-type ret-type) #:transparent #:constructor-name make-arrow)
(struct nat type () #:transparent #:constructor-name make-nat)
(define Nat (make-nat))

(define (type-eq? ty1 ty2)
  (equal? ty1 ty2))

(define (base-type a)
  (match (syntax-e a)
    ['Nat Nat]
    [_ #f]))

(define (parse-type ty-stx)
  (syntax-parse ty-stx
    #:datum-literals (->)
    [identifier:id
     #:when (base-type #'identifier)
     (base-type #'identifier)]
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
