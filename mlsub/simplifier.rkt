#lang typed/racket/base

(require racket/match
         racket/set
         "internal-type-rep.rkt")

(provide (all-defined-out))

(define-type PolarityOcurrence (Pairof Boolean
                                       Boolean))

(define-type VarInfo (Immutable-HashTable Var Boolean))

(define (var-needed? [tbl : VarInfo] [var : Var]) : Boolean
  (hash-ref tbl var #f))



(define (co-analyze [ty : MonoType]) : VarInfo
  (define var-tbl : (HashTable Var PolarityOcurrence)
    (make-hash))

  (let recur1 : Void ([ty : MonoType ty]
                      [polarity : Boolean #t])
    (match ty
      [(? var?)
       (hash-update! var-tbl ty
                     (lambda ([v : PolarityOcurrence]) : PolarityOcurrence
                       (if polarity
                           (cons #t (cdr v))
                           (cons (car v) #t)))
                     (lambda () : PolarityOcurrence
                       (if polarity
                           (cons #t #f)
                           (cons #f #t))))]
      [(? prim?) (void)]
      [(arrow arg-ty ret-ty)
       (recur1 arg-ty (not polarity))
       (recur1 ret-ty polarity)]
      [(record fs)
       (for ([f (in-list fs)])
         (recur1 (cdr f) polarity))]))

  (for*/hash : VarInfo
             ([([v : Var] [b : PolarityOcurrence]) (in-hash var-tbl)]
              #:when (and (car b) (cdr b)
                          (let ()
                            (match-define (var _ (variable-state _ lbs ubs)) v)
                            ;; if lbs and ubs are non-empty,
                            ;; lbs - ubs is empty, then the variable are complete sandwiched, i.e. t1 <: a <: t2
                            (or (set-empty? ubs)
                                (set-empty? lbs)
                                (not (set-empty? (set-subtract ubs lbs)))))))
    (values v #t)))


(module+ test
  (require typed/rackunit)
  (let ([var-a (var 'a (variable-state 0 null (list (prim 'nat))))])
    (check-equal? (co-analyze (arrow var-a (prim 'bool)))
                  (make-immutable-hash)))
  (let ([var-a (var 'a (variable-state 0 null null))])
    (check-equal? (co-analyze (arrow var-a var-a))
                  (make-immutable-hash (list (cons var-a #t))))))
