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

  (: co-occur? (-> Var Boolean MonoType Boolean))
  (define (co-occur? ty1 polar ty2)
    (match ty2
      [(var _ (variable-state _ lbs ubs))
       (define bounds (if polar lbs
                          ubs))
       (set-member? bounds ty1)]
      [_ #f]))

  (let remove-polar-var : Void ([ty : MonoType ty]
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
       (remove-polar-var arg-ty (not polarity))
       (remove-polar-var ret-ty polarity)]
      [(record fs)
       (for ([f (in-list fs)])
         (remove-polar-var (cdr f) polarity))]))

  (let unify-vars : Void ([ty : MonoType ty]
                          [polarity : Boolean #t])
    (match ty
      [(var _ (and (variable-state _ lbs ubs) vs))
       (define bounds (if polarity lbs ubs))
       (define new-bounds (for/list : (Listof MonoType)
                                    ([i (in-list bounds)]
                                     #:unless (co-occur? ty polarity i))
                            i))
       (if polarity
           (set-variable-state-lbs! vs new-bounds)
           (set-variable-state-ubs! vs new-bounds))

       (for ([b (in-list lbs)])
         (unify-vars b polarity))

       (for ([b (in-list ubs)])
         (unify-vars b polarity))]
      [(arrow arg-ty ret-ty)
       (unify-vars arg-ty (not polarity))
       (unify-vars ret-ty polarity)]
      [(? prim?) (void)]
      [(record fs)
       (for ([f (in-list fs)])
         (unify-vars (cdr f) polarity))]))

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
