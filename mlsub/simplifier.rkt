#lang typed/racket/base

(require racket/match
         racket/set
         racket/list
         "internal-type-rep.rkt")

(provide (all-defined-out))

(define-type PolarityOcurrence (Pairof Boolean
                                       Boolean))

(define-type VarInfo (Immutable-HashTable Var Boolean))

(define (var-needed? [tbl : VarInfo] [var : Var]) : Boolean
  (hash-ref tbl var #f))


(: co-occur? (-> Var Boolean MonoType Boolean))
(define (co-occur? ty1 polar ty2)
  (match ty2
    [(var _ (variable-state _ lbs ubs))
     (define bounds (if polar lbs
                        ubs))
     (set-member? bounds ty1)]
    [_ #f]))


(define-type PolarMaybeVars (Pairof (Option Var) (Option Var)))
(define-type VarCoccurence (HashTable Var PolarMaybeVars))
;; given ty and the polarity,
;; returns something;
;;
;; e.g. for (-> a b a|b), the monotype representation should be
;; (-> (var a (list b) null) (var b null null) (var a (list b) null)
(: unify-vars (-> MonoType Boolean VarCoccurence))
(define (unify-vars ty polarity)
  (define unified-var-mapping : (HashTable Var (Pairof (Option Var) (Option Var))) (make-hash))

  (let unify-vars! : Void ([ty : MonoType ty]
                           [polarity : Boolean polarity])
    (match ty
      [(var _ (and (variable-state _ lbs ubs) vs)) #:when (not (hash-ref unified-var-mapping ty #f))
       (define bounds (if polarity lbs ubs))


       (define (update-mapping! [i : Var]) : Void
         (hash-update! unified-var-mapping
                       i
                       (lambda ([n : PolarMaybeVars]) : PolarMaybeVars
                         (if polarity
                             (cons ty
                                   (cdr n))
                             (cons (car n)
                                   ty)))
                       (lambda () : PolarMaybeVars
                         (cons #f #f))))


       (for ([b (in-list (if polarity lbs ubs))])
         (when (and (var? b) (co-occur? ty polarity b))
           (update-mapping! b))
         #;
         (unify-vars! b polarity))

       #;
       (for ([b (in-list ubs)])
         (unify-vars! b polarity))]
      [(arrow arg-ty ret-ty)
       (cond
         ;; switch the order based on the polarity.
         ;; This is a makeshift.

         ;; There is something I don't fully understand. Like in the type scheme
         ;; for twice, at some point we get r ^ (a | b -> b & c ) -> a -> c since b
         ;; and c *always* co-occur negatively, and a and b *always* co-occur
         ;; positively.

         ;; my understanding is that we can choose to unify either group. However,
         ;; the resulting type schemes are quite different, i.e. satisfy =∀

         ;; if we do b&c first, we get (a | b -> b) -> a -> b (1). Since now in
         ;; positive positions, we have a | b and b, so we cannot further unify
         ;; them. That is the type scheme given by the paper.

         ;; if do a|b first, we get (a -> a & c ) -> a -> c (2). However, It seems there
         ;; is no instantiation to make (2) <=∀ (1) or (1) <=∀ (2) holds, i.e.
         ;; (2) =∀ (1) does not hold. This indiciates the ordering matters.
         [polarity (unify-vars! arg-ty (not polarity))
                   (unify-vars! ret-ty polarity)]
         [else (unify-vars! ret-ty polarity)
               (unify-vars! arg-ty (not polarity))])]
      [(? prim?) (void)]
      [(record fs)
       (for ([f (in-list fs)])
         (unify-vars! (cdr f) polarity))]))
  unified-var-mapping)

(define (co-analyze [ty : MonoType]) : VarInfo
  (define var-tbl : (HashTable Var PolarityOcurrence)
    (make-hash))


  (let remove-polar-var : Void ([ty : MonoType ty]
                                [polarity : Boolean #t])
    (match ty
      [(var _ (variable-state _ lbs ubs))
       (for-each (lambda ([a : MonoType])
                   (remove-polar-var a polarity))
                 lbs)

       (for-each (lambda ([a : MonoType])
                   (remove-polar-var a polarity))
                 ubs)
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


  #;
  (unify-vars! ty #t)
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
                  (make-immutable-hash (list (cons var-a #t)))))
  (let* ([var-b (var 'b (variable-state 0 null null))]
         [var-a (var 'a (variable-state 0 (list var-b) null))])
    (set-variable-state-lbs! (var-state var-b) (list var-a))
    ;; since var-a is cyclic, we use equal? + check-true
    (check-true
     (equal?
      (car (hash-ref (unify-vars (arrow var-a (arrow var-b var-a))
                                 #t)
                     var-b))
      var-a))
    #;
    (check-equal? ()
                  (u))))
