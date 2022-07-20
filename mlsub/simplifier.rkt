#lang typed/racket/base

(require racket/match
         racket/set
         racket/list
         "internal-type-rep.rkt")

(provide (all-defined-out))

(define-type PolarityOcurrence (Pairof Boolean
                                       Boolean))

(define-type VarInfo (Immutable-HashTable Var Boolean))


(: co-occur? (-> VarPolarConstrainInfo Var Boolean MonoType Boolean))
(define (co-occur? var-ctbl ty1 polar ty2)
  (match ty2
    [(? var?)
     (define bounds (var-bounds var-ctbl ty2 polar))
     (set-member? bounds ty1)]
    [_ #f]))


(define-type PolarMaybeVars (Pairof (Option Var) (Option Var)))
(define-type VarCoccurence (HashTable Var PolarMaybeVars))
;; given ty and the polarity,
;; returns something;
;;
;; e.g. for (-> a b a|b), the monotype representation should be
;; (-> (var a (list b) null) (var b null null) (var a (list b) null)
(: unify-vars (-> VarPolarConstrainInfo MonoType Boolean VarCoccurence))
(define (unify-vars var-ctbl ty polarity)
  (define unified-var-mapping : (HashTable Var (Pairof (Option Var) (Option Var))) (make-hash))

  (let unify-vars! : Void ([ty : MonoType ty]
                           [polarity : Boolean polarity])
    (match ty
      [(var _ _)
       #:when (not (hash-ref unified-var-mapping ty #f))
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


       (for ([b (in-list (var-bounds var-ctbl ty polarity))])
         (when (and (var? b) (co-occur? var-ctbl ty polarity b))
           (update-mapping! b))
         #;
         (unify-vars! b polarity))

       #;
       (for ([b (in-list ubs)])
         (unify-vars! b polarity))]
      [(arrow arg-ty ret-ty)
       ;; choose arg to unify first
       (unify-vars! arg-ty (not polarity))
       (unify-vars! ret-ty polarity)]
      [(? prim?) (void)]
      [(record fs)
       (for ([f (in-list fs)])
         (unify-vars! (cdr f) polarity))]))
  unified-var-mapping)

(define (co-analyze [var-cstbl : VarPolarConstrainInfo] [ty : MonoType]) : (-> Var Boolean)
  ;; FIXME: var-tbl is a strippe-down legacy of var-cstbl. it should be removed.
  (define var-tbl : (HashTable Var PolarityOcurrence)
    (make-hash))


  (let remove-polar-var : Void ([ty : MonoType ty]
                                [polarity : Boolean #t])
    (match ty
      [(? var? v)
       (for-each (lambda ([a : MonoType])
                   (remove-polar-var a polarity))
                 (var-bounds var-cstbl v #t))

       (for-each (lambda ([a : MonoType])
                   (remove-polar-var a polarity))
                 (var-bounds var-cstbl v #f))
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



  ;; (define unified-var-tbl (unify-vars! ty #t))
  (define var-info-tbl (for*/hash : VarInfo
                                  ([([v : Var] [b : PolarityOcurrence]) (in-hash var-tbl)]
                                   #:when (and (car b) (cdr b)
                                               (let ()
                                                 (match-define (var _ _) v)
                                                 ;; if lbs and ubs are non-empty,
                                                 ;; lbs - ubs is empty, then the variable are complete sandwiched, i.e. t1 <: a <: t2
                                                 (define ubs (var-bounds var-cstbl v #f))
                                                 (define lbs (var-bounds var-cstbl v #t))
                                                 (or (set-empty? ubs)
                                                     (set-empty? lbs)
                                                     (not (set-empty? (set-subtract ubs lbs)))))))
                         (values v #t)))
  (lambda ([v : Var]) : Boolean
    (cond
      [(hash-ref var-info-tbl v #f)
       #t]
      [else #f])))


(module+ test
  (require typed/rackunit)
  (let ([var-a (var 'a 0)]
        [vctbl (new-var-constrain)])
    (define tbl (co-analyze vctbl (arrow var-a (prim 'bool))))
    (check-false (tbl var-a)))

  (let ([var-a (var 'a 0)]
        [vctbl (new-var-constrain)])
    (define tbl (co-analyze vctbl (arrow var-a var-a)))
    (check-true (tbl var-a)))

  (let* ([var-b (var 'b 0)]
         [var-a (var 'a 0)]
         [vctbl (update-var-constrain (new-var-constrain) var-a #t var-b)]
         [vctbl (update-var-constrain vctbl var-b #t var-a)])
    ;; since var-a is cyclic, we use equal? + check-true
    (define mapping (unify-vars vctbl
                                (arrow var-a (arrow var-b var-a))
                                #t))
    (check-true
     (equal?
      (car (hash-ref mapping
                     var-b))
      var-a))
    #;
    (check-equal? ()
                  (u))))
