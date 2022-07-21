#lang typed/racket/base

(require racket/match
         racket/set
         racket/list
         "internal-type-rep.rkt")

(provide (all-defined-out))

(define-type PolarityOcurrence (Pairof Boolean
                                       Boolean))

(define-type VarInfo (Immutable-HashTable Var Boolean))


(struct compact-arrow ([param : CompactType]
                       [ret : CompactType])
  #:type-name CompactArrow
  #:transparent)

(define-type CompactRecord (Pairof Symbol CompactType))

(struct compact-type ([vars : (Setof Var)]
                      [prims : (Setof Prim)]
                      [arrow : (Option CompactArrow)]
                      [record : (Option (Pairof Symbol CompactType))])
  #:transparent
  #:type-name CompactType
  #:constructor-name make-compact-type)

(define (make-ct #:vars [vars : (Setof Var) (set)]
                 #:prims [prims : (Setof Prim) (set)]
                 #:arrow [arr : (Option CompactArrow) #f]
                 #:record [rcd : (Option CompactRecord) #f]) : CompactType
  (make-compact-type vars
                     prims
                     arr
                     rcd))

(define (merge-compact-type [ct1 : CompactType] [ct2 : CompactType]) : CompactType
  (: merge (All (A) (-> (Option A) (Option A) (-> A A A) (Option A))))
  (define (merge ct1 ct2 f)
    (match* (ct1 ct2)
      [(#f #f) #f]
      [(#f a) a]
      [(a #f) a]
      [(a b)
       #:when (and a b) ;; Err, without the expresion, TR can't recognize that a and b are not #f
       (f a b)]))

  (make-compact-type (set-union (compact-type-vars ct1)
                                (compact-type-vars ct2))
                     (set-union (compact-type-prims ct1)
                                (compact-type-prims ct2))
                     (merge (compact-type-arrow ct1)
                            (compact-type-arrow ct2)
                            (lambda ([a : CompactArrow] [b : CompactArrow]) : CompactArrow
                              (match* (a b)
                                [((compact-arrow p1 r1) (compact-arrow p2 r2))
                                 (compact-arrow (merge-compact-type p1 p2)
                                                (merge-compact-type r1 r2))])))
                     (merge (compact-type-record ct1)
                            (compact-type-record ct2)
                            (lambda ([a : CompactRecord] [b : CompactRecord]) : CompactRecord
                              (error 'merge "not implemented for records")))))

(define (mono->compact [vctbl : VarPolarConstrainInfo] [ty : MonoType] ) : CompactType
  (let loop : CompactType ([ty : MonoType ty]
                           [polar : Boolean #t])
    (match ty
      [(? prim?) (make-ct #:prims (set ty))]
      [(? var? v)
       (define lbs (var-bounds vctbl v #t))
       (define ubs (var-bounds vctbl v #f))
       (for/fold ([output : CompactType (make-ct #:vars (set v))])
                 ([i (in-list (if polar lbs ubs))])
         (merge-compact-type (loop i polar) output))]
      [(arrow param-ty ret-ty)
       (make-ct #:arrow (compact-arrow (loop param-ty (not polar))
                                       (loop ret-ty polar)))])))

(: co-occur? (-> VarPolarConstrainInfo Var Boolean MonoType Boolean))
(define (co-occur? var-ctbl ty1 polar ty2)
  (match ty2
    [(? var?)
     (define bounds (var-bounds var-ctbl ty2 polar))
     (set-member? bounds ty1)]
    [_ #f]))


(define-type PolarMaybeVars (Pairof (Option Var) (Option Var)))
(define-type UnifiedVarMapping (HashTable Var PolarMaybeVars))
;; given ty and the polarity,
;; returns something;
;;
;; e.g. for (-> a b a|b), the monotype representation should be
;; (-> (var a (list b) null) (var b null null) (var a (list b) null)
(: unify-vars (-> VarPolarConstrainInfo CompactType UnifiedVarMapping))
(define (unify-vars vctbl cty)
  (define unified-var-mapping : UnifiedVarMapping (make-hash))

  (define (update-mapping! [src : Var] [tgt : Var] [polarity : Boolean]) : Void
    (hash-update! unified-var-mapping
                  src
                  (lambda ([n : PolarMaybeVars]) : PolarMaybeVars
                    (if polarity
                        (cons tgt
                              (cdr n))
                        (cons (car n)
                              tgt)))
                  (lambda () : PolarMaybeVars
                    (cons #f #f))))

  (let unify-vars! : Void ([cty : CompactType cty]
                           [polarity : Boolean #t])


    (match-define (compact-type vars _ opt-arr opt-rcd) cty)

    (for ([v (in-list (set->list vars))])
      (define lbs (var-bounds vctbl v #t))
      (define ubs (var-bounds vctbl v #f))

      (for ([i (in-list lbs)]
            #:when (var? i))
        (define bounds (var-bounds vctbl i #t))
        (when (member v bounds)
          (update-mapping! i v #t)))

      (for ([i (in-list ubs)]
            #:when (var? i))
        (define bounds (var-bounds vctbl i #f))
        (when (member v bounds)
          (update-mapping! i v #f))))

    (when opt-arr
      (unify-vars! (compact-arrow-param opt-arr) (not polarity))
      (unify-vars! (compact-arrow-ret opt-arr) polarity))

    (when opt-rcd
      (error 'hi)))

  unified-var-mapping)

(define ((co-analyze [vctbl : VarPolarConstrainInfo] [cty : CompactType]) [v : Var] [polar : Boolean]) : (Option Var)
  ;; given this table and a compact type, ty
  ;; can we do a co-analysis?
  ;; for example, for (a -> b)  & ( b -> c ) -> a -> c,
  ;; the compact type is
  ;; ct->((ct(vars(a, b)), ct(vars(b, c))), ct->(ct(vars(a)), ct(vars(c))))
  (define (remove-polar-var! [tbl : UnifiedVarMapping])
    (for ([v (in-list (hash-keys tbl))])
      (define lbs (var-bounds vctbl v #t))
      (define ubs (var-bounds vctbl v #f))
      (when (or (and (empty? lbs) (not (empty? ubs)))
                (and (not (empty? lbs)) (empty? ubs))
                (set-empty? (set-subtract (list->set lbs)
                                          (list->set ubs))))
        (hash-remove! tbl v)))
    ;; if either lbs or ubs is empty, then it is *not* needed
    ;; if
    #;
    (define needed?
      (or
       (and (empty? lbs) (empty? ubs))
       (and (not (set-empty? (set-subtract (list->set lbs)
                                           (list->set ubs))))))))

  (define unified-var-tbl (unify-vars vctbl cty))
  (remove-polar-var! unified-var-tbl)

  (cond
    [(hash-ref unified-var-tbl v #f)
     =>
     (lambda ([a : PolarMaybeVars])
       (cond
         [((if polar car cdr) a)]
         [else v]))]
    [else #f]))

(module+ test
  (require typed/rackunit)

  (let* ([var-a (var 'a 0)]
         [vctbl (update-var-constrain (new-var-constrain) var-a #t (prim 'bool))]
         [lhs (mono->compact vctbl var-a)])
    (check-equal? lhs (make-ct #:vars (set var-a) #:prims (set (prim 'bool))))
    (define lookup (co-analyze vctbl lhs))
    (check-equal? (lookup var-a #t)
                  #f))

  (let* ([var-a (var 'a 0)]
         [vctbl (update-var-constrain (new-var-constrain) var-a #f (prim 'bool))]
         [lhs (mono->compact vctbl (arrow var-a (prim 'bool)))])
    (check-equal? lhs (make-ct #:arrow (compact-arrow (make-ct #:vars (set var-a)
                                                           #:prims (set (prim 'bool)))
                                                      (make-ct #:prims (set (prim 'bool))))))
    (define lookup (co-analyze vctbl lhs))
    (check-equal? (lookup var-a #f)
                  #f))

  ;; r & (a -> b)  & ( b -> c ) -> a -> c
  (let* ([var-r (var 'r 0)]
         [var-a (var 'a 0)]
         [var-b (var 'b 0)]
         [var-c (var 'c 0)]
         [f1 (arrow var-r (arrow var-a var-c))]
         [f2 (arrow var-a var-b)]
         [f3 (arrow var-b var-c)]
         [vctbl (update-var-constrain (new-var-constrain) var-r #f f2)]
         [vctbl (update-var-constrain vctbl var-r #f f3)])
    (check-equal? (mono->compact vctbl f1)
                  (make-ct #:arrow (compact-arrow (make-ct #:vars (set var-r)
                                                           #:arrow (compact-arrow (make-ct #:vars (set var-a var-b))
                                                                                  (make-ct #:vars (set var-b var-c))))
                                                  (make-ct #:arrow (compact-arrow (make-ct #:vars (set var-a))
                                                                                  (make-ct #:vars (set var-c)))))))))
