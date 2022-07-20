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

(define (mono-type->compact-type [vctbl : VarPolarConstrainInfo] [ty : MonoType] [polar : Boolean]) : CompactType
  (let loop : CompactType ([ty : MonoType ty]
                           [output : CompactType (make-ct)])
    (match ty
      [(? prim?) (make-ct #:prims (set ty))]
      [(? var? v)
       (define lbs (var-bounds vctbl v #t))
       (define ubs (var-bounds vctbl v #f))
       ;; if either lbs or ubs is empty, then it is *not* needed
       ;; if
       (define needed?
         (or
           (and (empty? lbs) (empty? ubs))
           (and (not (set-empty? (set-subtract (list->set lbs)
                                               (list->set ubs)))))))
       (cond
         [needed?
          (make-ct #:vars (set v))]
         [else
          (for/fold ([output : CompactType output])
                    ([i (in-list (if polar lbs ubs))])
            (merge-compact-type (loop i (make-ct)) output))])]
      [(arrow param-ty ret-ty)
       (make-ct #:arrow (compact-arrow (loop param-ty (make-ct))
                                       (loop ret-ty (make-ct))))])))

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

  (let* ([var-a (var 'a 0)]
         [vctbl (update-var-constrain (new-var-constrain) var-a #f (prim 'bool))])
    (check-equal? (mono-type->compact-type vctbl var-a #f)
                  (make-ct #:prims (set (prim 'bool)))))

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
    (check-equal? (mono-type->compact-type vctbl f1 #f)
                  (make-ct #:arrow (compact-arrow (make-ct #:arrow (compact-arrow (make-ct #:vars (set var-a var-b))
                                                                                  (make-ct #:vars (set var-b var-c))))
                                                  (make-ct #:arrow (compact-arrow (make-ct #:vars (set var-a))
                                                                                  (make-ct #:vars (set var-c))))))))

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
      var-a)))

  (let ([var-a (var 'a 0)]
        [vctbl (new-var-constrain)])
    (define tbl (co-analyze vctbl (arrow var-a var-a)))
    (check-true (tbl var-a)))

  (let* ([var-a (var 'a 0)]
         [var-b (var 'b 0)]
         [var-r (var 'r 0)]
         [var-d (var 'd 0)])
    (void)))
