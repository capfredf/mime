#lang typed/racket/base
(require "internal-type-rep.rkt"
         racket/match
         racket/list
         racket/set)

(provide (all-defined-out))

(define-type UserFacingType (U UVar UPrim UArrow URecord UTop UBot UInter UUnion))


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
(: unify-var! (-> UnifiedVarMapping Var Boolean Var))
(define (unify-var! mapping v polar)
  (define op (if polar car cdr))
  (define a (hash-ref mapping v))
  (cond
    [(op a)
     =>
     (lambda ([tgt : Var])
       ;; ((a | b -> b & c) -> b -> c)
       ;;   a's polar (b, #f)
       ;;   b's polar (a, c)
       ;;   c's polar (c, c)
       ;; pick b:
       (hash-update! mapping v (lambda ([old : PolarMaybeVars]) : PolarMaybeVars
                                 (match-define (cons pos neg) old)
                                 (cons (if pos tgt
                                           pos)
                                       (if neg tgt
                                           neg))))
       (for ([k (in-list (hash-keys mapping))])
         (hash-update! mapping k (lambda ([old : PolarMaybeVars]) : PolarMaybeVars
                                   (match-define (cons pos neg) old)
                                   (cons (if (equal? v pos) tgt
                                             pos)
                                         (if (equal? v neg) tgt
                                             neg)))))
       tgt)]
    [else v]))

(: create-unified-var-mapping (-> CompactType UnifiedVarMapping))
(define (create-unified-var-mapping cty)
  (: pos-vs (Boxof (Setof (Setof Var))))
  (define pos-vs (box (ann (set) (Setof (Setof Var)))))
  (define neg-vs : (Boxof (Setof (Setof Var))) (box (ann (set) (Setof (Setof Var)))))
  (define unified-var-mapping : UnifiedVarMapping (make-hash))

  (define (update-mapping! [src : Var] [tgt : Var] [polarity : Boolean]) : Void
    (hash-update! unified-var-mapping
                  src
                  (lambda ([n : PolarMaybeVars]) : PolarMaybeVars
                    (match-define (cons pos neg) n)
                    (if polarity
                        (cons tgt
                              neg)
                        (cons pos
                              tgt)))
                  (lambda () : PolarMaybeVars
                    (cons #f #f))))

  (let create! : Void ([cty : CompactType cty]
                       [polarity : Boolean #t])
    (match-define (compact-type vars _ opt-arr opt-rcd) cty)

    (unless (set-empty? vars)
      (define vs (if polarity pos-vs neg-vs))
      (set-box! vs (set-add (unbox vs) vars)))

    (when opt-arr
      (create! (compact-arrow-param opt-arr) (not polarity))
      (create! (compact-arrow-ret opt-arr) polarity))

    (when opt-rcd
      (error 'hi)))

  ;; fixme the ordering issue
  (eprintf "start ~n")
  (for ([vs (in-list (list (unbox pos-vs) (unbox neg-vs)))]
        [polar (in-list (list #t #f))])
    (for* ([lvs (in-value (set->list vs))]
           [a (in-list lvs)])
      (eprintf "a is ~a ~n" a)
      (let loop : Void
           ([acc : (Setof Var) a]
            [ls : (Listof (Setof Var)) lvs])
        (match ls
          [(? null?)
           (for* ([tgt (in-value (set-first acc))]
                  [src (in-list (set->list acc))])

             (update-mapping! src tgt polar))]
          [(cons h t)
           (define r (set-intersect h acc))
           (cond
             [(equal? (set-count r) 1) (update-mapping! (set-first r) (set-first r) polar)]
             [(set-empty? r) (loop acc t)]
             [else (loop r t)])]))))

  unified-var-mapping)

(define-type VarPolarOcurrence (Immutable-HashTable Var PolarityOcurrence))

(define (get-polar-var-mapping [cty : CompactType]) : VarPolarOcurrence
  (let loop : VarPolarOcurrence ([cty : CompactType cty]
                    [polar : Boolean #t]
                    [polar-var-mapping : VarPolarOcurrence (make-immutable-hash)])
      ;; use compact-type to generate a mapping
    (match-define (compact-type (app set->list vars) _ opt-arrow opt-rcd) cty)
      ;; vars (a, b) polar #t
      ;; a -> (#f, #t)
      ;; b -> ([a, ], _)
    (define mapping1
      (for/fold : VarPolarOcurrence
                ([acc : VarPolarOcurrence polar-var-mapping])
                ([v (in-list vars)])
        (hash-update acc v (lambda ([po : PolarityOcurrence]) : PolarityOcurrence
                             (match-define (cons pos neg) po)
                             (if polar
                                 (cons #t neg)
                                 (cons pos #t)))
                     (lambda () : (Pairof Boolean Boolean)
                       (cons #f #f)))))

    (define mapping2
      (match opt-arrow
        [(compact-arrow param-ty ret-ty)
         (loop ret-ty polar (loop param-ty (not polar) mapping1))]
        [_ mapping1]))
    (define mapping3
      (match opt-rcd
        [(? list?) (error 'hi)]
        [_ mapping2]))
    mapping3)
    ;; if either lbs or ubs is empty, then it is *not* needed
    ;; if
    #;
    (define needed?
      (or
       (and (empty? lbs) (empty? ubs))
       (and (not (set-empty? (set-subtract (list->set lbs)
                                           (list->set ubs))))))))

(: not-needed? (-> VarPolarOcurrence Var Boolean))
(define (not-needed? mapping v)
  (match (hash-ref mapping v)
    [(cons pos neg)
     (eq? pos (not neg))]))

(define (co-analyze [cty : CompactType])
        : (Values VarPolarOcurrence UnifiedVarMapping)
  ;; given this table and a compact type, ty
  ;; can we do a co-analysis?
  ;; for example, for (a -> b)  & ( b -> c ) -> a -> c,
  ;; the compact type is
  ;; ct->((ct(vars(a, b)), ct(vars(b, c))), ct->(ct(vars(a)), ct(vars(c))))


  (define polar-var-mapping (get-polar-var-mapping cty))
  (define unified-var-mapping (create-unified-var-mapping cty))

  (values polar-var-mapping unified-var-mapping)
  #;
  (match (hash-ref polar-var-mapping v)
    [(cons a b) #:when (eq? a (not b)) #f]
    [_
     (cond
       [(hash-ref unified-var-mapping v #f)
        =>
        (lambda ([n : PolarMaybeVars])
          ((if polar car cdr) n))]
       [else v])]))




(struct utop () #:type-name UTop #:transparent)
(struct ubot () #:type-name UBot #:transparent)
(struct uunion ([lhs : UserFacingType] [rhs : UserFacingType]) #:type-name UUnion #:transparent)
(struct uinter ([lhs : UserFacingType] [rhs : UserFacingType]) #:type-name UInter #:transparent)
(struct uarrow ([lhs : UserFacingType] [rhs : UserFacingType]) #:type-name UArrow #:transparent)
(struct urecord ([fs : (Listof (Pairof Symbol UserFacingType))]) #:type-name URecord #:transparent)
(struct uprim ([n : Symbol]) #:type-name UPrim #:transparent)
(struct uvar ([n : Symbol]) #:type-name UVar #:transparent)

(define (uty->sexp [uty : UserFacingType]) : Any
  (define pretty-vars (list "α" "β" "γ" "δ" "η"))
  (define seq 0)
  (define idx 0)
  (define var-tbl : (HashTable Symbol Symbol) (make-hash))
  (define (produce-beatiful-var [var : Symbol]) : Symbol
    (define (produce!) : Symbol
      (define var (list-ref pretty-vars idx))
      (define ret (string->symbol
                   (if (< seq 5)
                       var
                       (string-append var (number->string (quotient seq 5))))))
      (set! idx (modulo (add1 idx) (length pretty-vars)))
      (set! seq (add1 seq))
      ret)
    (cond
      [(hash-ref var-tbl var #f)]
      [else (define ret (produce!))
            (hash-set! var-tbl var ret)
            ret]))

  (let recur : Any ([uty : UserFacingType uty])
    (match uty
      [(? utop?) 'Top]
      [(? ubot?) 'Bot]
      [(struct uinter [lhs rhs])
       `(⊓ ,(recur lhs)
           ,(recur rhs))]
      [(struct uunion [lhs rhs])
       `(⊔ ,(recur lhs)
           ,(recur rhs))]
      [(struct uarrow [lhs rhs])
       `(-> ,(recur lhs)
            ,(recur rhs))]
      [(struct urecord [fs])
       (map (lambda ([a : (Pairof Symbol UserFacingType)])
              `(,(car a) : ,(recur (cdr a)))) fs)]
      [(struct uprim [n])
       n]
      [(struct uvar [n])
       (produce-beatiful-var n)])))


(define (coalesce-type [var-ctbl : VarPolarConstrainInfo] [ty : MonoType]) : UserFacingType
  ;; todo a table to track recurive type vars.
  (define ((create-merge-op [op : (-> UserFacingType UserFacingType UserFacingType)]
                            [base-pred : (-> UserFacingType Boolean)])
           [ty1 : UserFacingType] [ty2 : UserFacingType]) : UserFacingType
    (cond
      [(base-pred ty1) ty2]
      [(base-pred ty2) ty1]
      [else (op ty1 ty2)]))


  (define (un-fun [a : UserFacingType] [b : UserFacingType])
    (cond
      ;; use subtype instead
      [(equal? a b) b]
      [else (uunion a b)]))

  (define (inter-fun [a : UserFacingType] [b : UserFacingType])
    ;; use subtype instead
    [cond
      [(equal? a b) a]
      [else (uinter a b)]])

  (define union-op (create-merge-op un-fun ubot?))
  (define inter-op (create-merge-op inter-fun utop?))

  (define cty (mono->compact var-ctbl ty))
  (eprintf "cty ~a ~n" cty)

  (define-values (polar-mapping unified-var-mapping) (co-analyze cty))

  (eprintf "===========~n")
  ;; (eprintf "polar-mapping ~a ~n" polar-mapping)
  (eprintf "unified-var-mapping ~a ~n~n" unified-var-mapping)

  (: go (-> CompactType Boolean UserFacingType))
  (define (go cty polarity)
    (match-define (compact-type vars prims opt-arr opt-rcd) cty)

    (define merge-op (if polarity union-op inter-op))
    (define base (if polarity (ubot) (utop)))
    (define combined-var (for/fold : UserFacingType
                                   ([acc : UserFacingType base])
                                   ([v (in-list (set->list vars))])
                           (eprintf "~n")
                           (eprintf "acc ~a ~n" acc)
                           (eprintf "v ~a ~n" v)
                           (define out  (if (not-needed? polar-mapping v)
                                            acc
                                            (let ([v^ (unify-var! unified-var-mapping v polarity)])
                                              (merge-op (uvar (var-name v^)) acc))))
                           (eprintf "out ~a ~n" out)
                           out))

    (define combined-prim (foldl merge-op base (map (compose uprim prim-name) (set->list prims))))


    (define combined-arr
      (cond
        [opt-arr
         (match-define (compact-arrow param-ty ret-ty) opt-arr)
         (uarrow (go param-ty (not polarity))
                 (go ret-ty polarity))]
        [else base]))

    (define combined-rcd
      (cond
        [opt-rcd
         (error 'hi)]
        [else base]))

    (foldl merge-op combined-var (list combined-prim combined-arr combined-rcd)))
  (go cty #t))


(module* test racket/base
  (require rackunit
           racket/set)
  (require (submod "..")
           "internal-type-rep.rkt")

  #;
  (let* ([var-a (var 'a 0)]
         [vctbl (update-var-constrain (new-var-constrain) var-a #t (prim 'bool))]
         [lhs (mono->compact vctbl var-a)])
    (define-values (polar-mapping unified-var-mapping) (co-analyze lhs))
    (check-equal? lhs (make-ct #:vars (set var-a) #:prims (set (prim 'bool))))
    (check-equal? (not-needed? polar-mapping var-a) #t)
    (check-equal? (coalesce-type vctbl var-a) (uprim 'bool)))

  #;
  (let* ([var-a (var 'a 0)]
         [vctbl (update-var-constrain (new-var-constrain) var-a #f (prim 'bool))]
         [ty (arrow var-a (prim 'bool))]
         [lhs (mono->compact vctbl ty)])
    (check-equal? lhs (make-ct #:arrow (compact-arrow (make-ct #:vars (set var-a)
                                                           #:prims (set (prim 'bool)))
                                                      (make-ct #:prims (set (prim 'bool))))))
    (define-values (polar-mapping unified-var-mapping) (co-analyze lhs))
    (check-equal? (not-needed? polar-mapping var-a) #t)
    (check-equal? (coalesce-type vctbl ty) (uarrow (uprim 'bool) (uprim 'bool))))

  ;; r & (a -> b)  & ( b -> c ) -> a -> c
  ;; => ((a | b) -> b) -> a -> b
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
                                                                                  (make-ct #:vars (set var-c)))))))
    (define-values (polar-mapping unified-var-mapping) (co-analyze (mono->compact vctbl f1)))
    (check-equal? (not-needed? polar-mapping var-r) #t)
    (let ([t1 (unify-var! unified-var-mapping var-a #t)])
      (check-equal? t1 var-a)
      (let ([t2 (unify-var! unified-var-mapping var-b #t)])
        (check-equal? t2 t1)
        (let ([t (unify-var! unified-var-mapping var-c #t)])
          (check-equal? t var-c))))
    (check-equal? (coalesce-type vctbl f1) (uarrow
                                            (uarrow (uvar 'a) (uinter (uvar 'c) (uvar 'a)))
                                            (uarrow (uvar 'a) (uvar 'c)))))
  #;
  (check-match
   (let* ([var1 (var 'hi 0)]
          [cstbl (update-var-constrain (new-var-constrain)
                                       var1
                                       #t
                                       (prim 'nat))])
     (coalesce-type cstbl var1))
   (uprim 'nat))

  #;
  (let* ([var1 (var 'hi 0)]
         [cstbl (update-var-constrain (new-var-constrain)
                                      var1
                                      #f
                                      (prim 'nat))])
    (check-equal? (coalesce-type cstbl (arrow var1 (prim 'bool)))
                  (uarrow (uprim 'nat) (uprim 'bool))))

  #;
  (let ([v (var 'hi 0)]
        [vctbl (new-var-constrain)])
    (check-match (coalesce-type vctbl
                                (arrow v v))
                 (uarrow (? uvar? a) (? uvar? b))
                 (equal? a b))))
