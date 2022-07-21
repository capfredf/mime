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

  (define lookup (co-analyze var-ctbl cty))

  (: go (-> CompactType Boolean UserFacingType))
  (define (go cty polarity)
    (match-define (compact-type vars prims opt-arr opt-rcd) cty)

    (define merge-op (if polarity union-op inter-op))
    (define base (if polarity (ubot) (utop)))
    (define combined-var (for/fold : UserFacingType
                                   ([acc : UserFacingType base])
                                   ([v (in-list (set->list vars))])
                           (if (lookup v polarity)
                               (merge-op (uvar (var-name v)) acc)
                               acc)))

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

    (foldl merge-op combined-var (list combined-prim combined-arr combined-rcd))
    #;
    (match cty
      [(struct prim [n])
       (uprim n)]
      [(struct arrow [param-ty ret-ty])
       (uarrow (go param-ty (not polarity))
               (go ret-ty polarity))]
      [(struct record [fs])
       (urecord (for/list ([i (in-list fs)])
                  (cons (car i) (go (cdr i) polarity))))]
      [(and (var n _) v)
       ;; todo handle recursive variables
       (define-values (bounds merge-op)
         (if polarity (values (var-bounds var-ctbl v #t) union-op)
             (values (var-bounds var-ctbl v #f) inter-op)))
       (define bound-types : (Listof UserFacingType)
         (for/list ([b (in-list bounds)])
           (go b polarity)))


       (define res : UserFacingType
         (for/fold ([acc : UserFacingType base])
                   ([bt (in-list bound-types)])
           (merge-op acc bt)))
       ;; todo handle recursive types
       res]))
  (go cty #t))


(module* test racket/base
  (require rackunit
           racket/set)
  (require (submod "..")
           "internal-type-rep.rkt")

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
                                                                                  (make-ct #:vars (set var-c))))))))
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
