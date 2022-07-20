#lang typed/racket/base

(require racket/match
         racket/list
         racket/hash
         racket/set)
(provide (all-defined-out))

(define-type MonoType (U Var Prim Arrow Record))

(define-type Env (Listof (Pairof Identifier Type)))

(: lookup-env (-> Env Identifier Type))
(define (lookup-env env var)
  (cond
    [(assoc var env free-identifier=?)
     =>
     cdr]
    [else (error (format "~a is unbound" var))]))

(: new-env (-> Env))
(define (new-env)
  null)

(: extend-env (-> Env Identifier Type Env))
(define (extend-env env var ty)
  (cons (cons var ty) env))

(define (merge-bounds [a : (Listof MonoType)] [b : (Listof MonoType)]) : (Listof MonoType)
  (remove-duplicates (append a b)))

(define-type Bounds (Listof MonoType))

(struct var ([name : Symbol] [level : Natural]) #:type-name Var #:transparent)
(struct arrow ([arg-type : MonoType] [ret-type : MonoType]) #:type-name Arrow #:transparent)
(struct prim ([name : Symbol]) #:type-name Prim #:transparent)
(struct record ([fields : (Listof (Pairof Symbol MonoType))]) #:type-name Record #:transparent)
(define-type Type (U MonoType PolyType))

(struct poly-type ([level : Natural] [body : MonoType]) #:transparent #:type-name PolyType)

(: type-level (-> Type Natural))
(define (type-level type)
  (match type
    [(var _ lvl) lvl]
    [(arrow arg-type ret-type) (max (type-level arg-type) (type-level ret-type))]
    [(? prim?) 0]
    [(record fs) ((inst argmax Natural)
                  (lambda (x) x)
                  (map (lambda ([x : (Pairof Symbol MonoType)])
                         (type-level (cdr x)))
                       fs))]))

(define-type PolarBounds (Pairof (Listof MonoType)
                                 (Listof MonoType)))

(define (freshen-above [var-cs : VarPolarConstrainInfo] [ty : PolyType] [level : Natural]) : VarPolarConstrainInfo
  (match-define (poly-type lvl b) ty)
  (define cache : (HashTable Var Var) (make-hash))
  (let freshen : VarPolarConstrainInfo ([ty : MonoType b]
                                        [var-cs : VarPolarConstrainInfo var-cs])
    (match ty
      [(? var?)
       #:when (hash-ref cache ty #f)
       var-cs]
      [(var n lvl^)
       (define lvl^ (constrain-state-level (hash-ref var-cs n)))
       (cond
         [(< lvl lvl^)
          (define (update_ [var-cs : VarPolarConstrainInfo] [tys : Bounds]) : VarPolarConstrainInfo
            (for/fold ([acc : VarPolarConstrainInfo var-cs]) ([ty (in-list tys)])
              (freshen ty acc)))

          (let* ([var-cs^ : VarPolarConstrainInfo (update_ var-cs (var-bounds var-cs ty #f))]
                 [var-cs^^ : VarPolarConstrainInfo (update_ var-cs^ (var-bounds var-cs ty #t))])
            (hash-update var-cs^^ n (lambda ([cst : ConstrainState])
                                      (make-constrain-state level
                                                            (constrain-state-lowerbounds cst)
                                                            (constrain-state-upperbounds cst)))))]
         [else var-cs])]
      [(arrow arg-ty ret-ty)
       (freshen ret-ty (freshen arg-ty var-cs))]
      [(record fs)
       (for/fold : VarPolarConstrainInfo
                 ([acc : VarPolarConstrainInfo var-cs])
                 ([i (in-list fs)])
         (freshen (cdr i) acc))]
      [(? prim?) var-cs])))

(define (instantiate [var-cs : VarPolarConstrainInfo] [ty : Type] [level : Natural]) : (Values VarPolarConstrainInfo Type)
  (if (poly-type? ty)
      ;; replace the variables above (type-level ty) with fresh varibles at `level`
      ;; i.e. all the nesting alphas. ∀α₁α₂α₃....
      (values (freshen-above var-cs ty level) (poly-type-body ty))
      (values var-cs ty)))


(define (fmap-record [ty : Record] [f : (-> MonoType MonoType)])
  (match-define (record fs) ty)
  (record (for/list ([i (in-list fs)])
            (cond (car i) (f (cdr i))))))


(define (fresh-var! [debug-name : Symbol] [lvl : Natural 0]) : Var
  (var (gensym debug-name) lvl))

(define-type Cache (Setof (Pairof MonoType MonoType)))

(define-type Constrain (Pairof MonoType MonoType))

(define-type VarSym Symbol)

(struct constrain-state ([level : Natural] [lowerbounds : (Listof MonoType)]
                                           [upperbounds : (Listof MonoType)])
  #:type-name ConstrainState
  #:constructor-name make-constrain-state
  #:transparent)
(define-type VarPolarConstrainInfo (Immutable-HashTable VarSym ConstrainState))
(define-type Mutable-VarPolarConstrainInfo (Mutable-HashTable VarSym ConstrainState))

(define (update-var-constrain [var-ctbl : VarPolarConstrainInfo] [var : Var] [polar : Boolean] [v : MonoType])
        : VarPolarConstrainInfo
  (hash-update var-ctbl (var-name var) (lambda ([a : ConstrainState]) : ConstrainState
                                         (if polar
                                             (make-constrain-state (constrain-state-level a)
                                                                   (cons v (constrain-state-lowerbounds a))
                                                                   (constrain-state-upperbounds a))
                                             (make-constrain-state (constrain-state-level a)
                                                                   (constrain-state-lowerbounds a)
                                                                   (cons v (constrain-state-upperbounds a)))))
               (lambda () : ConstrainState
                 (make-constrain-state (var-level var) null null))))

(define (var-bounds [var-ctbl : VarPolarConstrainInfo] [var : Var] [polar : Boolean]) : Bounds
  (define a (hash-ref var-ctbl (var-name var)))
  (if polar
      (constrain-state-lowerbounds a)
      (constrain-state-upperbounds a)))

(: constrain (->* [VarPolarConstrainInfo MonoType MonoType]
                  [Cache]
                  VarPolarConstrainInfo))
(define (constrain var-ctbl lhs rhs [seen : Cache (set)])
  (define loop constrain)
  (cond
    [(set-member? seen (cons lhs rhs))
     var-ctbl]
    [else
     (define (recur [lhs^ : MonoType] [rhs^ : MonoType]) : VarPolarConstrainInfo
       (loop var-ctbl
             lhs^ rhs^
             (set-add seen (cons lhs rhs))))
     (match* (lhs rhs)
       [((struct prim [a]) (struct prim [b]))
        #:when (equal? a b)
        var-ctbl]
       [((struct arrow [p1 r1])
         (struct arrow [p2 r2]))
        (hash-union (recur p2 p1)
                    (recur r1 r2))]
       [((struct record [fs1])
         (struct record [fs2]))

        (for/fold : VarPolarConstrainInfo
                  ([acc : VarPolarConstrainInfo var-ctbl])
                  ([f1 (in-list fs1)])
          (cond
            [(assoc (car f1) fs2)
             =>
             (lambda (f2)
               (loop var-ctbl (cdr f1) (cdr f2) seen))]
            [else
             (error 'hi)]))]
       [((struct var [_ lvl]) rhs)
        #:when (<= lvl (type-level rhs))
        (define var-ctbl^ : VarPolarConstrainInfo
          (update-var-constrain var-ctbl lhs #f rhs))

        (for/fold : VarPolarConstrainInfo
                  ([acc : VarPolarConstrainInfo var-ctbl^])
                  ([i : MonoType (in-list (var-bounds var-ctbl^ lhs #t))])
          (loop acc i rhs seen))]

       [(lhs (struct var [_ lvl]))
        #:when (<= (type-level lhs) lvl)
        (define var-ctbl^ : VarPolarConstrainInfo
          (update-var-constrain var-ctbl rhs #t lhs))

        (for/fold : VarPolarConstrainInfo
                  ([acc : VarPolarConstrainInfo var-ctbl^])
                  ([i : MonoType (in-list (var-bounds var-ctbl^ rhs #f))])
          (loop acc lhs i seen))]

       [((? var? lhs) rhs)
        (define-values (ty var-ctbl^) (extrude var-ctbl rhs #f (type-level lhs)))
        (loop var-ctbl^ lhs ty seen)]

       [(lhs (? var? rhs))
        (define-values (ty var-ctbl^) (extrude var-ctbl lhs #t (type-level rhs)))
        (loop var-ctbl^ ty rhs seen)]
       [(_ _)
        (error 'contrain "unable to constrain ~a <: ~a" lhs rhs)])]))

(define (extrude [var-cs : VarPolarConstrainInfo] [ty : MonoType] [polarity : Boolean] [level : Natural]) : (values MonoType VarPolarConstrainInfo)
  (define var-cs* : Mutable-VarPolarConstrainInfo
    (make-hash (map (inst cons VarSym ConstrainState) (hash-keys var-cs)
                    (hash-values var-cs))))
  (let recur : (Values MonoType VarPolarConstrainInfo)
       ([ty : MonoType ty]
        [polarity : Boolean polarity]
        [var-cs : VarPolarConstrainInfo var-cs])
    (cond
      [(< (type-level ty) level)
       (values ty var-cs)]
      [else
       (match ty
         [(? prim?) (values ty var-cs)]
         [(arrow arg-ty ret-ty)
          (let-values ([(ty var-cs) (recur arg-ty (not polarity) var-cs)])
            (define-values (ty^ var-cs^) (recur ret-ty polarity var-cs))
            (values (arrow ty ty^)
                    var-cs^))]
         [(? record?)
          (values (fmap-record ty (lambda ([x : MonoType])
                                    (recur x polarity)))
                  var-cs)]
         [(? var v)
          (define nvar (fresh-var! 'nvs level))
          (values nvar
                  (cond
                    [polarity
                     (for/fold : VarPolarConstrainInfo
                               ([acc : VarPolarConstrainInfo (update-var-constrain var-cs v #f nvar)])
                               ([i (in-list (var-bounds var-cs v #t))])
                       (define ty^ (recur i polarity acc))
                       (update-var-constrain var-cs nvar #t ty^))]
                    [else
                     (for/fold ([acc : VarPolarConstrainInfo (update-var-constrain var-cs v #t nvar)])
                               ([i (in-list (var-bounds var-cs v #f))])
                       (define ty^ (recur i polarity acc))
                       (update-var-constrain var-cs nvar #f ty^))]))])])))


(module+ test
  (require typed/rackunit)

  #;
  (define-syntax-rule (tc given expected)
    (check-equal? (type-infer given (new-env))
                  expected))

  #;
  (define-syntax-rule (tc-alpha given expected)
    (check-true (alpha-eq? (type-infer given (new-env))
                           expected))))
