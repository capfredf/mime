#lang typed/racket/base

(require racket/match
         racket/list
         typed/racket/class
         syntax/parse/define
         (for-syntax  racket/syntax racket/base)
         racket/set)
(provide (all-defined-out))

(define-type MonoType (U Var Prim Arrow Record))


(define-type Env% (Class [lookup (-> Identifier Type)]
                         [extend (-> Identifier Type Void)]))
(: env% Env%)
(define env% (class object%
               (init)
               (define eles : (Boxof (Listof (Pairof Identifier Type))) (box (list)))
               (super-new)
               (define/public (lookup id)
                 (cond
                   [(assoc id (unbox eles) free-identifier=?)
                    => cdr]
                   [else (error 'hi "~a is unbound" id)]))

               (define/public (extend id v)
                 (set-box! eles (cons (cons id v)
                                      (unbox eles))))))

(: lookup-env (-> (Instance Env%) Identifier Type))
(define (lookup-env env var)
  (send env lookup var))

(: new-env (-> (Instance Env%)))
(define (new-env)
  (new env%))

(: extend-env (-> (Instance Env%) Identifier Type (Instance Env%)))
(define (extend-env env var ty)
  (send env extend var ty)
  env)

(define (merge-bounds [a : (Listof MonoType)] [b : (Listof MonoType)]) : (Listof MonoType)
  (remove-duplicates (append a b)))

(struct variable-state ([lvl : Natural]
                        [lbs : (Listof MonoType)]
                        [ubs : (Listof MonoType)])
  #:type-name VariableState
  #:transparent
  #:mutable)

(define-syntax-parser define-class-instance-types
  [(_ class-type-name:id cls-type-def)
   #:do [(define ins-type-name (format-id #'class-type-name ""))]
   #'(begin (define-type class-type-name cld-type-def))])

(define-type MonoType% (Class [get-type-level (-> Natural)]
                              [freshen (-> Natural Natural (Instance MonoType%))]))

(define-type Var% (Class (init [uniq-name Symbol]
                               [level Natural]
                               [upperbounds (Listof (Instance MonoType%))]
                               [lowerbounds (Listof (Instance MonoType%))])
                         [add-lower-bounds (-> (Instance MonoType%) Void)]
                         [add-upper-bounds (-> (Instance MonoType%) Void)]
                         #:implements MonoType%))
(define-type Var (Instance Var%))

(: var% Var%)
(define var% (class object%
               (super-new)
               (init uniq-name level upperbounds
                     lowerbounds)

               (define name : Symbol uniq-name)

               (define lvl : Natural level)

               (define ubs : (Boxof (Listof (Instance MonoType%))) (box upperbounds))

               (define lbs : (Boxof (Listof (Instance MonoType%))) (box lowerbounds))


               (define/public (add-lower-bounds delta)
                 (set-box! lbs (cons delta (unbox lbs))))

               (define/public (add-upper-bounds delta)
                 (set-box! ubs (cons delta (unbox ubs))))

               (define/public (get-type-level)
                 lvl)

               ;; (: fmap-bounds (-> MonoType MonoType))
               ;; (define (fmap-bounds op bounds))

               (define/public (freshen poly-lvl current-lvl)
                 (if (< poly-lvl lvl)
                     (new var%
                          [uniq-name name]
                          [level current-lvl]
                          [upperbounds (map (lambda ([a : (Instance MonoType%)])
                                              (send a freshen poly-lvl current-lvl))
                                            (unbox ubs))]
                          [lowerbounds (unbox lbs)])
                     this))))

(struct var ([uniq-name : Symbol] [state : VariableState]) #:type-name Var #:transparent)
(struct arrow ([arg-type : MonoType] [ret-type : MonoType]) #:type-name Arrow #:transparent)
(struct prim ([name : Symbol]) #:type-name Prim #:transparent)
(struct record ([fields : (Listof (Pairof Symbol MonoType))]) #:type-name Record #:transparent)
(define-type Type (U MonoType PolyType))

(struct poly-type ([level : Natural] [body : MonoType]) #:transparent #:type-name PolyType)

(: type-level (-> (U Type Var%) Natural))
(define (type-level type)
  (cond
    [(is-a? type var%) (send type get-type-level)]
    [else
     (match type
       [(var _ (variable-state lvl _ _)) lvl]
       [(arrow arg-type ret-type) (max (type-level arg-type) (type-level ret-type))]
       [(? prim?) 0]
       [(record fs) ((inst argmax Natural)
                     (lambda (x) x)
                     (map (lambda ([x : (Pairof Symbol MonoType)])
                            (type-level (cdr x)))
                          fs))])]))

(define (freshen-above [ty : PolyType] [level : Natural]) : Type
  (match-define (poly-type lvl b) ty)
  (define cache : (HashTable Var Var) (make-hash))
  (let freshen : MonoType ([ty : MonoType b])
    (match ty
      [(? var?)
       #:when (hash-ref cache ty #f)
       (hash-ref cache ty)]
      [(var n (variable-state lvl^ lbs ubs))
       (if (< lvl lvl^)
           (var n (variable-state level (map freshen lbs) (map freshen ubs)))
           ty)]
      [(arrow arg-ty ret-ty)
       (arrow (freshen arg-ty)
              (freshen ret-ty))]
      [(record fs)
       (record (for/list ([i (in-list fs)])
                 (cons (car i) (freshen (cdr i)))))]
      [(? prim?) ty])))

(define (instantiate [ty : Type] [level : Natural]) : Type
  (if (poly-type? ty)
      ;; replace the variables above (type-level ty) with fresh varibles at `level`
      ;; i.e. all the nesting alphas. ∀α₁α₂α₃....
      (freshen-above ty level)
      ty))


(define (fmap-record [ty : Record] [f : (-> MonoType MonoType)])
  (match-define (record fs) ty)
  (record (for/list ([i (in-list fs)])
            (cond (car i) (f (cdr i))))))


(define (fresh-var! [debug-name : Symbol] [lvl : Natural 0]) : Var
  (make-object var% (gensym debug-name) lvl null null))

(define-type Cache (Setof (Pairof MonoType MonoType)))

(: constrain! (->* [MonoType MonoType]
                   [Cache]
                   Void))
(define (constrain! lhs rhs [seen : Cache (set)]) : Void
  (cond
    [(set-member? seen (cons lhs rhs))
     (void)]
    [else
     (define (recur [lhs^ : MonoType] [rhs^ : MonoType]) : Void
       (constrain! lhs^ rhs^ (set-add seen (cons lhs rhs))))
     (match* (lhs rhs)
       [((struct prim [a]) (struct prim [b]))
        #:when (equal? a b)
        (void)]
       [((struct arrow [p1 r1])
         (struct arrow [p2 r2]))
        (recur p2 p1)
        (recur r1 r2)]
       [((struct record [fs1])
         (struct record [fs2]))
        (for ([f1 (in-list fs1)])
          (cond
            [(assoc (car f1) fs2)
             =>
             (lambda (f2)
               (recur (cdr f1) (cdr f2)))]
            [else
             (error 'hi)]))]
       [((struct var [_ vs]) rhs) #:when (<= (variable-state-lvl vs) (type-level lhs))
                                  (set-variable-state-ubs! vs (cons rhs (variable-state-ubs vs)))
                                  (for ([i (in-list (variable-state-lbs vs))])
                                    (recur i rhs))]

       [(lhs (struct var [_ vs])) #:when (<= (type-level lhs) (variable-state-lvl vs))
                                  (set-variable-state-lbs! vs (cons lhs (variable-state-lbs vs)))
                                  (for ([i (in-list (variable-state-ubs vs))])
                                    (recur lhs i))]

       [((? var? lhs) rhs)
        (recur lhs (extrude rhs #f (type-level lhs)))]

       [(lhs (? var? rhs))
        (recur (extrude lhs #t (type-level rhs)) rhs)]
       [(_ _)
        (error 'contrain "unable to constrain ~a <: ~a" lhs rhs)])]))

(define (extrude [ty : MonoType] [polarity : Boolean] [level : Natural]) : MonoType
  ;; todo: handle recurive types
  (let recur : MonoType ([ty : MonoType ty]
                         [polarity : Boolean polarity])
    (cond
      [(< (type-level ty) level)
       ty]
      [else
       (match ty
         [(? prim?) ty]
         [(arrow arg-ty ret-ty)
          (arrow (recur arg-ty (not polarity))
                 (recur ret-ty polarity))]
         [(? record?)
          (fmap-record ty (lambda ([x : MonoType])
                            (recur x polarity)))]
         [(var _ (and (variable-state _ lbs ubs) vs))
          (define nvar (fresh-var! 'nvs level))
          (match-define (var _ nvs) nvar)
          (cond
            [polarity
             (set-variable-state-ubs! vs (cons nvar ubs))
             (set-variable-state-lbs! nvs (for/list ([i (in-list lbs)])
                                            (recur i polarity)))]
            [else
             (set-variable-state-lbs! vs (cons nvar lbs))
             (set-variable-state-ubs! nvs (for/list ([i (in-list ubs)])
                                            (recur i (not polarity))))])
          nvar])])))


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
