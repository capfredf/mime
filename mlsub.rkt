#lang racket/base

(module typed-me typed/racket/base
  (require racket/match
           racket/set)
  (provide (all-defined-out))
  (define-type MonoType (U Var Prim Arrow Record))

  (define-type Env (Listof (Pairof Identifier MonoType)))

  (: lookup-env (-> Env Identifier MonoType))
  (define (lookup-env env var)
    (cond
      [(assoc var env free-identifier=?)
       =>
       cdr]
      [else (error (format "~a is unbound" var))]))

  (: new-env (-> Env))
  (define (new-env)
    null)

  (: extend-env (-> Env Identifier MonoType Env))
  (define (extend-env env var ty)
    (cons (cons var ty) env))


  (struct variable-state ([lbs : (Listof MonoType)]
                          [ubs : (Listof MonoType)])
    #:type-name VariableState
    #:transparent
    #:mutable)
  (struct var ([uniq-name : Symbol] [state : VariableState]) #:type-name Var #:transparent)
  (struct arrow ([arg-type : MonoType] [ret-type : MonoType]) #:type-name Arrow #:transparent)
  (struct prim ([name : Symbol]) #:type-name Prim #:transparent)
  (struct record ([fields : (Listof (Pairof Symbol MonoType))]) #:type-name Record #:transparent)

  (define (fresh-var! [debug-name : Symbol]) : Var
    (var (gensym debug-name) (variable-state null null)))

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
         [((struct var [_ vs]) rhs)
          (set-variable-state-ubs! vs (cons rhs (variable-state-ubs vs)))
          (for ([i (in-list (variable-state-lbs vs))])
            (recur i rhs))]

         [(lhs (struct var [_ vs]))
          (set-variable-state-lbs! vs (cons lhs (variable-state-lbs vs)))
          (for ([i (in-list (variable-state-ubs vs))])
            (recur lhs i))]

         [(_ _)
          (error 'contrain "unable to constrain ~a <: ~a" lhs rhs)])]))

  (define-type UserFacingType (U UVar UPrim UArrow URecord UTop UBot UInter UUnion))


  (struct polar-var ([vs : VariableState] [st : Boolean]) #:type-name PolarVariable #:transparent)
  (struct utop () #:type-name UTop #:transparent)
  (struct ubot () #:type-name UBot #:transparent)
  (struct uunion ([lhs : UserFacingType] [rhs : UserFacingType]) #:type-name UUnion #:transparent)
  (struct uinter ([lhs : UserFacingType] [rhs : UserFacingType]) #:type-name UInter #:transparent)
  (struct uarrow ([lhs : UserFacingType] [rhs : UserFacingType]) #:type-name UArrow #:transparent)
  (struct urecord ([fs : (Listof (Pairof Symbol UserFacingType))]) #:type-name URecord #:transparent)
  (struct uprim ([n : Symbol]) #:type-name UPrim #:transparent)
  (struct uvar ([n : Symbol]) #:type-name UVar #:transparent)

  (define (coalesce-type [ty : MonoType]) : UserFacingType
    ;; todo a table to track recurive type vars.
    (: go (-> MonoType Boolean UserFacingType))
    (define (go ty polarity)
      (match ty
        [(struct prim [n])
         (uprim n)]
        [(struct arrow [param-ty ret-ty])
         (uarrow (go param-ty (not polarity))
                 (go ret-ty (not polarity)))]
        [(struct record [fs])
         (urecord (for/list ([i (in-list fs)])
                    (cons (car i) (go (cdr i) polarity))))]
        [(struct var [n vs])
         ;; todo handle recursive variables
         (define-values (bounds merge-op)
           (if polarity (values (variable-state-lbs vs) uunion)
               (values (variable-state-ubs vs) uinter)))
         (define bound-types : (Listof UserFacingType)
           (for/list ([b (in-list bounds)])
             (go b polarity)))
         (define res : UserFacingType
           (for/fold ([acc : UserFacingType (uvar n)])
                     ([bt (in-list bound-types)])
             (merge-op acc bt)))
         ;; todo handle recursive types
         res]))
    (go ty #t)))


(module infer racket/base
  (require syntax/parse
           racket/match
           (for-syntax racket/base)
           (submod ".." typed-me))
  (provide (all-defined-out))
  (define-syntax (rcd stx)
    (error 'hi "don't call me"))

  (define-syntax (sel stx)
    (error 'hi "don't call me"))

  (define (type-infer term env)
    (syntax-parse term
      #:literals (lambda let rcd sel)
      [var:id
       (lookup-env env #'var)]
      [_:nat
       (prim 'nat)]
      [(rcd (f:id e:expr) ...)
       (record (map (lambda (n e)
                      (cons (syntax-e n) (type-infer e env)))
                    (syntax->list #'(f ...))
                    (syntax->list #'(e ...))))]
      [(lambda (x:id) body:expr)
       (define ty^ (fresh-var! 'abs))
       (arrow ty^ (type-infer #'body
                              (extend-env env #'x ty^)))]
      [(f arg)
       (define ty (fresh-var! 'app))
       (constrain! (type-infer #'f env)
                   (arrow (type-infer #'arg env) ty))
       ty]
      [(sel rcd name)
       (define ty (fresh-var! 'sel))
       (constrain! (type-infer #'rcd env)
                   (record (list (cons (syntax-e #'name) ty))))
       ty])))


(module+ test
  (require rackunit
           racket/match)
  (require (submod ".." infer)
           (submod ".." typed-me))

  (define (alpha-eq? t1 t2)
    (match* (t1 t2)
      [((? var?) (? var?)) #t]
      #;
      [((? poly-type?) (? poly-type?))
       (alpha-eq? (poly-type-body t1)
                  (poly-type-body t2))]
      [((? arrow?) (? arrow?))
       (and (alpha-eq? (arrow-arg-type t1)
                       (arrow-arg-type t2))
            (alpha-eq? (arrow-ret-type t1)
                       (arrow-ret-type t2)))]
      [((struct prim [a]) (struct prim [b]))
       (and (equal? a b) a b)]))

  (define-syntax-rule (tc given expected)
    (check-equal? (type-infer given (new-env))
                  expected))

  (define-syntax-rule (tc-match given expected)
    (check-match (type-infer given (new-env))
                  expected))

  (define-syntax-rule (tc-alpha given expected)
    (check-true (alpha-eq? (type-infer given (new-env))
                           expected)))

  (check-match
   (coalesce-type (var 'hi (variable-state (list (prim 'nat))
                                       null)))
   (struct uunion [(? uvar?)
                   (uprim 'nat)]))

  (check-match
   (coalesce-type (var 'hi (variable-state (list (prim 'nat))
                                       null)))
   (struct uunion [(? uvar?)
                   (uprim 'nat)]))

  (coalesce-type (type-infer #'(lambda (f)
                                 (lambda (x)
                                   (f (f x))))
                             (new-env)))
  (tc #'10 (prim 'nat))
  (tc #'(rcd [a 10]) (record (list [cons 'a (prim 'nat)])))
  (tc-alpha #'(lambda (a) a)
            (let ([v (fresh-var! 'a)])
              (arrow v v)))

  (tc-match #'((lambda (a) a)
               42)
            ;; we know the result type is at least a Nat, i.e, alpha V Nat
            (var _ (variable-state (list (prim 'nat))
                                   null))))
