#lang typed/racket/base
(require "internal-type-rep.rkt"
         "simplifier.rkt"
         racket/match
         racket/list
         racket/set)

(provide (all-defined-out))

(define-type UserFacingType (U UVar UPrim UArrow URecord UTop UBot UInter UUnion))


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
  (require rackunit)
  (require (submod "..")
           "internal-type-rep.rkt")
  (check-match
   (let* ([var1 (var 'hi 0)]
          [cstbl (update-var-constrain (new-var-constrain)
                                       var1
                                       #t
                                       (prim 'nat))])
     (coalesce-type cstbl var1))
   (uprim 'nat))

  (let* ([var1 (var 'hi 0)]
         [cstbl (update-var-constrain (new-var-constrain)
                                      var1
                                      #f
                                      (prim 'nat))])
    (check-equal? (coalesce-type cstbl (arrow var1 (prim 'bool)))
                  (uarrow (uprim 'nat) (uprim 'bool))))

  (let ([v (var 'hi 0)]
        [vctbl (new-var-constrain)])
    (check-match (coalesce-type vctbl
                                (arrow v v))
                 (uarrow (? uvar? a) (? uvar? b))
                 (equal? a b))))
