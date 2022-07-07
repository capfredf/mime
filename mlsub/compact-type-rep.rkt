#lang typed/racket/base

(require racket/match
         racket/set
         "internal-type-rep.rkt")

;; a container to represent a union or insection type depending on the polarity
(struct compact-type ([vars : (Setof Var)]
                      [prims : (Setof Prim)]
                      [rcd : (Option (Immutable-HashTable Symbol CompactType))]
                      [fun : (Option (Pairof CompactType CompactType))]) #:transparent
  #:type-name CompactType)

(define empty-ct (compact-type (set) (set) #f #f))

(define (merge-option)
  (void))

(define (merge-ct [polarity : Boolean] [lhs : CompactType] [rhs : CompactType]) : CompactType
  (compact-type (set-union (compact-type-vars lhs)
                           (compact-type-vars rhs))
                (set-union (compact-type-prims lhs)
                           (compact-type-prims rhs))
                (merge )))
