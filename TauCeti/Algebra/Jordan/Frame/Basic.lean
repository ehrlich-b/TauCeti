/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Ring.Defs

/-!
# Complete systems and Jordan frames

A complete system is a finite family of nonzero pairwise orthogonal idempotents summing to the
unit. A Jordan frame is a complete system consisting of primitive idempotents.

## Main results

* `IsCompleteSystem`: complete systems of nonzero orthogonal idempotents.
* `IsPrimitive`: nonzero idempotents admitting no proper nonzero idempotent beneath them.
* `IsJordanFrame`: complete systems of primitive idempotents.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Theorems III.1.1 and III.1.2 and
  Proposition IV.1.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/Frame.lean` and
  `EuclideanJordan/Rank.lean` at a83407e4 (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

/-- A finite complete system consists of nonzero orthogonal idempotents that sum to the unit. -/
structure IsCompleteSystem {J ι : Type*} [NonAssocSemiring J] [Fintype ι]
    (p : ι → J) : Prop where
  /-- Every member is nonzero. -/
  nonzero : ∀ i, p i ≠ 0
  /-- Every member is an idempotent. -/
  idempotent : ∀ i, IsIdempotentElem (p i)
  /-- Distinct members are orthogonal. -/
  orthogonal : ∀ i j, i ≠ j → p i * p j = 0
  /-- The members sum to the unit. -/
  sum_eq_one : ∑ i, p i = 1

/-- An idempotent is primitive when it is nonzero and has no proper nonzero idempotent below it. -/
structure IsPrimitive {J : Type*} [Mul J] [Zero J] (p : J) : Prop where
  /-- A primitive idempotent is nonzero. -/
  nonzero : p ≠ 0
  /-- A primitive element is idempotent. -/
  idempotent : IsIdempotentElem p
  /-- Every idempotent fixed by left multiplication by `p` is zero or `p`. -/
  eq_zero_or_eq : ∀ q : J, IsIdempotentElem q → p * q = q → q = 0 ∨ q = p

/-- A Jordan frame is a complete system of primitive idempotents. -/
structure IsJordanFrame {J ι : Type*} [NonAssocSemiring J] [Fintype ι] (p : ι → J) : Prop where
  /-- The frame is a complete system of orthogonal idempotents. -/
  toIsCompleteSystem : IsCompleteSystem p
  /-- Each member of the frame is primitive. -/
  isPrimitive : ∀ i, IsPrimitive (p i)

variable {J ι κ : Type*} [NonAssocSemiring J] [Fintype ι] [Fintype κ] {p : ι → J}

/-- Reindexing a complete system by an equivalence preserves completeness. -/
theorem IsCompleteSystem.reindex (hp : IsCompleteSystem p) (e : κ ≃ ι) :
    IsCompleteSystem (p ∘ e) where
  nonzero i := hp.nonzero (e i)
  idempotent i := hp.idempotent (e i)
  orthogonal i j hij := hp.orthogonal (e i) (e j) (e.injective.ne hij)
  sum_eq_one := (e.sum_comp p).trans hp.sum_eq_one

/-- Reindexing a Jordan frame by an equivalence gives a Jordan frame. -/
theorem IsJordanFrame.reindex (hp : IsJordanFrame p) (e : κ ≃ ι) :
    IsJordanFrame (p ∘ e) :=
  ⟨hp.toIsCompleteSystem.reindex e, fun i => hp.isPrimitive (e i)⟩

end TauCeti.Jordan
