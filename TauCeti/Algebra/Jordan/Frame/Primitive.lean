/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import TauCeti.Algebra.Jordan.Peirce.Subalgebra
public import TauCeti.Algebra.Jordan.Spectral

/-!
# Primitive idempotents and Jordan frames

A primitive idempotent is a nonzero idempotent with no proper nonzero idempotent in its
Peirce `1`-space. The spectral resolution in this subalgebra characterizes primitivity.

## Main results

* `isPrimitive_iff_peirceSpace_one_eq_span`: a nonzero idempotent is primitive exactly when
  its Peirce `1`-space is the line it spans.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Proposition IV.1.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/Rank.lean` and
  `EuclideanJordan/FramePeirceMul.lean` at a83407e4 (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

section PeirceSpace

variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module ℝ J]
  [SMulCommClass ℝ J J] [IsScalarTower ℝ J J]

/-- If an idempotent has a one-dimensional Peirce `1`-space, it is primitive. -/
theorem IsPrimitive.of_peirceSpace_one_eq_span {c : J} (hc : IsIdempotentElem c) (h₀ : c ≠ 0)
    (h : peirceSpace ℝ c 1 = Submodule.span ℝ {c}) : IsPrimitive c := by
  refine ⟨h₀, hc, fun q hq hfix => ?_⟩
  have hmem : q ∈ peirceSpace ℝ c 1 := mem_peirceSpace.mpr (by simpa using hfix)
  rw [h] at hmem
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  have heq := hq.eq
  rw [smul_mul_assoc, mul_smul_comm, hc.eq, smul_smul] at heq
  have hr : r * r = r := smul_left_injective ℝ h₀ heq
  rcases mul_eq_zero.mp (by rw [mul_sub, mul_one, hr, sub_self] : r * (r - 1) = 0) with h | h
  · exact Or.inl (by rw [h, zero_smul])
  · exact Or.inr (by rw [sub_eq_zero.mp h, one_smul])

variable [IsCommJordan J] [Module.Finite ℝ J] [IsFormallyReal J]

/-- The Peirce `1`-space at a primitive idempotent is the line it spans. -/
theorem IsPrimitive.peirceSpace_one_eq_span {c : J} (hc : IsPrimitive c) :
    peirceSpace ℝ c 1 = Submodule.span ℝ {c} := by
  apply le_antisymm
  · intro x hx
    let S := peirceOneSubalgebra (R := ℝ) hc.idempotent
    let y : S := ⟨x, hx⟩
    obtain ⟨n, q, a, hq, _, hy, _, _⟩ := spectralResolution y
    have hq₁ (i : Fin n) : (q i : J) = c := by
      have hfix : c * (q i : J) = q i := by simpa using mem_peirceSpace.mp (q i).property
      have hid : IsIdempotentElem (q i : J) := congrArg Subtype.val (hq.idempotent i).eq
      exact (hc.eq_zero_or_eq (q i) hid hfix).resolve_left
        (fun h => hq.nonzero i (Subtype.ext h))
    have hsum := congrArg S.toSubmodule.subtype hy
    simp only [map_sum, map_smul] at hsum
    change x = ∑ i, a i • (q i : J) at hsum
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [hq₁ i]
    exact Submodule.mem_span_singleton_self c
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl : x = c)
    exact mem_peirceSpace.mpr (by simpa using hc.idempotent.eq)

/-- A nonzero idempotent is primitive exactly when its Peirce `1`-space is its span. -/
theorem isPrimitive_iff_peirceSpace_one_eq_span {c : J} (hc : IsIdempotentElem c) (h₀ : c ≠ 0) :
    IsPrimitive c ↔ peirceSpace ℝ c 1 = Submodule.span ℝ {c} :=
  ⟨IsPrimitive.peirceSpace_one_eq_span, IsPrimitive.of_peirceSpace_one_eq_span hc h₀⟩

end PeirceSpace

end TauCeti.Jordan
