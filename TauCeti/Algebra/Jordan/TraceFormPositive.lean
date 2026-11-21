/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Algebra.Jordan.Peirce
public import TauCeti.Algebra.Jordan.Spectral
public import TauCeti.Algebra.Jordan.TraceForm

import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# Positive definiteness of the Jordan trace form

The trace of multiplication by an idempotent is the dimension of its Peirce `1`-space plus
half the dimension of its Peirce half-space. In a spectral resolution these traces weight the
squares of the eigenvalues, proving positivity. Conversely, applying an associative positive
form paired with the unit detects every nonzero square.

## Main results

* `one_le_mulTrace_of_isIdempotentElem`: a nonzero idempotent has multiplication trace at least one.
* `traceForm_self_pos`: the multiplication trace form is positive on nonzero elements.
* `formallyReal_iff_exists_associativeForm`: the algebraic and bilinear-form Euclidean conditions
  agree in finite dimension.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Section III.1 and Proposition VIII.4.2.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/TraceForm.lean` at a83407e4
  (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

section PeirceTrace

variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]
  [IsScalarTower ℝ J J] [IsCommJordan J] [Module.Finite ℝ J]

/-- The trace of multiplication by an idempotent is the dimension of its Peirce `1`-space
plus half the dimension of its Peirce half-space. -/
theorem mulTrace_eq_finrank_peirceSpace {c : J} (hc : IsIdempotentElem c) :
    mulTrace ℝ c = Module.finrank ℝ (peirceSpace ℝ c 1) +
      (2 : ℝ)⁻¹ * Module.finrank ℝ (peirceSpace ℝ c (⅟(2 : ℝ))) := by
  have hsplit : LinearMap.mulLeft ℝ c = peirceOne ℝ c + (2 : ℝ)⁻¹ • peirceHalf ℝ c := by
    ext y
    simp only [LinearMap.mulLeft_apply, LinearMap.add_apply, LinearMap.smul_apply,
      peirceOne_apply, peirceHalf_apply]
    module
  have h₁ := (LinearMap.isProj_range_iff_isIdempotentElem (peirceOne ℝ c)).mpr
    (isIdempotentElem_peirceOne hc.eq)
  have h₂ := (LinearMap.isProj_range_iff_isIdempotentElem (peirceHalf ℝ c)).mpr
    (isIdempotentElem_peirceHalf hc.eq)
  rw [mulTrace_apply, hsplit, map_add, map_smul, h₁.trace, h₂.trace,
    range_peirceOne hc, range_peirceHalf hc, smul_eq_mul]

/-- Multiplication by a nonzero idempotent has trace at least one. -/
theorem one_le_mulTrace_of_isIdempotentElem {c : J} (hc : IsIdempotentElem c) (h₀ : c ≠ 0) :
    1 ≤ mulTrace ℝ c := by
  have hmem : c ∈ peirceSpace ℝ c 1 := mem_peirceSpace.mpr (by simpa using hc.eq)
  have hne : peirceSpace ℝ c 1 ≠ ⊥ := fun h => h₀ (by simpa [h] using hmem)
  have hpos : 0 < Module.finrank ℝ (peirceSpace ℝ c 1) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)
  rw [mulTrace_eq_finrank_peirceSpace hc]
  refine le_add_of_le_of_nonneg ?_ (mul_nonneg (by positivity) (Nat.cast_nonneg _))
  exact_mod_cast hpos

end PeirceTrace

section Positive

variable {J : Type*} [NonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]
  [IsScalarTower ℝ J J]

/-- The trace form is positive on every nonzero element of a finite-dimensional formally real
Jordan algebra. -/
theorem traceForm_self_pos [IsCommJordan J] [Module.Finite ℝ J] [IsFormallyReal J] {x : J}
    (hx : x ≠ 0) : 0 < traceForm ℝ x x := by
  classical
  obtain ⟨n, p, c, hp, _, h⟩ := spectralResolution x
  have hdiag (i : Fin n) : p i * (∑ j, c j • p j) = c i • p i := by
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [mul_smul_comm, hp.idempotent i]
    · intro j _ hij
      rw [mul_smul_comm, hp.orthogonal i j hij.symm, smul_zero]
    · simp
  have hs : x * x = ∑ i, (c i * c i) • p i := by
    rw [h, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc, hdiag, smul_smul]
  have hpos (i : Fin n) : 0 < mulTrace ℝ (p i) :=
    zero_lt_one.trans_le (one_le_mulTrace_of_isIdempotentElem (hp.idempotent i) (hp.nonzero i))
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! hn
    exact hx (by simp [h, hn])
  rw [traceForm_apply, hs, map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (mul_self_nonneg _) (hpos j).le)
    ⟨i, Finset.mem_univ _, mul_pos (mul_self_pos.mpr hi) (hpos i)⟩

/-- Formal reality is equivalent to the existence of a symmetric positive definite associative
bilinear form on a finite-dimensional real Jordan algebra. -/
theorem formallyReal_iff_exists_associativeForm [IsCommJordan J] [Module.Finite ℝ J] :
    IsFormallyReal J ↔
      ∃ B : J →ₗ[ℝ] J →ₗ[ℝ] ℝ,
        (∀ x y, B x y = B y x) ∧ (∀ x ≠ 0, 0 < B x x) ∧
          ∀ x y z, B (x * y) z = B y (x * z) := by
  constructor
  · intro h
    exact ⟨traceForm ℝ, traceForm_comm ℝ,
      fun _ hx => traceForm_self_pos hx, traceForm_assoc ℝ⟩
  · rintro ⟨B, hsym, hpos, hassoc⟩
    have hs {x : J} (hx : x ≠ 0) : 0 < B 1 (x * x) := by
      rw [hsym, hassoc, mul_one]
      exact hpos x hx
    refine ⟨fun h => ?_⟩
    suffices ∀ y : J, IsSumNonzeroSq y → 0 < B 1 y by simpa using this 0 h
    intro y hy
    induction hy with
    | sq ha => exact hs ha
    | sq_add ha _ ih =>
      rw [map_add]
      exact add_pos (hs ha) ih

end Positive

end TauCeti.Jordan
