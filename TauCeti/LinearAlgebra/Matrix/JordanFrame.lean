/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Data.Matrix.Basis
public import TauCeti.Algebra.Jordan.Frame.Primitive
public import TauCeti.LinearAlgebra.Matrix.Jordan

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Diagonal frames and a Peirce half-space in Hermitian matrix algebras

The diagonal matrix units form a Jordan frame. In size two the matrix exchanging the two
coordinates lies in a Peirce half-space and its square is the identity.

## Main results

* `Matrix.HermitianJordan.isJordanFrame_diagonalUnit`: the standard diagonal frame.
* `Matrix.HermitianJordan.diagonalUnit_zero_mul_coordinateSwap`: a concrete eigenvector
  of eigenvalue one-half in size two.
* `Matrix.HermitianJordan.coordinateSwap_mul_self`: the swap squares to the Jordan unit.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Proposition IV.1.1 and Theorem IV.2.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/HermitianCarrier.lean` and
  `EuclideanJordan/Witness.lean` at a83407e4 (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

noncomputable section

namespace Matrix.HermitianJordan

open TauCeti.Jordan

variable {n K : Type*} [Fintype n] [DecidableEq n] [RCLike K]

/-- The Hermitian matrix unit with one in diagonal entry `i`. -/
def diagonalUnit (i : n) : HermitianJordan n K :=
  ofMatrix (Matrix.single i i 1) (by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    ext a b
    simp only [Matrix.star_apply, Matrix.single_apply]
    simp [and_comm])

/-- The matrix entries of a diagonal Jordan matrix unit are those of the usual matrix unit. -/
@[simp] theorem toMatrix_diagonalUnit (i : n) :
    toMatrix (diagonalUnit (K := K) i) = Matrix.single i i 1 := by
  simp [diagonalUnit]

private theorem diagonalUnit_ne_zero (i : n) : diagonalUnit (K := K) i ≠ 0 := by
  intro h
  have h' := congrArg (fun x : HermitianJordan n K => toMatrix x i i) h
  simp at h'

private theorem isIdempotentElem_diagonalUnit (i : n) :
    IsIdempotentElem (diagonalUnit (K := K) i) := by
  apply toMatrix_injective
  rw [toMatrix_mul_self, toMatrix_diagonalUnit, Matrix.single_mul_single_same, mul_one]

private theorem eq_smul_diagonalUnit_of_mul_eq_self (i : n) (x : HermitianJordan n K)
    (h : diagonalUnit i * x = x) :
    x = RCLike.re (toMatrix x i i) • diagonalUnit (K := K) i := by
  have hm := congrArg toMatrix h
  rw [toMatrix_mul, toMatrix_diagonalUnit] at hm
  apply toMatrix_injective
  rw [map_smul, toMatrix_diagonalUnit]
  ext a b
  have hentry := congrArg (fun A : Matrix n n K => A a b) hm
  simp only [Matrix.smul_apply, Matrix.add_apply] at hentry
  simp only [Matrix.smul_apply, Matrix.single_apply]
  have half_zero (z : K) (hz : (2 : ℝ)⁻¹ • z = z) : z = 0 := by
    by_contra! hz'
    have hh := smul_left_injective ℝ hz' (hz.trans (one_smul ℝ z).symm)
    norm_num at hh
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · subst b
      simpa [Algebra.smul_def] using ((RCLike.re_eq_ofReal_of_isSelfAdjoint
        (RCLike.im_eq_zero_iff_isSelfAdjoint.mp (im_diag_eq_zero x i))).mp rfl)
    · rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ hb,
        one_mul, add_zero] at hentry
      simp [Ne.symm hb, half_zero _ hentry]
  · by_cases hb : b = i
    · subst b
      rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, Matrix.mul_single_apply_same,
        mul_one, zero_add] at hentry
      simp [Ne.symm ha, half_zero _ hentry]
    · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, Matrix.mul_single_apply_of_ne _ _ _ _ _ hb,
        add_zero, smul_zero] at hentry
      simp [Ne.symm ha, hentry.symm]

/-- A diagonal matrix unit is a primitive Jordan idempotent. -/
theorem isPrimitive_diagonalUnit (i : n) : IsPrimitive (diagonalUnit (K := K) i) := by
  have hid := isIdempotentElem_diagonalUnit (K := K) i
  apply IsPrimitive.of_peirceSpace_one_eq_span hid (diagonalUnit_ne_zero i)
  apply le_antisymm
  · intro x hx
    exact Submodule.mem_span_singleton.mpr ⟨_, (eq_smul_diagonalUnit_of_mul_eq_self i x
      (by simpa using mem_peirceSpace.mp hx)).symm⟩
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl : x = diagonalUnit i)
    exact mem_peirceSpace.mpr (by simpa using hid.eq)

/-- The diagonal matrix units form a Jordan frame. -/
theorem isJordanFrame_diagonalUnit :
    IsJordanFrame (diagonalUnit : n → HermitianJordan n K) := by
  refine ⟨⟨diagonalUnit_ne_zero, isIdempotentElem_diagonalUnit, ?_, ?_⟩,
    isPrimitive_diagonalUnit⟩
  · intro i j hij
    apply toMatrix_injective
    rw [toMatrix_mul, toMatrix_diagonalUnit, toMatrix_diagonalUnit,
      Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
    simp
  · apply toMatrix_injective
    simp only [map_sum, toMatrix_diagonalUnit, toMatrix_one]
    ext i j
    rw [Matrix.sum_apply, Finset.sum_eq_single i]
    · simp [Matrix.single_apply, Matrix.one_apply]
    · intro k _ hk
      simp [hk]
    · simp

variable (K)

/-- The two-by-two Hermitian matrix exchanging the two coordinates. -/
def coordinateSwap : HermitianJordan (Fin 2) K :=
  ofMatrix (Matrix.single 0 1 1 + Matrix.single 1 0 1) (by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply])

/-- The swap lies in the Peirce half-space of the first diagonal matrix unit. -/
theorem diagonalUnit_zero_mul_coordinateSwap :
    diagonalUnit 0 * coordinateSwap K = (2 : ℝ)⁻¹ • coordinateSwap K := by
  apply toMatrix_injective
  simp only [toMatrix_mul, map_smul, toMatrix_diagonalUnit, coordinateSwap, toMatrix_ofMatrix]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single_apply]

/-- The two-by-two coordinate swap squares to the Jordan unit. -/
theorem coordinateSwap_mul_self : coordinateSwap K * coordinateSwap K = 1 := by
  apply toMatrix_injective
  simp only [toMatrix_mul_self, coordinateSwap, toMatrix_ofMatrix, toMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single_apply]

end Matrix.HermitianJordan
