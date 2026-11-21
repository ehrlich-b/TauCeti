/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.RCLike.Lemmas
public import TauCeti.Algebra.Star.Jordan
public import TauCeti.LinearAlgebra.Matrix.Trace.Hermitian

/-!
# The Jordan algebra of Hermitian matrices

Real symmetric and complex Hermitian matrices are formally real Jordan algebras under the
symmetrized product. The trace of a Jordan square is the sum of the squared entry norms.

## Main results

* `Matrix.HermitianJordan` is the carrier for these matrix models.
* Its diagonal entries are real, and it inherits finite dimensionality and formal reality.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Chapter II and Section III.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/HermitianCarrier.lean` and
  `EuclideanJordan/Witness.lean` at a83407e4 (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

noncomputable section

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [RCLike K]

local instance : Invertible (2 : Matrix n n K) :=
  SymAlg.invertibleTwoOfAlgebra (R := ℝ)

/-- The real Jordan algebra of Hermitian matrices over a real or complex field. -/
abbrev HermitianJordan (n K : Type*) [Fintype n] [DecidableEq n] [RCLike K] : Type _ :=
  SymAlg.selfAdjointJordan ℝ (Matrix n n K)

namespace HermitianJordan

/-- The real-linear inclusion into the ambient associative matrix algebra. -/
def toMatrix : HermitianJordan n K →ₗ[ℝ] Matrix n n K where
  toFun x := SymAlg.unsym x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inclusion into matrices is injective. -/
theorem toMatrix_injective :
    Function.Injective (toMatrix : HermitianJordan n K → Matrix n n K) :=
  fun _ _ h => Subtype.ext (SymAlg.unsym_injective h)

/-- The underlying matrix is Hermitian. -/
theorem isHermitian (x : HermitianJordan n K) : (toMatrix x).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.mpr x.property

/-- A diagonal entry has zero imaginary part. -/
theorem im_diag_eq_zero (x : HermitianJordan n K) (i : n) :
    RCLike.im (toMatrix x i i) = 0 :=
  RCLike.im_eq_zero_iff_isSelfAdjoint.mpr (x.isHermitian.apply i i)

/-- The Jordan unit is the identity matrix. -/
@[simp] theorem toMatrix_one : toMatrix (1 : HermitianJordan n K) = 1 := by
  change SymAlg.unsym 1 = 1
  exact SymAlg.unsym_one

/-- The Jordan product is half the sum of the two associative products. -/
theorem toMatrix_mul (x y : HermitianJordan n K) :
    toMatrix (x * y) = (2 : ℝ)⁻¹ • (toMatrix x * toMatrix y + toMatrix y * toMatrix x) := by
  change SymAlg.unsym (x.val * y.val) = _
  rw [SymAlg.unsym_mul_eq_smul (R := ℝ), invOf_eq_inv]
  rfl

/-- The Jordan square equals the associative square. -/
@[simp] theorem toMatrix_mul_self (x : HermitianJordan n K) :
    toMatrix (x * x) = toMatrix x * toMatrix x :=
  SymAlg.unsym_mul_self x.val

/-- Hermitian matrices form a finite-dimensional real vector space. -/
instance : Module.Finite ℝ (HermitianJordan n K) :=
  Module.Finite.of_injective toMatrix toMatrix_injective

/-- The real part of the matrix trace is strictly positive on nonzero Jordan squares. -/
theorem re_trace_toMatrix_mul_self_pos {x : HermitianJordan n K} (hx : x ≠ 0) :
    0 < RCLike.re (toMatrix (x * x)).trace := by
  have htrace := (isHermitian x).trace_mul_self_eq_sum_norm_sq
  rw [toMatrix_mul_self, htrace, RCLike.ofReal_re]
  obtain ⟨i, j, hij⟩ : ∃ i j, toMatrix x i j ≠ 0 := by
    by_contra! h
    exact hx (toMatrix_injective (Matrix.ext (by simpa only [map_zero, Matrix.zero_apply] using h)))
  refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
  exact ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨j, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.mpr hij)⟩⟩

/-- The trace functional detects every sum of nonzero Hermitian squares. -/
instance : IsFormallyReal (HermitianJordan n K) where
  not_isSumNonzeroSq_zero h := by
    let tr : Matrix n n K →ₗ[ℝ] K := Matrix.traceLinearMap n ℝ K
    let τ : HermitianJordan n K →ₗ[ℝ] ℝ := RCLike.reLm.comp (tr.comp toMatrix)
    have hτ {x : HermitianJordan n K} (hx : x ≠ 0) : 0 < τ (x * x) :=
      re_trace_toMatrix_mul_self_pos hx
    suffices ∀ x : HermitianJordan n K, IsSumNonzeroSq x → 0 < τ x by simpa using this 0 h
    intro x hs
    induction hs with
    | sq ha => exact hτ ha
    | sq_add ha _ ih =>
      rw [map_add]
      exact add_pos (hτ ha) ih

end HermitianJordan

end Matrix
