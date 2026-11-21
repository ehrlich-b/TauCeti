/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.Jordan.Frame.Peirce
public import TauCeti.Algebra.Jordan.Frame.Primitive

/-!
# Multiplication of Peirce blocks

The single-idempotent Peirce rules determine how blocks of a complete system multiply.
The shared indices of two blocks determine the possible blocks of their product.

## Main results

* Diagonal blocks are subalgebras and preserve incident off-diagonal blocks.
* Two elements of the same off-diagonal block multiply into its two diagonal blocks.
* Two off-diagonal blocks sharing one index multiply into the block of their other indices.
* Blocks with disjoint indices annihilate each other.
* For a Jordan frame, each diagonal block is the line spanned by its primitive idempotent.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Theorem IV.2.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/FramePeirceMul.lean` and
  `EuclideanJordan/Block.lean` at a83407e4 (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

open scoped Sym2

variable {J ι : Type*} [NonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]
  [Fintype ι] {p : ι → J}

namespace IsCompleteSystem

variable [IsCommJordan J]

/-- Each diagonal Peirce block is closed under multiplication. -/
theorem mul_mem_peirceBlock_diag (hp : IsCompleteSystem p) {i : ι} {x y : J}
    (hx : x ∈ peirceBlock p s(i, i)) (hy : y ∈ peirceBlock p s(i, i)) :
    x * y ∈ peirceBlock p s(i, i) := by
  simp only [peirceBlock_diag] at hx hy ⊢
  exact mul_mem_peirceSpace_of_mem_one (hp.idempotent i).eq hx hy

/-- The diagonal block at `i` preserves the block indexed by `i` and `j`. -/
theorem mul_mem_peirceBlock_diag_off (hp : IsCompleteSystem p) {i j : ι} (hij : i ≠ j)
    {x y : J} (hx : x ∈ peirceBlock p s(i, i)) (hy : y ∈ peirceBlock p s(i, j)) :
    x * y ∈ peirceBlock p s(i, j) := by
  have hz : x ∈ peirceSpace ℝ (p j) 0 :=
    mem_peirceSpace.mpr (by simpa using hp.mul_eq_zero_of_mem_peirceBlock hij.symm hij.symm hx)
  rw [peirceBlock_diag] at hx
  rw [peirceBlock_of_ne p hij] at hy ⊢
  exact ⟨mul_mem_peirceSpace_of_mem_one (hp.idempotent i).eq hx hy.1,
    mul_mem_peirceSpace_of_mem_zero (hp.idempotent j).eq hz hy.2⟩

/-- Two elements of the same off-diagonal block multiply into the sum of its diagonal blocks. -/
theorem mul_mem_sup_peirceBlock_diag (hp : IsCompleteSystem p) {i j : ι} (hij : i ≠ j)
    {x y : J} (hx : x ∈ peirceBlock p s(i, j)) (hy : y ∈ peirceBlock p s(i, j)) :
    x * y ∈ peirceBlock p s(i, i) ⊔ peirceBlock p s(j, j) := by
  have hsum := hp.isIdempotentElem_add hij
  have hfix : (p i + p j) * (x * y) = x * y := by
    have h := mul_mem_peirceSpace_of_mem_one hsum.eq
      (peirceBlock_le_peirceSpace_add_one hij hx) (peirceBlock_le_peirceSpace_add_one hij hy)
    simpa using mem_peirceSpace.mp h
  rw [peirceBlock_of_ne p hij] at hx hy
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp
    (mul_mem_peirceSpace_one_sup_zero_of_mem_invOf_two (hp.idempotent i).eq hx.1 hy.1)
  have hu' : u ∈ peirceBlock p s(i, i) := by simpa using hu
  have hvj : p j * v = v := by
    have hui : p i * u = u := by simpa using mem_peirceSpace.mp hu
    have hvi : p i * v = 0 := by simpa using mem_peirceSpace.mp hv
    have huj := hp.mul_eq_zero_of_mem_peirceBlock hij.symm hij.symm hu'
    rw [← huv, add_mul, mul_add, mul_add, hui, hvi, huj, add_zero, zero_add] at hfix
    exact add_left_cancel hfix
  refine Submodule.mem_sup.mpr ⟨u, hu', v, ?_, huv⟩
  rw [peirceBlock_diag, mem_peirceSpace, one_smul]
  exact hvj

/-- Two off-diagonal blocks at consecutive pairs multiply into the block of the outer pair. -/
theorem mul_mem_peirceBlock_middle (hp : IsCompleteSystem p) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {x y : J}
    (hx : x ∈ peirceBlock p s(i, j)) (hy : y ∈ peirceBlock p s(j, k)) :
    x * y ∈ peirceBlock p s(i, k) := by
  have hy₀ : y ∈ peirceSpace ℝ (p i) 0 :=
    mem_peirceSpace.mpr (by simpa using hp.mul_eq_zero_of_mem_peirceBlock hij hik hy)
  have hx₀ : x ∈ peirceSpace ℝ (p k) 0 :=
    mem_peirceSpace.mpr (by simpa using hp.mul_eq_zero_of_mem_peirceBlock hik.symm hjk.symm hx)
  rw [peirceBlock_of_ne p hij] at hx
  rw [peirceBlock_of_ne p hjk] at hy
  rw [peirceBlock_of_ne p hik]
  refine ⟨?_, mul_mem_peirceSpace_of_mem_zero (hp.idempotent k).eq hx₀ hy.2⟩
  rw [mul_comm]
  exact mul_mem_peirceSpace_of_mem_zero (hp.idempotent i).eq hy₀ hx.1

/-- Peirce blocks with disjoint sets of indices annihilate one another. -/
theorem mul_eq_zero_of_peirceBlock_disjoint (hp : IsCompleteSystem p) {i j k l : ι}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) {x y : J}
    (hx : x ∈ peirceBlock p s(i, j)) (hy : y ∈ peirceBlock p s(k, l)) : x * y = 0 := by
  classical
  have hi := hp.mul_eq_zero_of_mem_peirceBlock hik hil hy
  by_cases hij : i = j
  · subst j
    rw [peirceBlock_diag] at hx
    exact mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero (hp.idempotent i).eq hx
      (mem_peirceSpace.mpr (by simpa using hi))
  · have hj := hp.mul_eq_zero_of_mem_peirceBlock hjk hjl hy
    exact mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero
      (hp.isIdempotentElem_add hij).eq (peirceBlock_le_peirceSpace_add_one hij hx)
      (mem_peirceSpace.mpr (by simp [add_mul, hi, hj]))

end IsCompleteSystem

/-- The diagonal block of a Jordan frame is spanned by its primitive idempotent. -/
theorem IsJordanFrame.peirceBlock_diag_eq_span [IsScalarTower ℝ J J] [IsCommJordan J]
    [Module.Finite ℝ J] [IsFormallyReal J] (hp : IsJordanFrame p) (i : ι) :
    peirceBlock p s(i, i) = Submodule.span ℝ {p i} := by
  rw [peirceBlock_diag]
  exact (hp.isPrimitive i).peirceSpace_one_eq_span

end TauCeti.Jordan
