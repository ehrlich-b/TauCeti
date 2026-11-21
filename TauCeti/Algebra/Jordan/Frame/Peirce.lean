/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.Algebra.Jordan.Peirce
public import TauCeti.Algebra.Jordan.Frame.Basic

import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Peirce spaces of a complete system

The Peirce blocks of a complete system are indexed by unordered pairs. The diagonal blocks are
the Peirce `1`-spaces, and the off-diagonal blocks are intersections of two Peirce half-spaces.

## Main results

* The multiplication operators of a complete system commute and add to the identity.
* A diagonal linear combination acts on each block by the average of the two coefficients.
  Every partial sum of the members is an idempotent.
* Products of distinct multiplication operators have range in the corresponding off-diagonal
  block. Scaled by four, they are the off-diagonal projections.
* `IsCompleteSystem.isInternal_peirceBlock`: the Peirce blocks form an internal direct sum.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Theorem IV.2.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/FramePeirce.lean` and
  `EuclideanJordan/Block.lean` at a83407e4 (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

open scoped Sym2

variable {J ι : Type*}

section Blocks

variable [NonUnitalNonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]

/-- The diagonal and off-diagonal Peirce spaces indexed by unordered pairs. -/
noncomputable def peirceBlock (p : ι → J) : Sym2 ι → Submodule ℝ J := by
  classical
  refine Sym2.lift ⟨fun i j => if i = j then peirceSpace ℝ (p i) 1 else
    peirceSpace ℝ (p i) ⅟(2 : ℝ) ⊓ peirceSpace ℝ (p j) ⅟(2 : ℝ), ?_⟩
  intro i j
  by_cases h : i = j
  · subst j
    rfl
  · simp [h, Ne.symm h, inf_comm]

/-- The diagonal Peirce block is the Peirce `1`-space. -/
@[simp] theorem peirceBlock_diag (p : ι → J) (i : ι) :
    peirceBlock p s(i, i) = peirceSpace ℝ (p i) 1 := by
  classical
  simp [peirceBlock]

/-- An off-diagonal Peirce block is the intersection of the two half-spaces. -/
theorem peirceBlock_of_ne (p : ι → J) {i j : ι} (h : i ≠ j) :
    peirceBlock p s(i, j) =
      peirceSpace ℝ (p i) ⅟(2 : ℝ) ⊓ peirceSpace ℝ (p j) ⅟(2 : ℝ) := by
  classical
  simp [peirceBlock, h]

/-- An off-diagonal block lies in the Peirce `1`-space of the sum of its two idempotents. -/
theorem peirceBlock_le_peirceSpace_add_one {p : ι → J} {i j : ι} (h : i ≠ j) :
    peirceBlock p s(i, j) ≤ peirceSpace ℝ (p i + p j) 1 := by
  intro x hx
  rw [peirceBlock_of_ne p h] at hx
  rw [mem_peirceSpace, add_mul, mem_peirceSpace.mp hx.1, mem_peirceSpace.mp hx.2, invOf_eq_inv]
  module

/-- The Peirce projection onto an unordered pair's block, given by `P₁` on the diagonal
and by four times the composition of the two multiplication operators off the diagonal. -/
noncomputable def peirceBlockProj (p : ι → J) (i j : ι) : Module.End ℝ J := by
  classical
  exact if i = j then peirceOne ℝ (p i) else
    (4 : ℝ) • (LinearMap.mulLeft ℝ (p i) * LinearMap.mulLeft ℝ (p j))

/-- On the diagonal, the block projection is the Peirce one projection. -/
@[simp] theorem peirceBlockProj_diag (p : ι → J) (i : ι) :
    peirceBlockProj p i i = peirceOne ℝ (p i) := by
  classical
  simp [peirceBlockProj]

/-- Off the diagonal, the block projection is four times the composed multiplication maps. -/
theorem peirceBlockProj_of_ne (p : ι → J) {i j : ι} (h : i ≠ j) :
    peirceBlockProj p i j =
      (4 : ℝ) • (LinearMap.mulLeft ℝ (p i) * LinearMap.mulLeft ℝ (p j)) := by
  classical
  simp [peirceBlockProj, h]

end Blocks

variable [NonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]

namespace IsCompleteSystem

variable [Fintype ι] {p : ι → J}

/-- The sum of the multiplication operators of a complete system is the identity. -/
theorem sum_mulLeft (hp : IsCompleteSystem p) :
    (∑ i, LinearMap.mulLeft ℝ (p i)) = LinearMap.id := by
  ext x
  simp only [LinearMap.sum_apply, LinearMap.mulLeft_apply, ← Finset.sum_mul, hp.sum_eq_one,
    one_mul, LinearMap.id_apply]

private theorem mem_peirceSpace_zero_of_ne (hp : IsCompleteSystem p) {i j : ι} (h : i ≠ j) :
    p j ∈ peirceSpace ℝ (p i) 0 :=
  mem_peirceSpace.mpr (by simp [hp.orthogonal i j h])

variable [IsCommJordan J]

/-- The multiplication operators of the members of a complete system commute. -/
theorem commute_mulLeft (hp : IsCompleteSystem p) (i j : ι) :
    Commute (LinearMap.mulLeft ℝ (p i)) (LinearMap.mulLeft ℝ (p j)) := by
  classical
  by_cases h : i = j
  · subst j
    exact Commute.refl _
  · apply LinearMap.ext
    intro x
    exact mul_left_comm_of_mem_peirceSpace_one_or_zero (hp.idempotent i).eq
      (Or.inr (hp.mem_peirceSpace_zero_of_ne h)) x

omit [Module ℝ J] [SMulCommClass ℝ J J] [IsCommJordan J] in
/-- The sum of two distinct members of a complete system is an idempotent. -/
theorem isIdempotentElem_add (hp : IsCompleteSystem p) {i j : ι} (h : i ≠ j) :
    IsIdempotentElem (p i + p j) := by
  exact (hp.idempotent i).add (hp.idempotent j)
    (by rw [hp.orthogonal i j h, hp.orthogonal j i h.symm, zero_add])

/-- Every member outside the indexing pair annihilates an element of its Peirce block. -/
theorem mul_eq_zero_of_mem_peirceBlock (hp : IsCompleteSystem p) {i j k : ι}
    (hki : k ≠ i) (hkj : k ≠ j) {x : J} (hx : x ∈ peirceBlock p s(i, j)) : p k * x = 0 := by
  classical
  by_cases h : i = j
  · subst j
    rw [peirceBlock_diag] at hx
    rw [mul_comm]
    exact mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero (hp.idempotent i).eq hx
      (hp.mem_peirceSpace_zero_of_ne hki.symm)
  · have hx₁ := peirceBlock_le_peirceSpace_add_one h hx
    have hx₀ : p k ∈ peirceSpace ℝ (p i + p j) 0 := by
      simp [mem_peirceSpace, add_mul, hp.orthogonal i k hki.symm, hp.orthogonal j k hkj.symm]
    rw [mul_comm]
    exact mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero
      (hp.isIdempotentElem_add h).eq hx₁ hx₀

private theorem mul_mul_mem_half (hp : IsCompleteSystem p) {i j : ι} (h : i ≠ j) (x : J) :
    p i * (p j * x) ∈ peirceSpace ℝ (p i) ⅟(2 : ℝ) := by
  have hi := (hp.idempotent i).eq
  have hz := hp.mem_peirceSpace_zero_of_ne h
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_peirce_decomposition (R := ℝ) hi x
  have ha₀ : p j * a = 0 := by
    rw [mul_comm]
    exact mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero hi ha hz
  have hb₁ := mul_mem_peirceSpace_of_mem_zero hi hz hb
  have hc₀ := mul_mem_peirceSpace_of_mem_zero hi hz hc
  have hc₀' : p i * (p j * c) = 0 := by simpa using mem_peirceSpace.mp hc₀
  simp only [mul_add, ha₀, zero_add, hc₀', add_zero, mem_peirceSpace.mp hb₁]
  exact Submodule.smul_mem _ _ hb₁

/-- Applying two distinct multiplication operators lands in their off-diagonal block. -/
theorem mul_mul_mem_peirceBlock (hp : IsCompleteSystem p) {i j : ι} (h : i ≠ j) (x : J) :
    p i * (p j * x) ∈ peirceBlock p s(i, j) := by
  rw [peirceBlock_of_ne p h]
  refine ⟨hp.mul_mul_mem_half h x, ?_⟩
  have hc : p i * (p j * x) = p j * (p i * x) :=
    DFunLike.congr_fun (hp.commute_mulLeft i j).eq x
  rw [hc]
  exact hp.mul_mul_mem_half h.symm x

/-- The Peirce blocks of a complete system span the ambient algebra. -/
theorem iSup_peirceBlock_eq_top (hp : IsCompleteSystem p) : ⨆ s, peirceBlock p s = ⊤ := by
  classical
  let U := ⨆ s, peirceBlock p s
  refine eq_top_iff.mpr fun x _ => ?_
  have hsum : (∑ i, p i * x) = x := by rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]
  rw [← hsum]
  refine Submodule.sum_mem U fun i _ => ?_
  have hd : peirceOne ℝ (p i) x ∈ U :=
    Submodule.mem_iSup_of_mem s(i, i) (by
      rw [peirceBlock_diag]
      exact peirceOne_mem_peirceSpace (hp.idempotent i).eq x)
  have ho : (∑ j ∈ Finset.univ.erase i, p i * (p j * x)) ∈ U :=
    Submodule.sum_mem U fun j hj =>
      Submodule.mem_iSup_of_mem s(i, j)
        (hp.mul_mul_mem_peirceBlock (Finset.ne_of_mem_erase hj).symm x)
  have hsplit : p i * x = p i * (p i * x) + ∑ j ∈ Finset.univ.erase i, p i * (p j * x) := by
    conv_lhs => rw [← hsum, Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have heq : p i * x = peirceOne ℝ (p i) x +
      (2 : ℝ) • (∑ j ∈ Finset.univ.erase i, p i * (p j * x)) := by
    rw [peirceOne_apply, show (∑ j ∈ Finset.univ.erase i, p i * (p j * x)) =
      p i * x - p i * (p i * x) from eq_sub_of_add_eq' hsplit.symm]
    module
  rw [heq]
  exact U.add_mem hd (U.smul_mem _ ho)

end IsCompleteSystem

namespace IsCompleteSystem

variable [Fintype ι] [IsCommJordan J] {p : ι → J}

omit [Fintype ι] [IsCommJordan J] in
/-- The block projection fixes every vector of its Peirce block. -/
theorem peirceBlockProj_apply_eq_self {i j : ι} {x : J}
    (hx : x ∈ peirceBlock p s(i, j)) : peirceBlockProj p i j x = x := by
  classical
  by_cases h : i = j
  · subst j
    rw [peirceBlock_diag] at hx
    simpa only [peirceBlockProj_diag] using peirceOne_of_mem_peirceSpace_one hx
  · rw [peirceBlock_of_ne p h] at hx
    rw [peirceBlockProj_of_ne _ h]
    change (4 : ℝ) • (p i * (p j * x)) = x
    rw [mem_peirceSpace.mp hx.2, mul_smul_comm, mem_peirceSpace.mp hx.1]
    norm_num [invOf_eq_inv, smul_smul]

/-- The Peirce block projection has range equal to the corresponding block. -/
theorem range_peirceBlockProj (hp : IsCompleteSystem p) (i j : ι) :
    LinearMap.range (peirceBlockProj p i j) = peirceBlock p s(i, j) := by
  classical
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    by_cases h : i = j
    · subst j
      rw [peirceBlock_diag]
      simpa only [peirceBlockProj_diag] using
        peirceOne_mem_peirceSpace (R := ℝ) (hp.idempotent i).eq y
    · rw [peirceBlockProj_of_ne _ h]
      exact Submodule.smul_mem _ _ (hp.mul_mul_mem_peirceBlock h y)
  · exact fun x hx => ⟨x, peirceBlockProj_apply_eq_self hx⟩

/-- The block projection kills every vector in a different Peirce block. -/
theorem peirceBlockProj_apply_eq_zero (hp : IsCompleteSystem p) {i j k l : ι}
    (hne : s(k, l) ≠ s(i, j)) {x : J} (hx : x ∈ peirceBlock p s(k, l)) :
    peirceBlockProj p i j x = 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [peirceBlockProj_diag]
    by_cases h : i = k ∨ i = l
    · have hkl : k ≠ l := by
        rintro rfl
        rcases h with rfl | rfl <;> exact hne rfl
      rw [peirceBlock_of_ne p hkl] at hx
      have hhalf := hx
      apply peirceOne_of_mem_peirceSpace_invOf_two
      rcases h with rfl | rfl
      · exact hhalf.1
      · exact hhalf.2
    · exact peirceOne_of_mem_peirceSpace_zero
        (mem_peirceSpace.mpr (by simp [hp.mul_eq_zero_of_mem_peirceBlock
          (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h')) hx]))
  · rw [peirceBlockProj_of_ne _ hij]
    change (4 : ℝ) • (p i * (p j * x)) = 0
    have hout : (i ≠ k ∧ i ≠ l) ∨ (j ≠ k ∧ j ≠ l) := by
      have h := fun heq : (k, l) = (i, j) ∨ (k, l) = (j, i) =>
        hne (Sym2.mk_eq_mk_iff.mpr heq)
      grind
    rcases hout with hi | hj
    · have hc : p i * (p j * x) = p j * (p i * x) :=
        DFunLike.congr_fun (hp.commute_mulLeft i j).eq x
      rw [hc, hp.mul_eq_zero_of_mem_peirceBlock hi.1 hi.2 hx, mul_zero, smul_zero]
    · rw [hp.mul_eq_zero_of_mem_peirceBlock hj.1 hj.2 hx, mul_zero, smul_zero]

/-- The Peirce blocks of a complete system are independent submodules. -/
theorem iSupIndep_peirceBlock (hp : IsCompleteSystem p) : iSupIndep (peirceBlock p) := by
  classical
  intro s
  induction s using Sym2.ind with
  | _ i j =>
    have hker : (⨆ t, ⨆ (_ : t ≠ s(i, j)), peirceBlock p t) ≤
        LinearMap.ker (peirceBlockProj p i j) := by
      refine iSup_le fun t => ?_
      induction t using Sym2.ind with
      | _ k l =>
        exact iSup_le fun ht _ hx => LinearMap.mem_ker.mpr
          (hp.peirceBlockProj_apply_eq_zero ht hx)
    rw [Submodule.disjoint_def]
    intro x hx hx'
    exact (peirceBlockProj_apply_eq_self hx).symm.trans (LinearMap.mem_ker.mp (hker hx'))

/-- The Peirce spaces of a complete system form an internal direct sum. -/
theorem isInternal_peirceBlock [DecidableEq ι] (hp : IsCompleteSystem p) :
    DirectSum.IsInternal (peirceBlock p) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨hp.iSupIndep_peirceBlock, hp.iSup_peirceBlock_eq_top⟩

omit [Module ℝ J] [SMulCommClass ℝ J J] [IsCommJordan J] in
/-- Every partial sum of a complete system is an idempotent. -/
theorem isIdempotentElem_sum (hp : IsCompleteSystem p) (s : Finset ι) :
    IsIdempotentElem (∑ i ∈ s, p i) := by
  classical
  change (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => hp.orthogonal i j hji.symm)
    (fun h => False.elim (h hi))]
  exact (hp.idempotent i).eq

/-- Left multiplication by a diagonal linear combination acts by the average of the
two indexed coefficients on each Peirce block. -/
theorem sum_smul_mul_eq_smul_of_mem_peirceBlock [IsScalarTower ℝ J J]
    (hp : IsCompleteSystem p) (a : ι → ℝ) {i j : ι} {x : J}
    (hx : x ∈ peirceBlock p s(i, j)) :
    (∑ k, a k • p k) * x = ((a i + a j) / 2) • x := by
  classical
  rw [Finset.sum_mul]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · have hfix : p i * x = x := by
        rw [peirceBlock_diag, mem_peirceSpace, one_smul] at hx
        exact hx
      rw [smul_mul_assoc, hfix]
      module
    · intro k _ hk
      rw [smul_mul_assoc, hp.mul_eq_zero_of_mem_peirceBlock hk hk hx, smul_zero]
    · simp
  · have hsum := Finset.sum_sdiff (f := fun k => (a k • p k) * x)
      (Finset.subset_univ ({i, j} : Finset ι))
    rw [← hsum, Finset.sum_pair hij]
    have hzero : (∑ k ∈ Finset.univ \ {i, j}, (a k • p k) * x) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have h := (Finset.mem_sdiff.mp hk).2
      have hki : k ≠ i := fun e => h (by simp [e])
      have hkj : k ≠ j := fun e => h (by simp [e])
      rw [smul_mul_assoc, hp.mul_eq_zero_of_mem_peirceBlock hki hkj hx, smul_zero]
    rw [peirceBlock_of_ne p hij] at hx
    rw [hzero, zero_add, smul_mul_assoc, smul_mul_assoc,
      mem_peirceSpace.mp hx.1, mem_peirceSpace.mp hx.2, invOf_eq_inv]
    module

end IsCompleteSystem

end TauCeti.Jordan
