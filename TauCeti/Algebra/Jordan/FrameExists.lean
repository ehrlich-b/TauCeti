/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Sigma
public import TauCeti.Algebra.Jordan.Primitive

/-!
# Existence of Jordan frames

A proper idempotent in the Peirce `1`-space of an idempotent splits it into two orthogonal
idempotents. Their Peirce `1`-spaces have smaller dimension, so the process ends at primitive
idempotents.

## Main results

* `exists_primitive_decomposition`: every idempotent is a sum of orthogonal primitive idempotents.
* `exists_isJordanFrame`: splitting the unit gives a Jordan frame, including the empty frame
  in the zero algebra.
* `IsCompleteSystem.exists_refinement`: any complete system refines to a Jordan frame.
* `exists_isJordanFrame_sum_eq`: any idempotent is the sum of part of a Jordan frame.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Proposition IV.1.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/FrameExists.lean` at a83407e4
  (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

variable {J : Type*} [NonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]
  [IsCommJordan J] [Module.Finite ℝ J]

private structure IsPrimitiveDecomposition (c : J) {n : ℕ} (p : Fin n → J) : Prop where
  primitive : ∀ i, IsPrimitive (p i)
  fixed : ∀ i, c * p i = p i
  orthogonal : ∀ i j, i ≠ j → p i * p j = 0
  sum_eq : ∑ i, p i = c

private theorem peirceSpace_one_lt_of_mul_eq_self {c d : J} (hc : IsIdempotentElem c)
    (hd : IsIdempotentElem d) (hcd : c * d = d) (hne : d ≠ c) :
    Module.finrank ℝ (peirceSpace ℝ d 1) < Module.finrank ℝ (peirceSpace ℝ c 1) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (peirceSpace_one_le_of_mul_eq_self hd hcd) fun h => hne ?_
  have hmem : c ∈ peirceSpace ℝ c 1 := mem_peirceSpace.mpr (by simpa using hc.eq)
  have hdmem : c ∈ peirceSpace ℝ d 1 := h.symm ▸ hmem
  rw [mem_peirceSpace, one_smul] at hdmem
  exact hcd.symm.trans ((mul_comm c d).trans hdmem)

omit [Module.Finite ℝ J] in
private theorem append_primitiveDecomposition {d e : J} {n m : ℕ}
    {p : Fin n → J} {q : Fin m → J} (hd : IsIdempotentElem d) (he : IsIdempotentElem e)
    (hde : d * e = 0)
    (hp : IsPrimitiveDecomposition d p) (hq : IsPrimitiveDecomposition e q) :
    IsPrimitiveDecomposition (d + e) (Fin.append p q) := by
  have hdp (i : Fin n) : p i ∈ peirceSpace ℝ d 1 :=
    mem_peirceSpace.mpr (by simpa using hp.fixed i)
  have hqz (j : Fin m) : q j ∈ peirceSpace ℝ d 0 := by
    have hfix : (1 - d) * e = e := by rw [sub_mul, one_mul, hde, sub_zero]
    have h : q j ∈ peirceSpace ℝ e 1 := mem_peirceSpace.mpr (by simpa using hq.fixed j)
    rw [← peirceSpace_one_sub_one (R := ℝ)]
    exact peirceSpace_one_le_of_mul_eq_self he hfix h
  have hpz (i : Fin n) : p i * e = 0 :=
    mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero hd.eq (hdp i)
      (mem_peirceSpace.mpr (by simpa using hde))
  have hcross (i : Fin n) (j : Fin m) : p i * q j = 0 :=
    mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero hd.eq (hdp i) (hqz j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Fin.addCases (fun i => by simpa using hp.primitive i)
      (fun j => by simpa using hq.primitive j)
  · refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · rw [Fin.append_left, add_mul, hp.fixed i, mul_comm e, hpz, add_zero]
    · rw [Fin.append_right, add_mul, hq.fixed j,
        show d * q j = 0 by simpa using mem_peirceSpace.mp (hqz j), zero_add]
  · refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · refine Fin.addCases (fun i' h => ?_) (fun j _ => ?_)
      · simpa using hp.orthogonal i i' (fun heq => h (congrArg (Fin.castAdd m) heq))
      · simpa using hcross i j
    · refine Fin.addCases (fun i _ => ?_) (fun j' h => ?_)
      · simpa [mul_comm] using hcross i j
      · simpa using hq.orthogonal j j' (fun heq => h (congrArg (Fin.natAdd n) heq))
  · simp [Fin.sum_univ_add, hp.sum_eq, hq.sum_eq]

private theorem exists_primitiveDecomposition {c : J} (hc : IsIdempotentElem c) :
    ∃ (n : ℕ) (p : Fin n → J), IsPrimitiveDecomposition c p := by
  classical
  generalize hdim : Module.finrank ℝ (peirceSpace ℝ c 1) = N
  induction N using Nat.strong_induction_on generalizing c with
  | ind N ih =>
    by_cases h₀ : c = 0
    · exact ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [h₀]⟩⟩
    by_cases hprim : IsPrimitive c
    · refine ⟨1, fun _ => c, ⟨fun _ => hprim, fun _ => hc.eq, ?_, by simp⟩⟩
      exact fun i j hij => (hij (Subsingleton.elim i j)).elim
    have hproper : ∃ d : J, IsIdempotentElem d ∧ c * d = d ∧ d ≠ 0 ∧ d ≠ c := by
      by_contra! hn
      exact hprim ⟨h₀, hc, fun d hd hcd => or_iff_not_imp_left.mpr (hn d hd hcd)⟩
    obtain ⟨d, hd, hcd, hdz, hdc⟩ := hproper
    let e := c - d
    have hde : d * e = 0 := by
      dsimp [e]
      rw [mul_sub, mul_comm d c, hcd, hd.eq, sub_self]
    have hce : c * e = e := by
      dsimp [e]
      rw [mul_sub, hc.eq, hcd]
    have he : IsIdempotentElem e := by
      change e * e = e
      rw [show e * e = c * e - d * e by exact sub_mul _ _ _, hce, hde, sub_zero]
    have hec : e ≠ c := fun h => hdz (sub_eq_self.mp h)
    have hdlt := peirceSpace_one_lt_of_mul_eq_self hc hd hcd hdc
    have helt := peirceSpace_one_lt_of_mul_eq_self hc he hce hec
    obtain ⟨n, p, hp⟩ := ih _ (hdim ▸ hdlt) hd rfl
    obtain ⟨m, q, hq⟩ := ih _ (hdim ▸ helt) he rfl
    have hsum : d + e = c := by simp [e, add_sub_cancel]
    exact ⟨n + m, Fin.append p q, hsum ▸ append_primitiveDecomposition hd he hde hp hq⟩

/-- Every idempotent decomposes as a sum of pairwise orthogonal primitive idempotents
in its Peirce `1`-space. -/
theorem exists_primitive_decomposition {c : J} (hc : IsIdempotentElem c) :
    ∃ (n : ℕ) (p : Fin n → J), (∀ i, IsPrimitive (p i)) ∧ (∀ i, c * p i = p i) ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧ ∑ i, p i = c := by
  obtain ⟨n, p, hp⟩ := exists_primitiveDecomposition hc
  exact ⟨n, p, hp.primitive, hp.fixed, hp.orthogonal, hp.sum_eq⟩

/-- A finite-dimensional real Jordan algebra has a Jordan frame. -/
theorem exists_isJordanFrame : ∃ (n : ℕ) (p : Fin n → J), IsJordanFrame p := by
  have h₁ : IsIdempotentElem (1 : J) := one_mul 1
  obtain ⟨n, p, hprim, _, horth, hsum⟩ := exists_primitive_decomposition h₁
  exact ⟨n, p, ⟨fun i => (hprim i).nonzero, fun i => (hprim i).idempotent,
    horth, hsum⟩, hprim⟩

/-- Any complete system can be refined to a Jordan frame by splitting each member. -/
theorem IsCompleteSystem.exists_refinement {ι : Type*} [Fintype ι] {p : ι → J}
    (hp : IsCompleteSystem p) :
    ∃ (n : ι → ℕ) (q : (Σ i, Fin (n i)) → J),
      IsJordanFrame q ∧ ∀ i, (∑ j, q ⟨i, j⟩) = p i := by
  classical
  choose n q hprim hfix horth hsum using
    fun i => exists_primitive_decomposition (hp.idempotent i)
  let f (a : Σ i, Fin (n i)) := q a.1 a.2
  have hf (a : Σ i, Fin (n i)) : IsPrimitive (f a) := hprim a.1 a.2
  refine ⟨n, f, ⟨⟨fun a => (hf a).nonzero, fun a => (hf a).idempotent, ?_, ?_⟩, hf⟩, hsum⟩
  · rintro ⟨i, x⟩ ⟨j, y⟩ hne
    by_cases h : i = j
    · subst j
      exact horth i x y (fun hxy => hne (by cases hxy; rfl))
    · have hx : q i x ∈ peirceSpace ℝ (p i) 1 :=
        mem_peirceSpace.mpr (by simpa using hfix i x)
      have hy : q j y ∈ peirceSpace ℝ (p j) 1 :=
        mem_peirceSpace.mpr (by simpa using hfix j y)
      have hij : p i ∈ peirceSpace ℝ (p j) 0 :=
        mem_peirceSpace.mpr (by simp [hp.orthogonal j i (Ne.symm h)])
      have hy₀ : q j y ∈ peirceSpace ℝ (p i) 0 := mem_peirceSpace.mpr (by
        rw [zero_smul, mul_comm]
        exact mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero
          (hp.idempotent j).eq hy hij)
      exact mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero
        (hp.idempotent i).eq hx hy₀
  · rw [Fintype.sum_sigma]
    simp only [f, hsum, hp.sum_eq_one]

/-- An idempotent is the sum of the first part of a Jordan frame formed by refining it and
its complement. -/
theorem exists_isJordanFrame_sum_eq {c : J} (hc : IsIdempotentElem c) :
    ∃ (n m : ℕ) (p : Fin n → J) (q : Fin m → J),
      IsJordanFrame (Fin.append p q) ∧ (∑ i, p i) = c := by
  obtain ⟨n, p, hp⟩ := exists_primitiveDecomposition hc
  obtain ⟨m, q, hq⟩ := exists_primitiveDecomposition hc.one_sub
  have h := append_primitiveDecomposition hc hc.one_sub hc.mul_one_sub_self hp hq
  refine ⟨n, m, p, q, ⟨⟨fun i => (h.primitive i).nonzero, fun i => (h.primitive i).idempotent,
      h.orthogonal, h.sum_eq.trans ?_⟩, h.primitive⟩, hp.sum_eq⟩
  exact add_sub_cancel c 1

end TauCeti.Jordan
