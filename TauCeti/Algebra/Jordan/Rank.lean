/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.Jordan.FrameExists

/-!
# Rank bounds for real Jordan algebras

Nonzero pairwise orthogonal idempotents are linearly independent, so the sizes of frames
in a finite-dimensional real Jordan algebra have a maximum.

## Main results

* `rank`: the supremum of the cardinalities of Jordan frames.
* `rank_le_finrank`: the rank is bounded by the dimension.
* `exists_jordanFrame_card_rank`: this bound on frame sizes is attained at the rank.
* `exists_spectral_frame`: every element is diagonal in a Jordan frame of some size.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Theorems III.1.1 and III.1.2.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/Rank.lean`,
  `EuclideanJordan/FrameExists.lean` and `EuclideanJordan/Spectral.lean` at a83407e4
  (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

/-- The rank is the supremum of the cardinalities of Jordan frames. -/
noncomputable def rank (J : Type*) [NonAssocSemiring J] : ℕ :=
  sSup {n : ℕ | ∃ p : Fin n → J, IsJordanFrame p}

section LinearIndependent

variable {K J ι : Type*} [Field K] [NonAssocRing J] [Module K J] [SMulCommClass K J J]
  [Fintype ι] {p : ι → J}

/-- Members of a complete system are linearly independent. Multiplication by one member
isolates its coefficient in any linear relation. -/
theorem IsCompleteSystem.linearIndependent (hp : IsCompleteSystem p) :
    LinearIndependent K p := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun a ha i => ?_
  have h : p i * (∑ j, a j • p j) = 0 := by rw [ha, mul_zero]
  rw [Finset.mul_sum, Finset.sum_eq_single i] at h
  · rw [mul_smul_comm, (hp.idempotent i).eq] at h
    exact (smul_eq_zero.mp h).resolve_right (hp.nonzero i)
  · intro j _ hji
    rw [mul_smul_comm, hp.orthogonal i j hji.symm, smul_zero]
  · simp

end LinearIndependent

section Bounds

variable {J : Type*} [NonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]
  [Module.Finite ℝ J]

private theorem bddAbove_frameSizes :
    BddAbove {n : ℕ | ∃ p : Fin n → J, IsJordanFrame p} := by
  refine ⟨Module.finrank ℝ J, ?_⟩
  rintro _ ⟨p, hp⟩
  simpa only [Fintype.card_fin] using
    (hp.1.linearIndependent (K := ℝ)).fintype_card_le_finrank

/-- A Jordan frame has at most `rank J` members. -/
theorem IsJordanFrame.card_le_rank {n : ℕ} {p : Fin n → J} (hp : IsJordanFrame p) :
    n ≤ rank J :=
  le_csSup (bddAbove_frameSizes (J := J)) ⟨p, hp⟩

/-- The rank is at most the real dimension. -/
theorem rank_le_finrank : rank J ≤ Module.finrank ℝ J :=
  csSup_le' fun _ ⟨_, hp⟩ => by
    simpa only [Fintype.card_fin] using
      (hp.1.linearIndependent (K := ℝ)).fintype_card_le_finrank

/-- There is a Jordan frame whose size is the rank. -/
theorem exists_jordanFrame_card_rank [IsCommJordan J] :
    ∃ p : Fin (rank J) → J, IsJordanFrame p := by
  exact Nat.sSup_mem ⟨_, exists_isJordanFrame (J := J).choose_spec⟩
    (bddAbove_frameSizes (J := J))

end Bounds

section Spectral

variable {J : Type*} [NonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]
  [IsScalarTower ℝ J J] [IsCommJordan J] [Module.Finite ℝ J] [IsFormallyReal J]

/-- Every element admits a decomposition in some Jordan frame, obtained by refining its
spectral idempotents. -/
theorem exists_spectral_frame (x : J) :
    ∃ (n : ℕ) (p : Fin n → J) (coeff : Fin n → ℝ),
      IsJordanFrame p ∧ x = ∑ i, coeff i • p i := by
  classical
  obtain ⟨_, p, c, hp, _, h, _, _⟩ := spectralResolution x
  obtain ⟨n, q, hq, heq⟩ := hp.exists_refinement
  let m := Fintype.card (Σ i, Fin (n i))
  let e : Fin m ≃ (Σ i, Fin (n i)) := (Fintype.equivFin _).symm
  refine ⟨m, q ∘ e, fun j => c (e j).1, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact fun j => hq.1.nonzero (e j)
  · exact fun j => hq.1.idempotent (e j)
  · exact fun i j hne => hq.1.orthogonal (e i) (e j) (e.injective.ne hne)
  · exact (e.sum_comp q).trans hq.1.sum_eq_one
  · exact fun j => hq.2 (e j)
  · let f (j : Σ i, Fin (n i)) := c j.1 • q j
    calc
      x = ∑ i, c i • p i := h
      _ = ∑ j, f j := by
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl fun i _ => by simp only [f, ← Finset.smul_sum, heq]
      _ = ∑ j, f (e j) := (e.sum_comp f).symm

end Spectral

end TauCeti.Jordan
