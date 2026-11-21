/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.Jordan.Frame.Exists
public import TauCeti.Algebra.Jordan.Spectral
public import TauCeti.Algebra.Group.Action.CommMagma
public import TauCeti.RingTheory.Idempotents.LinearIndependent

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

/-- The rank is the supremum of the cardinalities of Jordan frames, with the empty or unbounded
case assigned the natural-number supremum `0`. -/
noncomputable def rank (J : Type*) [NonAssocSemiring J] : ℕ :=
  sSup {n : ℕ | ∃ p : Fin n → J, IsJordanFrame p}

section Bounds

variable {J : Type*} [NonAssocCommRing J] [Module ℝ J] [IsScalarTower ℝ J J]
  [Module.Finite ℝ J]

/-- A Jordan frame has at most as many members as the dimension of the algebra. -/
theorem IsJordanFrame.card_le_finrank {n : ℕ} {p : Fin n → J} (hp : IsJordanFrame p) :
    n ≤ Module.finrank ℝ J := by
  have h := hp.toIsCompleteSystem
  simpa only [Fintype.card_fin] using
    (linearIndependent_of_pairwise_mul_eq_zero (k := ℝ)
      h.idempotent (fun _ _ hne => h.orthogonal _ _ hne) h.nonzero).fintype_card_le_finrank

private theorem bddAbove_frameSizes :
    BddAbove {n : ℕ | ∃ p : Fin n → J, IsJordanFrame p} := by
  refine ⟨Module.finrank ℝ J, ?_⟩
  rintro _ ⟨p, hp⟩
  exact hp.card_le_finrank

/-- A Jordan frame has at most `rank J` members. -/
theorem IsJordanFrame.card_le_rank {n : ℕ} {p : Fin n → J} (hp : IsJordanFrame p) :
    n ≤ rank J :=
  le_csSup (bddAbove_frameSizes (J := J)) ⟨p, hp⟩

/-- The rank is at most the real dimension. -/
theorem rank_le_finrank : rank J ≤ Module.finrank ℝ J :=
  csSup_le' fun _ ⟨_, hp⟩ => hp.card_le_finrank

/-- There is a Jordan frame whose size is the rank. -/
theorem exists_jordanFrame_card_rank [SMulCommClass ℝ J J] [IsCommJordan J] :
    ∃ p : Fin (rank J) → J, IsJordanFrame p := by
  exact Nat.sSup_mem ⟨_, exists_isJordanFrame (J := J).choose_spec⟩
    (bddAbove_frameSizes (J := J))

end Bounds

section Spectral

variable {J : Type*} [NonAssocCommRing J] [Module ℝ J] [SMulCommClass ℝ J J]
  [IsCommJordan J] [Module.Finite ℝ J] [IsFormallyReal J]

/-- Every element admits a decomposition in some Jordan frame, obtained by refining its
spectral idempotents. -/
theorem exists_spectral_frame (x : J) :
    ∃ (n : ℕ) (p : Fin n → J) (coeff : Fin n → ℝ),
      IsJordanFrame p ∧ x = ∑ i, coeff i • p i := by
  classical
  let := IsScalarTower.of_commMagma ℝ J
  obtain ⟨_, p, c, hp, _, h, _, _⟩ := spectralResolution x
  obtain ⟨n, q, hq, heq⟩ := hp.exists_refinement
  let m := Fintype.card (Σ i, Fin (n i))
  let e : Fin m ≃ (Σ i, Fin (n i)) := (Fintype.equivFin _).symm
  refine ⟨m, q ∘ e, fun j => c (e j).1, hq.reindex e, ?_⟩
  let f (j : Σ i, Fin (n i)) := c j.1 • q j
  calc
    x = ∑ i, c i • p i := h
    _ = ∑ j, f j := by
      rw [Fintype.sum_sigma]
      exact Finset.sum_congr rfl fun i _ => by simp only [f, ← Finset.smul_sum, heq]
    _ = ∑ j, f (e j) := (e.sum_comp f).symm

end Spectral

end TauCeti.Jordan
