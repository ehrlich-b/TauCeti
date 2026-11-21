/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import TauCeti.Algebra.Ring.IsFormallyReal

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-!
# Minimal polynomials in formally real algebras

In a formally real real algebra the minimal polynomial of an integral element is squarefree by
reducedness. A nonreal root would give a quadratic factor that is a sum of two squares. A Bézout
identity isolates that factor and turns it into a vanishing sum of squares in the algebra.

## Main results

* `minpoly.splits_of_isFormallyReal`: the minimal polynomial of an element of a
  formally real real algebra splits over the reals when the element is integral.
* `minpoly.aeval_eq_of_eqOn_roots_of_isFormallyReal`: polynomial evaluation depends
  only on the values at those roots.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Theorem III.1.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/Spectral.lean` at a83407e4
  (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

open Polynomial

namespace minpoly

variable {A : Type*} [CommRing A] [Algebra ℝ A] [IsFormallyReal A]

private theorem aeval_quadratic_eq_zero {a : A} {z : ℂ} (hz : z.im ≠ 0)
    (hroot : Polynomial.aeval z (minpoly ℝ a) = 0) (hsq : Squarefree (minpoly ℝ a)) : False := by
  let q : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
  have hdvd : q ∣ minpoly ℝ a :=
    (minpoly ℝ a).quadratic_dvd_of_aeval_eq_zero_im_ne_zero hroot hz
  obtain ⟨u, hu⟩ := hdvd
  have hcop : IsCoprime q u := (IsRelPrime.of_squarefree_mul (hu ▸ hsq)).isCoprime
  obtain ⟨α, β, hbez⟩ := hcop
  let e := Polynomial.aeval a (β * u)
  have hqe : Polynomial.aeval a q * e = 0 := by
    have heq : q * (β * u) = β * minpoly ℝ a := by rw [hu]; ring
    rw [← map_mul, heq, map_mul, minpoly.aeval, mul_zero]
  let r := (a - algebraMap ℝ A z.re) * e
  let i := z.im • e
  have hsum : r * r + i * i = 0 := by
    have hq : q = (X - C z.re) ^ 2 + (C z.im) ^ 2 := by
      have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      simp only [q, hnorm, map_add, map_pow, map_mul, map_ofNat]
      ring
    have h := congrArg (· * e) hqe
    rw [hq, map_add, map_pow, map_pow, map_sub, aeval_X, aeval_C, aeval_C, zero_mul] at h
    dsimp [r, i]
    rw [Algebra.smul_def]
    linear_combination h
  have hi : i = 0 := IsFormallyReal.eq_zero_of_mul_self_eq_zero
    (IsFormallyReal.eq_zero_of_add_left (.mul_self r) (.mul_self i) hsum)
  have he : e = 0 := (smul_eq_zero.mp hi).resolve_left hz
  have hqu : q ∣ β * u := dvd_trans ⟨u, hu⟩ (minpoly.dvd ℝ a he)
  have hunit : IsUnit q := isUnit_of_dvd_one (hbez ▸ dvd_add (dvd_mul_left q α) hqu)
  have hdeg : q.natDegree = 2 := by dsimp [q]; compute_degree!
  exact (by decide : (2 : ℕ) ≠ 0) (hdeg ▸ natDegree_eq_zero_of_isUnit hunit)

/-- An integral element of a formally real real algebra has a split minimal polynomial. -/
theorem splits_of_isFormallyReal {a : A} (ha : IsIntegral ℝ a) : (minpoly ℝ a).Splits := by
  have hsq : Squarefree (minpoly ℝ a) :=
    (minpoly.isRadical ℝ a).squarefree (minpoly.ne_zero ha)
  refine (IsAlgClosed.splits (p := (minpoly ℝ a).map (algebraMap ℝ ℂ))).of_splits_algebraMap ?_
  intro z hz
  have him : z.im = 0 := by
    by_contra h
    exact aeval_quadratic_eq_zero h (mem_rootSet'.mp hz).2 hsq
  exact ⟨z.re, by apply Complex.ext <;> simp [him]⟩

/-- Polynomials agreeing on the real roots of the minimal polynomial evaluate equally
at an integral element of a formally real real algebra. -/
theorem aeval_eq_of_eqOn_roots_of_isFormallyReal {a : A} (ha : IsIntegral ℝ a) {f g : ℝ[X]}
    (h : ∀ r ∈ (minpoly ℝ a).roots, f.eval r = g.eval r) :
    Polynomial.aeval a f = Polynomial.aeval a g := by
  classical
  let m := minpoly ℝ a
  have hsplit : m.Splits := minpoly.splits_of_isFormallyReal ha
  have hsep : m.Separable := PerfectField.separable_iff_squarefree.mpr
    ((minpoly.isRadical ℝ a).squarefree (minpoly.ne_zero ha))
  have hnodup := Polynomial.nodup_roots hsep
  have hprod : m = ∏ r ∈ m.roots.toFinset, (X - C r) := calc
    m = (m.roots.map (fun r => X - C r)).prod := hsplit.eq_prod_roots_of_monic (minpoly.monic ha)
    _ = _ := by
      change (m.roots.map _).prod = ((m.roots.toFinset.val).map _).prod
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hdiv : m ∣ f - g := by
    rw [hprod]
    refine Finset.prod_dvd_of_coprime
      ((pairwise_coprime_X_sub_C (Function.injective_id (α := ℝ))).set_pairwise _) ?_
    intro r hr
    apply dvd_iff_isRoot.mpr
    simpa only [IsRoot.def, eval_sub, sub_eq_zero] using h r (Multiset.mem_toFinset.mp hr)
  obtain ⟨u, hu⟩ := hdiv
  apply sub_eq_zero.mp
  rw [← map_sub, hu, map_mul, minpoly.aeval, zero_mul]

end minpoly
