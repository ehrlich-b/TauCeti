/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Group.Torsion
public import TauCeti.Algebra.Jordan.Basic

import Mathlib.Tactic.Abel

/-!
# Power associativity of commutative Jordan algebras

The linearized Jordan identity relates successive commutators on each antidiagonal in the
exponents. Antisymmetry forces a positive multiple of each commutator to vanish. Injectivity of
positive natural scalar multiplication then gives the product law.

## Main results

* `jpow_mul_jpow`: the powers of one element multiply by adding exponents.
* `jpow_mul_left_comm`: left multiplication by two powers of one element commutes.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Chapter II.
* McCrimmon, *A Taste of Jordan Algebras*, §II.4.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/Power.lean` and
  `EuclideanJordan/PowerAssoc.lean` at a83407e4 (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

section Power

variable {A : Type*} [MulOneClass A]

/-- Jordan powers are obtained by repeatedly multiplying on the left, starting from the unit. -/
@[expose]
def jpow (x : A) : ℕ → A
  | 0 => 1
  | n + 1 => x * jpow x n

/-- The zeroth Jordan power is the unit. -/
@[simp] theorem jpow_zero (x : A) : jpow x 0 = 1 := rfl

/-- Each successive Jordan power multiplies by the element on the left. -/
theorem jpow_succ (x : A) (n : ℕ) : jpow x (n + 1) = x * jpow x n := rfl

/-- The first Jordan power is the element itself. -/
@[simp] theorem jpow_one (x : A) : jpow x 1 = x := mul_one x

end Power

private def power {A : Type*} [Mul A] (x : A) (n : ℕ) : A :=
  Nat.rec x (fun _ y => x * y) n

private theorem power_zero {A : Type*} [Mul A] (x : A) : power x 0 = x := rfl

private theorem power_succ {A : Type*} [Mul A] (x : A) (n : ℕ) :
    power x (n + 1) = x * power x n := rfl

section Ring

variable {A : Type*} [NonUnitalNonAssocCommRing A]

private theorem power_mul_of_commute {x : A} {m : ℕ}
    (h : ∀ w, x * (power x m * w) = power x m * (x * w)) (n : ℕ) :
    power x m * power x n = power x (m + n + 1) := by
  induction n with
  | zero => exact mul_comm _ _
  | succ n ih =>
      rw [power_succ, ← h, ih, show m + (n + 1) + 1 = (m + n + 1) + 1 from by omega]
      rfl

private def cm (x : A) (i j : ℕ) (w : A) : A :=
  power x i * (power x j * w) - power x j * (power x i * w)

private theorem cm_antisymm (x : A) (i j : ℕ) (w : A) : cm x i j w = -cm x j i w := by
  simp [cm]

private theorem commute_of_cm {x : A} {i : ℕ} (h : ∀ w, cm x 0 i w = 0) :
    ∀ w, x * (power x i * w) = power x i * (x * w) :=
  fun w => sub_eq_zero.mp (h w)

variable [IsCommJordan A] [HasUniqueDiv A]

private theorem cm_cyclic (x : A) (i j : ℕ)
    (hij : power x i * power x j = power x (i + j + 1)) (w : A) :
    cm x j (i + 1) w + cm x 0 (i + j + 1) w + cm x i (j + 1) w = 0 := by
  have h₂ : IsSMulRegular A (2 : ℕ) :=
    nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  have h := mul_mul_mul_sub_add_add_eq_zero h₂ x (power x i) (power x j) w
  rw [hij, mul_comm (power x j) x] at h
  convert h using 1
  simp only [cm, power_zero, power_succ]
  abel

-- Induct on total degree, then propagate along its antidiagonal and cancel the wrap-around.
private theorem cm_eq_zero (x : A) (N : ℕ) :
    ∀ i j : ℕ, i + j ≤ N → ∀ w : A, cm x i j w = 0 := by
  induction N with
  | zero =>
      intro i j hij w
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
      exact sub_self _
  | succ N ih =>
      have hA : ∀ i j : ℕ, i + j ≤ N → power x i * power x j = power x (i + j + 1) :=
        fun i j hij => power_mul_of_commute (commute_of_cm (fun w => ih 0 i (by omega) w)) j
      intro i j hij w
      rcases Nat.lt_or_ge (i + j) (N + 1) with hlt | hge
      · exact ih i j (by omega) w
      · have hsum : i + j = N + 1 := by omega
        set c : A := cm x 0 (N + 1) w with hc
        have key : ∀ k : ℕ, k ≤ N + 1 → ∀ l : ℕ, k + l = N + 1 →
            cm x k l w = (k + 1) • c := by
          intro k
          induction k with
          | zero =>
              intro _ l hl
              obtain rfl : l = N + 1 := by omega
              simp [hc]
          | succ k ihk =>
              intro hk l hl
              have hcyc := cm_cyclic x l k (hA l k (by omega)) w
              rw [show l + k + 1 = N + 1 from by omega] at hcyc
              rw [ihk (by omega) (l + 1) (by omega), cm_antisymm x l (k + 1) w, ← hc] at hcyc
              rw [(add_neg_eq_zero.mp hcyc).symm, ← succ_nsmul]
        have hlast : cm x (N + 1) 0 w = (N + 2) • c := key (N + 1) le_rfl 0 (by omega)
        have hneg : cm x (N + 1) 0 w = -c := by rw [cm_antisymm x (N + 1) 0 w, ← hc]
        have hzero : (N + 3) • c = 0 := by
          rw [show N + 3 = (N + 2) + 1 from rfl, succ_nsmul, ← hlast, hneg]
          exact neg_add_cancel c
        rw [key i (by omega) j (by omega),
          (nsmul_eq_zero_iff_right (by omega : N + 3 ≠ 0)).mp hzero, smul_zero]

end Ring

section Unital

variable {A : Type*} [NonAssocCommRing A]

private theorem jpow_succ_eq_power (x : A) (n : ℕ) : jpow x (n + 1) = power x n := by
  induction n with
  | zero => exact jpow_one x
  | succ n ih => rw [jpow_succ, power_succ, ih]

variable [IsCommJordan A] [HasUniqueDiv A]

/-- Two powers of a Jordan element multiply by adding their exponents. -/
theorem jpow_mul_jpow (x : A) (m n : ℕ) : jpow x m * jpow x n = jpow x (m + n) := by
  cases m with
  | zero => simp
  | succ m =>
    cases n with
    | zero => simp
    | succ n =>
      rw [show m + 1 + (n + 1) = (m + n + 1) + 1 by omega]
      simp only [jpow_succ_eq_power]
      exact power_mul_of_commute
        (commute_of_cm (fun w => cm_eq_zero x m 0 m (by simp) w)) n

/-- Left multiplication by any two powers of a Jordan element commutes. -/
theorem jpow_mul_left_comm (x w : A) (m n : ℕ) :
    jpow x m * (jpow x n * w) = jpow x n * (jpow x m * w) := by
  cases m with
  | zero => simp
  | succ m =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [jpow_succ_eq_power]
      exact sub_eq_zero.mp (cm_eq_zero x (m + n) m n le_rfl w)

end Unital

end TauCeti.Jordan
