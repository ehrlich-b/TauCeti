/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Regular.SMul

/-!
# Jordan homomorphisms

A linear multiplicative map between Jordan algebras is a Mathlib `NonUnitalAlgHom`.
Its identities, composition and inverse construction are already available there.

## Main results

* `AddMonoidHom.map_mul_of_map_mul_self`: polarization recovers product preservation
  from square preservation when doubling is injective on the target.
* `NonUnitalAlgHom.map_one_of_surjective`: a surjective Jordan homomorphism preserves the unit.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Chapter II.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/OrderAuto.lean` at a83407e4
  (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

variable {A B : Type*}

/-- A square-preserving additive map between commutative nonassociative semirings is
multiplicative if doubling is injective in the target. -/
theorem AddMonoidHom.map_mul_of_map_mul_self [NonUnitalNonAssocCommSemiring A]
    [NonUnitalNonAssocCommSemiring B] [IsCancelAdd B]
    (f : A →+ B) (h₂ : IsSMulRegular B (2 : ℕ)) (h : ∀ x, f (x * x) = f x * f x)
    (x y : A) : f (x * y) = f x * f y := by
  have hxy := h (x + y)
  simp only [add_mul, mul_add, map_add, mul_comm y x, mul_comm (f y) (f x), h] at hxy
  simp only [add_assoc] at hxy
  have hcross := add_left_cancel hxy
  simp only [← add_assoc] at hcross
  exact h₂ (by simpa only [two_nsmul] using add_right_cancel hcross)

/-- A surjective multiplicative map of unital algebras sends the unit to the unit. -/
theorem NonUnitalAlgHom.map_one_of_surjective {R : Type*} [Monoid R]
    [NonAssocSemiring A] [NonAssocSemiring B] [DistribMulAction R A] [DistribMulAction R B]
    (f : A →ₙₐ[R] B) (hf : Function.Surjective f) : f 1 = 1 := by
  obtain ⟨x, hx⟩ := hf 1
  calc
    f 1 = f 1 * f x := by rw [hx, mul_one]
    _ = f (1 * x) := (map_mul f 1 x).symm
    _ = 1 := by rw [one_mul, hx]
