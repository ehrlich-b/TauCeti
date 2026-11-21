/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Symmetrized
public import Mathlib.Algebra.Ring.Invertible
public import TauCeti.Algebra.Jordan.Subalgebra

/-!
# The Jordan algebra of self-adjoint elements

The self-adjoint elements of a star algebra over a commutative scalar ring with invertible
`2` form a subalgebra for the symmetrized multiplication.

## Main results

* `selfAdjointJordan` is the subalgebra of self-adjoint elements in the symmetrization.
* It inherits the Jordan identity, the ambient unit and compatible scalar multiplication.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Chapter II and Section III.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/HermitianCarrier.lean` at a83407e4
  (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace SymAlg

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The symmetrization of an associative ring is a commutative nonassociative ring. -/
instance instNonAssocCommRingSym [Invertible (2 : A)] : NonAssocCommRing Aˢʸᵐ where
  __ := (inferInstance : NonAssocRing Aˢʸᵐ)
  mul_comm := SymAlg.mul_comm

variable [Invertible (2 : A)]

/-- The symmetrized product is half the sum of the two products in the original algebra. -/
theorem unsym_mul_eq_smul [Invertible (2 : R)] (x y : Aˢʸᵐ) :
    unsym (x * y) = ⅟(2 : R) • (unsym x * unsym y + unsym y * unsym x) := by
  have hinv : ⅟(2 : A) = algebraMap R A (⅟(2 : R)) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap R A) 2, ← map_mul, mul_invOf_self, map_one]
  rw [unsym_mul, Algebra.smul_def, hinv]

/-- Scalar multiplication associates with the symmetrized multiplication. -/
instance : IsScalarTower R Aˢʸᵐ Aˢʸᵐ where
  smul_assoc r x y := by
    change (r • x) * y = r • (x * y)
    apply unsym_injective
    simp only [unsym_mul, unsym_smul, smul_mul_assoc, mul_smul_comm, ← smul_add]

/-- Scalar multiplication commutes with the symmetrized multiplication. -/
instance : SMulCommClass R Aˢʸᵐ Aˢʸᵐ where
  smul_comm r x y := by
    change r • (x * y) = x * (r • y)
    rw [mul_comm x y, ← smul_mul_assoc, mul_comm (r • y) x]

variable (R A) [StarMul R] [TrivialStar R] [StarRing A] [StarModule R A]

/-- The self-adjoint elements with the symmetrized multiplication.
Using the symmetrized ambient algebra keeps the associative multiplication separate. -/
def selfAdjointJordan : NonUnitalSubalgebra R Aˢʸᵐ :=
  let unsymₗ : Aˢʸᵐ →ₗ[R] A := { toFun := unsym, map_add' := unsym_add, map_smul' := unsym_smul }
  ((selfAdjoint.submodule R A).comap unsymₗ).toNonUnitalSubalgebra fun x y hx hy => by
    change IsSelfAdjoint (unsym x) at hx
    change IsSelfAdjoint (unsym y) at hy
    change IsSelfAdjoint (unsym (x * y))
    rw [unsym_mul]
    have h₂ : IsSelfAdjoint (2 : A) := by
      rw [← one_add_one_eq_two]
      exact (IsSelfAdjoint.one A).add (IsSelfAdjoint.one A)
    have hz : IsSelfAdjoint (unsym x * unsym y + unsym y * unsym x) := by
      simp only [isSelfAdjoint_iff, star_add, star_mul, hx.star_eq, hy.star_eq, add_comm]
    rw [isSelfAdjoint_iff, star_mul, hz.star_eq, h₂.invOf.star_eq]
    exact ((Nat.cast_commute 2 _).invOf_left).eq.symm

/-- Membership in the symmetrized subalgebra is self-adjointness in the original algebra. -/
@[simp] theorem mem_selfAdjointJordan {x : Aˢʸᵐ} :
    x ∈ selfAdjointJordan R A ↔ IsSelfAdjoint (unsym x) :=
  (Iff.rfl)

/-- The symmetrized self-adjoint subalgebra is unital, with the original algebra's unit. -/
instance : NonAssocCommRing (selfAdjointJordan R A) :=
  (selfAdjointJordan R A).nonAssocCommRingOfUnit
    ⟨1, (mem_selfAdjointJordan R A).mpr (by rw [unsym_one]; exact IsSelfAdjoint.one A)⟩
    (fun x => Subtype.ext (one_mul (x : Aˢʸᵐ)))

/-- The self-adjoint Jordan unit is the unit of the symmetrized algebra. -/
@[simp] theorem coe_one_selfAdjointJordan :
    ((1 : selfAdjointJordan R A) : Aˢʸᵐ) = 1 :=
  (rfl)

end SymAlg
