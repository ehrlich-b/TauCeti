/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.LinearAlgebra.Pi
public import TauCeti.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Pi

/-!
# Products of Jordan algebras

The Jordan identity and formal reality hold coordinatewise. In particular, the coordinatewise
multiplication on a finite product of real lines makes it a Euclidean Jordan algebra.

## Main results

* Products inherit the commutative nonassociative ring structure, the Jordan identity,
  and formal reality from their factors.
* Coordinate projections and single-coordinate inclusions are multiplicative linear maps.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Chapter II and Section III.1.
-/

public section

namespace Pi

variable {ι : Type*} {A : ι → Type*}

/-- A product of commutative nonassociative rings has the pointwise ring structure. -/
instance instNonAssocCommRingPi [∀ i, NonAssocCommRing (A i)] :
    NonAssocCommRing (∀ i, A i) where
  __ := (inferInstance : NonAssocRing (∀ i, A i))
  mul_comm x y := funext fun i => mul_comm (x i) (y i)

/-- The Jordan identity holds coordinatewise in a product. -/
instance [∀ i, CommMagma (A i)] [∀ i, IsCommJordan (A i)] :
    IsCommJordan (∀ i, A i) where
  lmul_comm_rmul_rmul x y := funext fun i => IsCommJordan.lmul_comm_rmul_rmul (x i) (y i)

/-- The product of formally real algebras is formally real. -/
instance [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, IsFormallyReal (A i)] :
    IsFormallyReal (∀ i, A i) :=
  .of_eq_zero_of_eq_zero_of_mul_self_add fun {s a} hs h => by
    have eval {s : ∀ i, A i} (hs : IsSumSq s) (i : ι) : IsSumSq (s i) := by
      induction hs with
      | zero => exact .zero
      | sq_add a _ ih => exact .sq_add (a i) ih
    ext i
    exact IsFormallyReal.eq_zero_of_mul_self_eq_zero
      (IsFormallyReal.eq_zero_of_add_right (.mul_self (a i)) (eval hs i)
        (congrFun h i))

section CoordinateMaps

variable {R : Type*} [Semiring R] [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, Module R (A i)]

/-- Evaluation at a coordinate preserves multiplication and scalar multiplication. -/
def evalNonUnitalAlgHom (i : ι) : (∀ j, A j) →ₙₐ[R] A i where
  __ := evalNonUnitalRingHom A i
  map_smul' _ _ := rfl

/-- Inclusion at a coordinate, with zero in all other coordinates. -/
def singleNonUnitalAlgHom [DecidableEq ι] (i : ι) : A i →ₙₐ[R] (∀ j, A j) where
  toFun := Pi.single i
  map_zero' := (LinearMap.single R A i).map_zero
  map_add' := (LinearMap.single R A i).map_add
  map_smul' := (LinearMap.single R A i).map_smul
  map_mul' x y := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne h]

/-- Evaluating the projection gives the specified coordinate. -/
@[simp] theorem evalNonUnitalAlgHom_apply (i : ι) (x : ∀ j, A j) :
    evalNonUnitalAlgHom (R := R) i x = x i :=
  (rfl)

/-- The inclusion gives a dependent function supported at one coordinate. -/
@[simp] theorem singleNonUnitalAlgHom_apply [DecidableEq ι] (i : ι) (x : A i) :
    singleNonUnitalAlgHom (R := R) i x = Pi.single i x :=
  (rfl)

end CoordinateMaps

end Pi
