/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import TauCeti.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Pi

/-!
# Products of Jordan algebras

The Jordan identity and formal reality hold coordinatewise. In particular, the coordinatewise
multiplication on a finite product of real lines makes it a Euclidean Jordan algebra.

## Main results

* Products inherit the Jordan identity and formal reality from their factors.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Chapter II and Section III.1.
-/

public section

namespace Pi

variable {ι : Type*} {A : ι → Type*}

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

end Pi
