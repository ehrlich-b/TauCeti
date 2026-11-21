/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Scalar compatibility with commutative multiplication

Commutativity lets a scalar action that commutes with multiplication in the right argument
associate with multiplication in the left argument.

## Main results

* `IsScalarTower.of_commMagma`: derive scalar compatibility on the left without associativity
  or a unit for multiplication.

## References

* Mathlib's `IsScalarTower.of_commMonoid` for associative unital multiplication.
-/

public section

/-- In a commutative magma, compatibility of scalar multiplication with right factors also
gives compatibility with left factors. -/
theorem IsScalarTower.of_commMagma (R J : Type*) [CommMagma J] [SMul R J]
    [SMulCommClass R J J] : IsScalarTower R J J where
  smul_assoc r x y := by
    -- The self-action of a magma is left multiplication.
    change (r • x) * y = r • (x * y)
    rw [mul_comm (r • x) y, mul_smul_comm, mul_comm y x]
