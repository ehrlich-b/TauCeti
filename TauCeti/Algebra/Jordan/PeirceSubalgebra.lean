/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.Jordan.Peirce
public import TauCeti.Algebra.Jordan.Subalgebra

/-!
# Unital Peirce subalgebras

The Peirce `1`- and `0`-spaces at an idempotent are closed under multiplication. They are
unital with units the idempotent and its complement. A smaller idempotent has its own
Peirce `1`-space inside that of the larger idempotent.

## Main results

* `peirceOneSubalgebra` and `peirceZeroSubalgebra`: the two unital Peirce subalgebras.
* `peirceSpace_one_le_of_mul_eq_self`: inclusion of the spaces of comparable idempotents.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Proposition IV.1.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/PeirceSubalgebra.lean` and
  `EuclideanJordan/FrameExists.lean` at a83407e4 (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace TauCeti.Jordan

variable {R J : Type*} [CommRing R] [NonUnitalNonAssocCommRing J] [Module R J]
  [SMulCommClass R J J]

variable [Invertible (2 : R)] [IsCommJordan J]

/-- The Peirce `1`-space as a product-closed submodule. -/
@[expose]
def peirceOneSubalgebra {c : J} (hc : IsIdempotentElem c) : NonUnitalSubalgebra R J :=
  (peirceSpace R c 1).toNonUnitalSubalgebra fun _ _ hx hy =>
    mul_mem_peirceSpace_of_mem_one hc.eq hx hy

/-- The Peirce `0`-space as a product-closed submodule. -/
@[expose]
def peirceZeroSubalgebra {c : J} (hc : IsIdempotentElem c) : NonUnitalSubalgebra R J :=
  (peirceSpace R c 0).toNonUnitalSubalgebra fun _ _ hx hy =>
    mul_mem_peirceSpace_of_mem_zero hc.eq hx hy

/-- The Peirce `1`-space is a unital ring with the idempotent as its unit. -/
instance {c : J} (hc : IsIdempotentElem c) : NonAssocCommRing (peirceOneSubalgebra (R := R) hc) :=
  (peirceOneSubalgebra (R := R) hc).nonAssocCommRingOfUnit
    ⟨c, mem_peirceSpace.mpr (by simpa using hc.eq)⟩
    (fun x => Subtype.ext (by simpa using mem_peirceSpace.mp x.property))

/-- The unit of the Peirce `1`-space is the original idempotent. -/
@[simp] theorem coe_one_peirceOneSubalgebra {c : J} (hc : IsIdempotentElem c) :
    ((1 : peirceOneSubalgebra (R := R) hc) : J) = c := by
  exact rfl

/-- If an idempotent is fixed by left multiplication by `c`, its Peirce `1`-space
is contained in the Peirce `1`-space of `c`. -/
theorem peirceSpace_one_le_of_mul_eq_self {c d : J} (hd : IsIdempotentElem d) (hcd : c * d = d) :
    peirceSpace R d 1 ≤ peirceSpace R c 1 := by
  intro x hx
  have hdx : d * x = x := by simpa using mem_peirceSpace.mp hx
  have hzero : c - d ∈ peirceSpace R d 0 := by
    apply mem_peirceSpace.mpr
    rw [mul_sub, mul_comm d c, hcd, hd.eq, sub_self, zero_smul]
  have h := mul_eq_zero_of_mem_peirceSpace_one_of_mem_peirceSpace_zero hd.eq hx hzero
  rw [mul_sub, mul_comm x c, mul_comm x d, hdx, sub_eq_zero] at h
  exact mem_peirceSpace.mpr (by simpa using h)

section Unital

variable {A : Type*} [NonAssocCommRing A] [Module R A] [SMulCommClass R A A]

omit [Invertible (2 : R)] in
/-- The `1`-space of an element's complement is its `0`-space. -/
theorem peirceSpace_one_sub_one (c : A) : peirceSpace R (1 - c) 1 = peirceSpace R c 0 := by
  ext x
  simp [mem_peirceSpace, sub_mul, sub_eq_self]

variable [IsCommJordan A]

/-- The Peirce `0`-space is a unital ring with the complementary idempotent as unit. -/
instance {c : A} (hc : IsIdempotentElem c) :
    NonAssocCommRing (peirceZeroSubalgebra (R := R) hc) :=
  (peirceZeroSubalgebra (R := R) hc).nonAssocCommRingOfUnit
    ⟨1 - c, mem_peirceSpace.mpr (by rw [mul_sub, mul_one, hc.eq, sub_self, zero_smul])⟩
    (fun x => Subtype.ext (by
      have hx : c * (x : A) = 0 := by simpa using mem_peirceSpace.mp x.property
      simp [sub_mul, hx]))

/-- The unit of the Peirce `0`-space is the complementary idempotent. -/
@[simp] theorem coe_one_peirceZeroSubalgebra {c : A} (hc : IsIdempotentElem c) :
    ((1 : peirceZeroSubalgebra (R := R) hc) : A) = 1 - c := by
  exact rfl

end Unital

end TauCeti.Jordan
