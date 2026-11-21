/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Jordan subalgebras

Mathlib's nonunital subalgebras model product-closed submodules. A subalgebra inherits the Jordan
identity and formal reality, and can have its own unit, as in the Peirce spaces.

## Main results

* Every product-closed submodule of a Jordan algebra inherits the Jordan identity.
* `NonUnitalSubalgebra.nonAssocCommRingOfUnit` equips such a submodule with its own unit.
* Formal reality and finite dimensionality descend to subalgebras.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Chapter II and Proposition IV.1.1.
* Bryan Ehrlich, euclidean-jordan, `EuclideanJordan/PeirceSubalgebra.lean` at a83407e4
  (https://github.com/ehrlich-b/euclidean-jordan).
-/

public section

namespace NonUnitalSubalgebra

variable {R A : Type*} [CommRing R]

section CommRing

variable [NonUnitalNonAssocCommRing A] [Module R A]

/-- A product-closed submodule inherits commutative nonassociative multiplication. -/
instance (S : NonUnitalSubalgebra R A) : NonUnitalNonAssocCommRing S where
  __ := (inferInstance : NonUnitalNonAssocRing S)
  mul_comm x y := Subtype.ext (mul_comm (x : A) (y : A))

/-- A product-closed submodule inherits the Jordan identity. -/
instance [IsCommJordan A] (S : NonUnitalSubalgebra R A) : IsCommJordan S where
  lmul_comm_rmul_rmul x y :=
    Subtype.ext (IsCommJordan.lmul_comm_rmul_rmul (x : A) (y : A))

/-- The induced ring on a subalgebra equipped with an internal multiplicative unit.
The addition, multiplication and scalar action retain their usual subtype definitions. -/
@[expose, instance_reducible]
def nonAssocCommRingOfUnit (S : NonUnitalSubalgebra R A) (e : S)
    (he : ∀ x : S, e * x = x) : NonAssocCommRing S where
  __ := (inferInstance : NonUnitalNonAssocCommRing S)
  one := e
  one_mul := he
  mul_one x := (mul_comm x e).trans (he x)

end CommRing

/-- Formal reality is inherited by product-closed submodules. -/
instance [NonUnitalNonAssocRing A] [Module R A] [IsFormallyReal A]
    (S : NonUnitalSubalgebra R A) : IsFormallyReal S where
  not_isSumNonzeroSq_zero h := by
    suffices ∀ s : S, IsSumNonzeroSq s → IsSumNonzeroSq (s : A) from
      IsFormallyReal.not_isSumNonzeroSq_zero (this 0 h)
    intro s hs
    induction hs with
    | sq ha =>
      exact .sq (fun h => ha (Subtype.ext h))
    | sq_add ha _ ih =>
      exact .sq_add (fun h => ha (Subtype.ext h)) ih

/-- A product-closed submodule of a finite-dimensional vector space is finite-dimensional. -/
instance {K : Type*} [Field K] [NonUnitalNonAssocRing A]
    [Module K A] [Module.Finite K A] (S : NonUnitalSubalgebra K A) : Module.Finite K S :=
  Module.Finite.of_injective S.toSubmodule.subtype (fun _ _ h => Subtype.ext h)

end NonUnitalSubalgebra
