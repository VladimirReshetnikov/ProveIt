From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticRootInvariantRelationsProductsCore
  LazardQuinticRootInvariantRelationsProductI5
  LazardQuinticRootInvariantRelationsProductI6
  LazardQuinticRootInvariantRelationsProductI7
  LazardQuinticRootInvariantRelationsProductI8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Proof-light assembly of the four independently checked Figure-2 product
    identities into their public record. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationsProducts.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module PC := PolynomialFormulasLazardQuinticRootInvariantRelationsProductsCore.
Module P5 := PolynomialFormulasLazardQuinticRootInvariantRelationsProductI5.
Module P6 := PolynomialFormulasLazardQuinticRootInvariantRelationsProductI6.
Module P7 := PolynomialFormulasLazardQuinticRootInvariantRelationsProductI7.
Module P8 := PolynomialFormulasLazardQuinticRootInvariantRelationsProductI8.
Local Open Scope ring_scope.

Section Products.

Variable F : fieldType.

Theorem lazard_root_invariant_product_relations
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  PC.lazard_invariant_product_relations
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).
Proof.
constructor.
- exact: P5.lazard_root_invariant_product_i5 hsum.
- exact: P6.lazard_root_invariant_product_i6 hsum.
- exact: P7.lazard_root_invariant_product_i7 hsum.
- exact: P8.lazard_root_invariant_product_i8 hsum.
Qed.

End Products.

End PolynomialFormulasLazardQuinticRootInvariantRelationsProducts.
