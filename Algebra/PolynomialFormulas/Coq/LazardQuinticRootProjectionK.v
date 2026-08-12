From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticFourier
  LazardQuinticProjection LazardQuinticRootProjections
  LazardQuinticRootProjectionJKCommon LazardQuinticRootProjectionKCore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Lazard's fourth raw root projection, assembled from the shared cyclic
    reduction and its isolated degree-ten coefficient certificate. *)
Module PolynomialFormulasLazardQuinticRootProjectionK.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootRadicals.
Import PolynomialFormulasLazardQuinticFourier.
Import PolynomialFormulasLazardQuinticProjection.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticRootProjectionJKCommon.
Import PolynomialFormulasLazardQuinticRootProjectionKCore.
Local Open Scope ring_scope.

Section RootProjectionK.

Variable F : fieldType.

(** Denominator-free form, valid in every characteristic in which a
    primitive fifth root exists. *)
Theorem lazard_root_standard_projection_K_scaled omega roots
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  2%:R *
    lazard_standard_projections (lazard_root_epsilon omega roots)
      (lazard_root_T omega roots) (lazard_root_formula_U omega roots)
      (lazard_root_fourier_fifth_orbit omega roots) p3 =
    25%:R * lazard_root_invariant_K
      (@lazard_depressed_of_roots F roots) (@lazard_root_invariants F roots).
Proof.
rewrite (lazard_root_standard_projection_K_as_cyclic roots omega_primitive).
have [h12 [h23 h34]] := lazard_cyclic_K_vector_tail_equal roots.
rewrite (lazard_cyclic_eval_equal_tail omega_primitive h12 h23 h34)
  lazard_cyclic_K_vector_difference.
transitivity (5%:R * (2%:R * lazard_root_K_component roots)).
- by rewrite !mulrA [2%:R * 5%:R]mulrC.
- rewrite (lazard_root_K_component_core hsum) mulrA.
  by rewrite -lazard_root_projection_twenty_five_natrE.
Qed.

(** Lean's [(25/2)K] normalization, with characteristic two excluded
    exactly where division by two is used. *)
Theorem lazard_root_standard_projection_K omega roots
    (two_neq0 : (2%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_standard_projections (lazard_root_epsilon omega roots)
      (lazard_root_T omega roots) (lazard_root_formula_U omega roots)
      (lazard_root_fourier_fifth_orbit omega roots) p3 =
    ((25%:R : F) / 2%:R) * lazard_root_invariant_K
      (@lazard_depressed_of_roots F roots) (@lazard_root_invariants F roots).
Proof.
apply: (mulfI two_neq0).
rewrite (lazard_root_standard_projection_K_scaled omega_primitive hsum).
rewrite mulrA [2%:R * ((25%:R : F) / 2%:R)]mulrC divfK //.
Qed.

End RootProjectionK.

End PolynomialFormulasLazardQuinticRootProjectionK.
