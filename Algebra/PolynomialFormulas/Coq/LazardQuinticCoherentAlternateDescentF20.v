From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction
  QuinticRecursiveFactor QuinticCanonicalDecision
  LazardQuinticInvariantDescentF20
  LazardQuinticRootAlternateRecovery
  LazardQuinticRootCoherentAlternateInvariantF20.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Concrete same-field specialization of corrected alternate descent.

    If the quintic splitting field already contains a primitive fifth root,
    the canonical rational-resolvent ordering supplies the complete root
    action needed by the generic fixed-field theorem.  The general Lazard
    construction instead works in the compositum with the fifth-cyclotomic
    field; keeping this specialization separate makes that remaining
    compositum transport explicit. *)
Module PolynomialFormulasLazardQuinticCoherentAlternateDescentF20.

Import GRing.Theory Num.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module RA := PolynomialFormulasLazardQuinticRootAlternateRecovery.
Module CAI :=
  PolynomialFormulasLazardQuinticRootCoherentAlternateInvariantF20.

Section CanonicalSelectedRoots.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

(** All root-action premises of the generic descent theorem are derived
    from the canonical selected ordering. *)
Theorem lazard_selected_coherent_alternate_value_mem_prime_field
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (omega : L) (omega_primitive : 5.-primitive_root omega)
    (j : 'I_4) :
  RA.lazard_root_coherent_alternate_projection_values
      omega (ID.lazard_selected_roots i) j \in (1%AS : {subfield L}).
Proof.
apply: (@CAI.lazard_root_coherent_alternate_projection_value_mem_base
  rat L (1%AS : {subfield L}) omega (ID.lazard_selected_roots i)
  omega_primitive (galois_numfield p) _ j).
move=> g _.
exists ((@GA.quintic_gal_perm p p_size g) ^ representative i).
split.
- exact: ID.lazard_selected_gal_perm_mem_standard_F20 p_irr hi g.
- exact: ID.lazard_selected_roots_gal i g.
Qed.

(** Equivalent rational-value form in the canonical embedding. *)
Theorem exists_rational_selected_coherent_alternate_value
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (omega : L) (omega_primitive : 5.-primitive_root omega)
    (j : 'I_4) :
  exists a : rat,
    RA.lazard_root_coherent_alternate_projection_values
        omega (ID.lazard_selected_roots i) j = ratrL a.
Proof.
apply: ID.lazard_numfield_fixed_is_rational=> g hg.
exact: fixed_gal (sub1v fullv) hg
  (lazard_selected_coherent_alternate_value_mem_prime_field
    p_irr hi omega_primitive j).
Qed.

End CanonicalSelectedRoots.

Print Assumptions
  lazard_selected_coherent_alternate_value_mem_prime_field.
Print Assumptions exists_rational_selected_coherent_alternate_value.

End PolynomialFormulasLazardQuinticCoherentAlternateDescentF20.
