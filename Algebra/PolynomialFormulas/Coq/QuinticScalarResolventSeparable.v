From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0 abel.
From PolynomialFormulas Require Import
  QuinticThetaValues QuinticPaddedSymmetrization
  SexticRationalRootSearch QuinticRecursiveFactor QuinticGaloisAction
  QuinticCanonicalDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Separability of the scalar Frobenius--Dummit resolvent for the canonical
    roots of an irreducible quintic.

    The substantive input already proved by [QuinticCanonicalDecision] is
    injectivity of the six theta values.  Here we expose the short, reusable
    bridge from that theorem to [uniq] and then to MathComp's
    [separable_prod_XsubC].  The last two theorems transport separability
    through the exact scaled-resolvent coefficient identity. *)
Module PolynomialFormulasQuinticScalarResolventSeparable.

Import GRing.Theory.
Module TV := PolynomialFormulasQuinticThetaValues.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QGA := PolynomialFormulasQuinticGaloisAction.

Local Open Scope ring_scope.

Section CanonicalQuintic.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @QGA.quintic_root_tuple p p_size.

(** Pairwise distinctness of the six theta values, now packaged in the exact
    sequence form consumed by [separable_prod_XsubC]. *)
Theorem canonical_quintic_theta_values_uniq
    (p_irr : irreducible_poly p) :
  uniq (TV.quintic_theta_values roots).
Proof.
apply/tuple_uniqP=> i j hij.
apply: (@CD.canonical_quintic_theta_value_injective f p_irr i j).
by move: hij; rewrite !TV.tnth_quintic_theta_values.
Qed.

(** The scalar resolvent is a product of the six distinct linear factors. *)
Theorem canonical_quintic_scalar_resolvent_separable
    (p_irr : irreducible_poly p) :
  separable_poly (TV.quintic_scalar_resolvent roots).
Proof.
rewrite /TV.quintic_scalar_resolvent separable_prod_XsubC.
exact: canonical_quintic_theta_values_uniq p_irr.
Qed.

(** Separability after mapping the executable integer coefficient polynomial
    to the canonical splitting field.  The scale is nonzero by irreducibility
    and the already proved nonvanishing of all five canonical roots. *)
Theorem canonical_quintic_scaled_resolvent_mapped_separable
    (p_irr : irreducible_poly p) :
  separable_poly
    (map_poly (intr : int -> L)
      (RRS.coefficient_list_poly_int (QPS.quintic_scaled_resolvent f))).
Proof.
rewrite (@CD.quintic_scaled_resolvent_poly_correct L roots f
  (@CD.canonical_quintic_padded_vieta f)).
rewrite (eqp_separable
  (eqp_scale (TV.quintic_scalar_resolvent roots)
    (@CD.canonical_quintic_resolvent_scale_nonzero f p_irr))).
exact: canonical_quintic_scalar_resolvent_separable p_irr.
Qed.

(** The executable scaled resolvent is already separable over [rat], before
    extending coefficients to the canonical splitting field. *)
Theorem canonical_quintic_scaled_resolvent_rational_separable
    (p_irr : irreducible_poly p) :
  separable_poly
    (map_poly (intr : int -> rat)
      (RRS.coefficient_list_poly_int (QPS.quintic_scaled_resolvent f))).
Proof.
have hsep := canonical_quintic_scaled_resolvent_mapped_separable p_irr.
have hmap :
    map_poly ratrL
      (map_poly (intr : int -> rat)
        (RRS.coefficient_list_poly_int (QPS.quintic_scaled_resolvent f))) =
    map_poly (intr : int -> L)
      (RRS.coefficient_list_poly_int (QPS.quintic_scaled_resolvent f)).
  rewrite -map_poly_comp.
  apply: eq_map_poly=> z.
  by rewrite /= rmorph_int.
move: hsep.
by rewrite -hmap separable_map.
Qed.

End CanonicalQuintic.

End PolynomialFormulasQuinticScalarResolventSeparable.
