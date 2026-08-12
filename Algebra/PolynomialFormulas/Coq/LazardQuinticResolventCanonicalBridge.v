From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticChapman QuinticThetaValues
  QuinticGaloisAction QuinticThetaGaloisBridge QuinticRecursiveFactor
  QuinticPaddedSymmetrization SexticRationalRootSearch
  QuinticCanonicalDecision
  QuinticScalarResolventSeparable
  LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootBranchEquivariance
  LazardQuinticInvariantDescentF20
  LazardQuinticCanonicalEpsilonNonzero
  LazardQuinticRootOrdering
  LazardQuinticResolventPolynomial
  LazardQuinticResolventRootCertificate
  LazardQuinticExecutableScale LazardQuinticVieta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Exact canonical bridge between Lazard's displayed monic sextic and the
    scalar Frobenius--Dummit resolvent.

    The equality theorem is deliberately canonical and irreducible.  In that
    setting the already proved theta-injectivity theorem supplies six
    distinct roots.  We make no generic assertion that a product containing
    repeated theta values divides an arbitrary sextic merely because all its
    values are roots. *)
Module PolynomialFormulasLazardQuinticResolventCanonicalBridge.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module QF := PolynomialFormulasQuinticF20Data.
Module C := PolynomialFormulasQuinticChapman.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module TGB := PolynomialFormulasQuinticThetaGaloisBridge.
Module QS := PolynomialFormulasQuinticScalarResolventSeparable.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module RO := PolynomialFormulasLazardQuinticRootOrdering.
Module LR := PolynomialFormulasLazardQuinticResolventPolynomial.
Module RC := PolynomialFormulasLazardQuinticResolventRootCertificate.
Module ES := PolynomialFormulasLazardQuinticExecutableScale.
Module V := PolynomialFormulasLazardQuinticVieta.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Section RepresentativeCoefficients.

Variable F : fieldType.

Add Ring lazard_resolvent_representative_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_resolvent_representative_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The six chosen coset representatives merely reorder the elementary
    symmetric functions.  These four finite lemmas keep that bookkeeping
    separate from both the coefficient record and the theta-root proof. *)
Lemma lazard_representative_esymm2E
    (roots : 5.-tuple F) (i : 'I_6) :
  RP.lazard_root_esymm2
      (TV.permute_quintic_roots ((representative i)^-1) roots) =
    RP.lazard_root_esymm2 roots.
Proof.
rewrite /RP.lazard_root_esymm2
    !TV.tnth_permute_quintic_roots
    QF.representative_inv_o0E QF.representative_inv_o1E
    QF.representative_inv_o2E QF.representative_inv_o3
    QF.representative_inv_o4.
  case: i=> [[|[|[|[|[|[|j]]]]]]] hj; last by move: hj.
  all: rewrite /QF.representative_inv_o0_table
    /QF.representative_inv_o1_table
    /QF.representative_inv_o2_table /=.
  all: repeat rewrite (tnth_nth QF.o0).
  all: simpl.
  all: set x0 := tnth roots QF.o0;
    set x1 := tnth roots QF.o1;
    set x2 := tnth roots QF.o2;
    set x3 := tnth roots QF.o3;
    set x4 := tnth roots QF.o4;
    clearbody x0 x1 x2 x3 x4.
  all: try reflexivity.
  + rewrite [(x1 * x0)%R]mulrC [(x2 * x0)%R]mulrC.
    exact: (@GRing.add F).[ACl 2 * 5 * 8 * 9 * 1 * 3 * 4 * 6 * 7 * 10].
  + rewrite [(x2 * x0)%R]mulrC [(x2 * x1)%R]mulrC.
    exact: (@GRing.add F).[ACl 5 * 1 * 6 * 7 * 2 * 8 * 9 * 3 * 4 * 10].
  + rewrite [(x1 * x0)%R]mulrC.
    exact: (@GRing.add F).[ACl 1 * 5 * 6 * 7 * 2 * 3 * 4 * 8 * 9 * 10].
  + rewrite [(x2 * x1)%R]mulrC.
    exact: (@GRing.add F).[ACl 2 * 1 * 3 * 4 * 5 * 8 * 9 * 6 * 7 * 10].
  + rewrite [(x2 * x1)%R]mulrC [(x2 * x0)%R]mulrC
      [(x1 * x0)%R]mulrC.
    exact: (@GRing.add F).[ACl 5 * 2 * 8 * 9 * 1 * 6 * 7 * 3 * 4 * 10].
Qed.

Lemma lazard_representative_esymm3E
    (roots : 5.-tuple F) (i : 'I_6) :
  RP.lazard_root_esymm3
      (TV.permute_quintic_roots ((representative i)^-1) roots) =
    RP.lazard_root_esymm3 roots.
Proof.
rewrite /RP.lazard_root_esymm3
    !TV.tnth_permute_quintic_roots
    QF.representative_inv_o0E QF.representative_inv_o1E
    QF.representative_inv_o2E QF.representative_inv_o3
    QF.representative_inv_o4.
  case: i=> [[|[|[|[|[|[|j]]]]]]] hj; last by move: hj.
  all: rewrite /QF.representative_inv_o0_table
    /QF.representative_inv_o1_table
    /QF.representative_inv_o2_table /=.
  all: repeat rewrite (tnth_nth QF.o0).
  all: simpl.
  all: set y0 := tnth roots QF.o0;
    set y1 := tnth roots QF.o1;
    set y2 := tnth roots QF.o2;
    set y3 := tnth roots QF.o3;
    set y4 := tnth roots QF.o4;
    clearbody y0 y1 y2 y3 y4.
  all: try reflexivity.
  + rewrite [(y1 * y2 * y0)%R](@GRing.mul F).[ACl 3 * 1 * 2]
      [(y1 * y0 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y1 * y0 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y0 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y0 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3].
    exact: (@GRing.add F).[ACl 1 * 4 * 5 * 7 * 8 * 10 * 2 * 3 * 6 * 9].
  + rewrite [(y2 * y0 * y1)%R](@GRing.mul F).[ACl 2 * 3 * 1]
      [(y2 * y0 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y0 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y1 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y1 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3].
    exact: (@GRing.add F).[ACl 1 * 7 * 8 * 2 * 3 * 9 * 4 * 5 * 10 * 6].
  + rewrite [(y1 * y0 * y2)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y1 * y0 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y1 * y0 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3].
    exact: (@GRing.add F).[ACl 1 * 2 * 3 * 7 * 8 * 9 * 4 * 5 * 6 * 10].
  + rewrite [(y0 * y2 * y1)%R](@GRing.mul F).[ACl 1 * 3 * 2]
      [(y2 * y1 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y1 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3].
    exact: (@GRing.add F).[ACl 1 * 4 * 5 * 2 * 3 * 6 * 7 * 8 * 10 * 9].
  + rewrite [(y2 * y1 * y0)%R](@GRing.mul F).[ACl 3 * 2 * 1]
      [(y2 * y1 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y1 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y0 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y2 * y0 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y1 * y0 * y3)%R](@GRing.mul F).[ACl 2 * 1 * 3]
      [(y1 * y0 * y4)%R](@GRing.mul F).[ACl 2 * 1 * 3].
    exact: (@GRing.add F).[ACl 1 * 7 * 8 * 4 * 5 * 10 * 2 * 3 * 9 * 6].
Qed.

Lemma lazard_representative_esymm4E
    (roots : 5.-tuple F) (i : 'I_6) :
  RP.lazard_root_esymm4
      (TV.permute_quintic_roots ((representative i)^-1) roots) =
    RP.lazard_root_esymm4 roots.
Proof.
rewrite /RP.lazard_root_esymm4
    !TV.tnth_permute_quintic_roots
    QF.representative_inv_o0E QF.representative_inv_o1E
    QF.representative_inv_o2E QF.representative_inv_o3
    QF.representative_inv_o4.
  case: i=> [[|[|[|[|[|[|j]]]]]]] hj; last by move: hj.
  all: rewrite /QF.representative_inv_o0_table
    /QF.representative_inv_o1_table
    /QF.representative_inv_o2_table /=.
  all: repeat rewrite (tnth_nth QF.o0).
  all: simpl.
  all: set z0 := tnth roots QF.o0;
    set z1 := tnth roots QF.o1;
    set z2 := tnth roots QF.o2;
    set z3 := tnth roots QF.o3;
    set z4 := tnth roots QF.o4;
    clearbody z0 z1 z2 z3 z4.
  all: try reflexivity.
  + rewrite [(z1 * z2 * z0 * z3)%R]
      (@GRing.mul F).[ACl 3 * 1 * 2 * 4]
      [(z1 * z2 * z0 * z4)%R]
      (@GRing.mul F).[ACl 3 * 1 * 2 * 4]
      [(z1 * z0 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4]
      [(z2 * z0 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4].
    exact: (@GRing.add F).[ACl 1 * 2 * 4 * 5 * 3].
  + rewrite [(z2 * z0 * z1 * z3)%R]
      (@GRing.mul F).[ACl 2 * 3 * 1 * 4]
      [(z2 * z0 * z1 * z4)%R]
      (@GRing.mul F).[ACl 2 * 3 * 1 * 4]
      [(z2 * z0 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4]
      [(z2 * z1 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4].
    exact: (@GRing.add F).[ACl 1 * 2 * 5 * 3 * 4].
  + rewrite [(z1 * z0 * z2 * z3)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4]
      [(z1 * z0 * z2 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4]
      [(z1 * z0 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4].
    exact: (@GRing.add F).[ACl 1 * 2 * 3 * 5 * 4].
  + rewrite [(z0 * z2 * z1 * z3)%R]
      (@GRing.mul F).[ACl 1 * 3 * 2 * 4]
      [(z0 * z2 * z1 * z4)%R]
      (@GRing.mul F).[ACl 1 * 3 * 2 * 4]
      [(z2 * z1 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4].
    exact: (@GRing.add F).[ACl 1 * 2 * 4 * 3 * 5].
  + rewrite [(z2 * z1 * z0 * z3)%R]
      (@GRing.mul F).[ACl 3 * 2 * 1 * 4]
      [(z2 * z1 * z0 * z4)%R]
      (@GRing.mul F).[ACl 3 * 2 * 1 * 4]
      [(z2 * z1 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4]
      [(z2 * z0 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4]
      [(z1 * z0 * z3 * z4)%R]
      (@GRing.mul F).[ACl 2 * 1 * 3 * 4].
    exact: (@GRing.add F).[ACl 1 * 2 * 5 * 4 * 3].
Qed.

Lemma lazard_representative_esymm5E
    (roots : 5.-tuple F) (i : 'I_6) :
  RP.lazard_root_esymm5
      (TV.permute_quintic_roots ((representative i)^-1) roots) =
    RP.lazard_root_esymm5 roots.
Proof.
rewrite /RP.lazard_root_esymm5
    !TV.tnth_permute_quintic_roots
    QF.representative_inv_o0E QF.representative_inv_o1E
    QF.representative_inv_o2E QF.representative_inv_o3
    QF.representative_inv_o4.
  case: i=> [[|[|[|[|[|[|j]]]]]]] hj; last by move: hj.
  all: rewrite /QF.representative_inv_o0_table
    /QF.representative_inv_o1_table
    /QF.representative_inv_o2_table /=.
  all: repeat rewrite (tnth_nth QF.o0).
  all: simpl.
  all: set w0 := tnth roots QF.o0;
    set w1 := tnth roots QF.o1;
    set w2 := tnth roots QF.o2;
    set w3 := tnth roots QF.o3;
    set w4 := tnth roots QF.o4;
    clearbody w0 w1 w2 w3 w4.
  all: try reflexivity.
  + exact: (@GRing.mul F).[ACl 3 * 1 * 2 * 4 * 5].
  + exact: (@GRing.mul F).[ACl 2 * 3 * 1 * 4 * 5].
  + exact: (@GRing.mul F).[ACl 2 * 1 * 3 * 4 * 5].
  + exact: (@GRing.mul F).[ACl 1 * 3 * 2 * 4 * 5].
  + exact: (@GRing.mul F).[ACl 3 * 2 * 1 * 4 * 5].
Qed.

(** The coefficient record is invariant because each of its four fields is
    one of the separately proved finite symmetric expressions. *)
Lemma lazard_representative_depressed_coefficientsE
    (roots : 5.-tuple F) (i : 'I_6) :
  RP.lazard_depressed_of_roots
      (TV.permute_quintic_roots ((representative i)^-1) roots) =
    RP.lazard_depressed_of_roots roots.
Proof.
apply: BE.lazard_depressed_coefficients_ext=> /=.
- exact: lazard_representative_esymm2E roots i.
- by rewrite lazard_representative_esymm3E.
- exact: lazard_representative_esymm4E roots i.
- by rewrite lazard_representative_esymm5E.
Qed.

(** The [i4] of the selected ordering is exactly its indexed theta value. *)
Lemma lazard_representative_i4E (roots : 5.-tuple F) (i : 'I_6) :
  RP.lazard_root_i4
      (RP.lazard_root_invariants
        (TV.permute_quintic_roots ((representative i)^-1) roots)) =
    TV.quintic_theta_value roots i.
Proof.
rewrite RO.lazard_root_i4_theta_formulaE.
exact: esym (C.quintic_theta_value_formulaE roots i).
Qed.

End RepresentativeCoefficients.

Section CanonicalBridge.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

Lemma lazard_canonical_two_neq0 : (2%:R : L) != 0.
Proof.
by rewrite -[2%:R](rmorph_nat (char0_ratr (char_numfield p)) 2) fmorph_eq0.
Qed.

(** Every one of the six canonical theta values is a root of the literal
    displayed Lazard polynomial. *)
Theorem canonical_lazard_theta_value_root
    (hdepressed : CE.lazard_canonical_quintic_depressed f)
    (i : 'I_6) :
  root
    (LR.lazard_resolvent_polynomial
      (RP.lazard_depressed_of_roots roots))
    (TV.quintic_theta_value roots i).
Proof.
rewrite -(@lazard_representative_i4E L roots i).
rewrite -(@lazard_representative_depressed_coefficientsE L roots i).
apply: RC.lazard_resolvent_root_i4.
- exact: CE.lazard_selected_root_esymm1_zero hdepressed i.
- exact: lazard_canonical_two_neq0.
Qed.

(** Distinctness is used exactly here, to retain all six linear factors in
    the divisibility statement. *)
Theorem canonical_quintic_scalar_resolvent_dvd_lazard
    (p_irr : irreducible_poly p)
    (hdepressed : CE.lazard_canonical_quintic_depressed f) :
  TV.quintic_scalar_resolvent roots %|
    LR.lazard_resolvent_polynomial
      (RP.lazard_depressed_of_roots roots).
Proof.
rewrite /TV.quintic_scalar_resolvent.
apply: uniq_roots_dvdp.
- apply/allP=> z hz.
  move/tnthP: hz=> [i ->].
  rewrite TV.tnth_quintic_theta_values.
  exact: canonical_lazard_theta_value_root hdepressed i.
- by rewrite uniq_rootsE; exact: QS.canonical_quintic_theta_values_uniq p_irr.
Qed.

(** Exact monic equality, not equality only up to the executable homogeneous
    scale. *)
Theorem canonical_quintic_scalar_resolvent_eq_lazard
    (p_irr : irreducible_poly p)
    (hdepressed : CE.lazard_canonical_quintic_depressed f) :
  TV.quintic_scalar_resolvent roots =
    LR.lazard_resolvent_polynomial
      (RP.lazard_depressed_of_roots roots).
Proof.
have hdiv := canonical_quintic_scalar_resolvent_dvd_lazard
  p_irr hdepressed.
apply/eqP.
rewrite -eqp_monic ?TV.quintic_scalar_resolvent_monic
  ?RC.lazard_resolvent_polynomial_monic //.
rewrite -(dvdp_size_eqp hdiv).
by rewrite TV.size_quintic_scalar_resolvent
  RC.lazard_resolvent_polynomial_size.
Qed.

Corollary canonical_lazard_resolvent_eq_scalar
    (p_irr : irreducible_poly p)
    (hdepressed : CE.lazard_canonical_quintic_depressed f) :
  LR.lazard_resolvent_polynomial
      (RP.lazard_depressed_of_roots roots) =
    TV.quintic_scalar_resolvent roots.
Proof. exact: esym (canonical_quintic_scalar_resolvent_eq_lazard
  p_irr hdepressed). Qed.

(** The literal, unscaled Lazard sextic is separable in the canonical
    irreducible depressed scope.  This is a named conclusion about Lazard's
    displayed polynomial itself, rather than an equality silently consumed
    inside a later determinant proof. *)
Theorem canonical_lazard_resolvent_separable
    (p_irr : irreducible_poly p)
    (hdepressed : CE.lazard_canonical_quintic_depressed f) :
  separable_poly
    (LR.lazard_resolvent_polynomial
      (RP.lazard_depressed_of_roots roots)).
Proof.
rewrite (canonical_lazard_resolvent_eq_scalar p_irr hdepressed).
exact: QS.canonical_quintic_scalar_resolvent_separable p_irr.
Qed.

(** Paper-facing composition of the exact displayed-polynomial identity with
    the F20/Galois criterion.  Injectivity of the six theta values and hence
    resolvent separability are derived from irreducibility; neither is a
    premise of this theorem.  "Rational root" means a root [in_alg L q] for
    an actual [q : rat] in the canonical splitting field. *)
Theorem canonical_lazard_resolvent_has_rational_root_iff_galois_solvable
    (p_irr : irreducible_poly p)
    (hdepressed : CE.lazard_canonical_quintic_depressed f) :
  ((exists q : rat,
      root
        (LR.lazard_resolvent_polynomial
          (RP.lazard_depressed_of_roots roots))
        (in_alg L q)) <->
    solvable 'Gal({:L} / 1%AS)).
Proof.
rewrite (canonical_lazard_resolvent_eq_scalar p_irr hdepressed).
exact: (@TGB.quintic_scalar_resolvent_has_rational_root_iff_galois_solvable
  p p_size p_irr (CD.canonical_quintic_theta_value_injective p_irr)).
Qed.

(** Irreducibility also proves that the depressed constant coefficient, and
    hence the executable homogeneous scale, cannot vanish. *)
Theorem canonical_lazard_depressed_s_neq0
    (p_irr : irreducible_poly p) :
  RP.lazard_root_s (RP.lazard_depressed_of_roots roots) != 0.
Proof.
rewrite /RP.lazard_depressed_of_roots /= oppr_eq0
  /RP.lazard_root_esymm5.
have hproduct := CD.canonical_quintic_root_product_nonzero p_irr.
rewrite ES.lazard_five_tuple_productE
  /V.lazard_five_esymm5 in hproduct.
exact: hproduct.
Qed.

(** End-to-end coefficient identity for the executable integral polynomial:
    its only difference from Lazard's displayed monic sextic is the explicit
    nonzero scalar [-(120*s)]. *)
Theorem canonical_quintic_executable_resolvent_eq_lazard_scale
    (p_irr : irreducible_poly p)
    (hdepressed : CE.lazard_canonical_quintic_depressed f) :
  map_poly (intr : int -> L)
      (RRS.coefficient_list_poly_int
        (QPS.quintic_scaled_resolvent f)) =
    ((- (120%:R *
      RP.lazard_root_s (RP.lazard_depressed_of_roots roots))) *:
      LR.lazard_resolvent_polynomial
        (RP.lazard_depressed_of_roots roots))%R.
Proof.
rewrite (@CD.quintic_scaled_resolvent_poly_correct L roots f
  (@CD.canonical_quintic_padded_vieta f)).
rewrite ES.lazard_five_tuple_productE
  /V.lazard_five_esymm5
  (canonical_quintic_scalar_resolvent_eq_lazard p_irr hdepressed).
by rewrite /RP.lazard_depressed_of_roots /= mulrN opprK.
Qed.

End CanonicalBridge.

Print Assumptions canonical_lazard_theta_value_root.
Print Assumptions canonical_quintic_scalar_resolvent_eq_lazard.
Print Assumptions canonical_lazard_resolvent_separable.
Print Assumptions
  canonical_lazard_resolvent_has_rational_root_iff_galois_solvable.
Print Assumptions canonical_lazard_depressed_s_neq0.
Print Assumptions canonical_quintic_executable_resolvent_eq_lazard_scale.

End PolynomialFormulasLazardQuinticResolventCanonicalBridge.
