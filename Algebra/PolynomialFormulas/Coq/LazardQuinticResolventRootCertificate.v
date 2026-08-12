From Stdlib Require Import Lia.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticCayleyTranslation
  LazardQuinticResolventPolynomial
  LazardQuinticResolventRootCertificateKernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Cheap assembly layer over the separately cached root-factor
    certificates. *)
Module PolynomialFormulasLazardQuinticResolventRootCertificate.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module CT := PolynomialFormulasLazardQuinticCayleyTranslation.
Module LR := PolynomialFormulasLazardQuinticResolventPolynomial.
Module RF :=
  PolynomialFormulasLazardQuinticResolventRootCertificateKernel.
Local Open Scope ring_scope.

Section RootCertificate.

Variable F : fieldType.

Lemma lazard_resolvent_square_product (a d : F) :
  a ^+ 2 * d ^+ 2 = (a * d) ^+ 2.
Proof.
rewrite !expr2 !mulrA.
by rewrite [a * d * a]mulrAC.
Qed.

(** Cayley's fraction-free identity at the ten-term root invariant [i4].
    This is the substantive algebraic certificate that each such [i4] is a
    root of the displayed Lazard sextic. *)
Theorem lazard_resolvent_root_fraction_free_identity
    (roots : 5.-tuple F)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  LR.lazard_resolvent_cayley_theta
      (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_i4 (RP.lazard_root_invariants roots)) *
    LR.lazard_resolvent_discriminant
      (RP.lazard_depressed_of_roots roots) =
  LR.lazard_resolvent_core
      (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_i4 (RP.lazard_root_invariants roots)) ^+ 2.
Proof.
have htheta := CT.lazard_root_cayley_theta_depressedE hsum.
rewrite /CT.lazard_root_cayley_theta /CT.lazard_cayley_theta
  /LR.lazard_resolvent_cayley_theta in htheta.
rewrite /LR.lazard_resolvent_cayley_theta.
rewrite -htheta
  (RF.lazard_resolvent_discriminant_root_factor hsum)
  (RF.lazard_resolvent_core_root_factor hsum).
exact: lazard_resolvent_square_product.
Qed.

(** Polynomial form of the preceding certificate.  Only the harmless
    characteristic restriction [2 != 0], already needed by the monic
    half-core normalization, remains explicit. *)
Theorem lazard_resolvent_root_i4
    (roots : 5.-tuple F)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (two_neq0 : (2%:R : F) != 0) :
  root
    (LR.lazard_resolvent_polynomial
      (RP.lazard_depressed_of_roots roots))
    (RP.lazard_root_i4 (RP.lazard_root_invariants roots)).
Proof.
apply/rootP.
rewrite (LR.lazard_resolvent_polynomial_horner
  (RP.lazard_depressed_of_roots roots)
  (RP.lazard_root_i4 (RP.lazard_root_invariants roots))
  two_neq0).
apply: (proj2 (LR.lazard_resolvent_eval_eq0_iff
  (RP.lazard_depressed_of_roots roots)
  (RP.lazard_root_i4 (RP.lazard_root_invariants roots))
  two_neq0)).
exact: lazard_resolvent_root_fraction_free_identity hsum.
Qed.

(** Small degree lemmas used to compare the displayed sextic with the
    six-factor scalar resolvent. *)
Lemma lazard_resolvent_size_add_degree
    (p q : {poly F}) (n : nat) :
  leq (size p) n.+1 -> leq (size q) n.+1 ->
  leq (size (p + q)) n.+1.
Proof.
move=> hp hq.
apply: leq_trans (size_polyD p q) _.
by rewrite geq_max hp hq.
Qed.

Lemma lazard_resolvent_size_mul_degree
    (p q : {poly F}) (dp dq : nat) :
  leq (size p) dp.+1 -> leq (size q) dq.+1 ->
  leq (size (p * q)) (dp + dq).+1.
Proof.
move=> hp hq.
apply: leq_trans (size_polyMleq p q) _.
have hsum := leq_add hp hq.
have hpred := leq_sub2r 1 hsum.
move: hpred.
by rewrite !subn1 addSn addnS.
Qed.

Lemma lazard_resolvent_cubic_tail_size
    (c : RP.LazardDepressedRootCoefficients F) :
  leq (size
    ((LR.lazard_resolvent_cubic_a c)%:P * 'X ^+ 2 + (
      (LR.lazard_resolvent_cubic_b c)%:P * 'X +
      (LR.lazard_resolvent_cubic_g c)%:P))) 3.
Proof.
apply: lazard_resolvent_size_add_degree.
- apply: (lazard_resolvent_size_mul_degree
    (dp := 0%N) (dq := 2%N)).
  + exact: size_polyC_leq1.
  + by rewrite size_polyXn.
- apply: lazard_resolvent_size_add_degree.
  + have hb :
      leq (size ((LR.lazard_resolvent_cubic_b c)%:P * 'X)) 2.
    apply: (lazard_resolvent_size_mul_degree
      (dp := 0%N) (dq := 1%N)).
    * exact: size_polyC_leq1.
    * by rewrite size_polyX.
    exact: leq_trans hb (leqnSn 2).
  + exact: leq_trans (size_polyC_leq1 _)
      (leq_trans (leqnSn 1) (leqnSn 2)).
Qed.

Lemma lazard_resolvent_cubic_size
    (c : RP.LazardDepressedRootCoefficients F) :
  size (LR.lazard_resolvent_cubic c) = 4%N.
Proof.
rewrite /LR.lazard_resolvent_cubic -!addrA.
have hdom :
    ltn (size
        ((LR.lazard_resolvent_cubic_a c)%:P * 'X ^+ 2 + (
          (LR.lazard_resolvent_cubic_b c)%:P * 'X +
          (LR.lazard_resolvent_cubic_g c)%:P)))
      (size ('X ^+ 3 : {poly F})).
  rewrite size_polyXn.
  exact: leq_ltn_trans (lazard_resolvent_cubic_tail_size c) (ltnSn 3).
by rewrite (size_polyDl hdom) size_polyXn.
Qed.

Lemma lazard_resolvent_cubic_monic
    (c : RP.LazardDepressedRootCoefficients F) :
  LR.lazard_resolvent_cubic c \is monic.
Proof.
apply/monicP.
rewrite /LR.lazard_resolvent_cubic -!addrA.
have hdom :
    ltn (size
        ((LR.lazard_resolvent_cubic_a c)%:P * 'X ^+ 2 + (
          (LR.lazard_resolvent_cubic_b c)%:P * 'X +
          (LR.lazard_resolvent_cubic_g c)%:P)))
      (size ('X ^+ 3 : {poly F})).
  rewrite size_polyXn.
  exact: leq_ltn_trans (lazard_resolvent_cubic_tail_size c) (ltnSn 3).
by rewrite (lead_coefDl hdom) lead_coefXn.
Qed.

Lemma lazard_resolvent_cubic_square_size
    (c : RP.LazardDepressedRootCoefficients F) :
  size (LR.lazard_resolvent_cubic c ^+ 2) = 7%N.
Proof.
have hmonic := lazard_resolvent_cubic_monic c.
rewrite expr2 (size_monicM hmonic (monic_neq0 hmonic)).
by rewrite lazard_resolvent_cubic_size.
Qed.

Lemma lazard_resolvent_line_size
    (c : RP.LazardDepressedRootCoefficients F) :
  size (LR.lazard_resolvent_line c) = 2%N.
Proof. by rewrite /LR.lazard_resolvent_line size_XaddC. Qed.

(** The displayed polynomial is literally monic of size seven, independently
    of whether its six roots happen to be distinct. *)
Theorem lazard_resolvent_polynomial_size
    (c : RP.LazardDepressedRootCoefficients F) :
  size (LR.lazard_resolvent_polynomial c) = 7%N.
Proof.
rewrite /LR.lazard_resolvent_polynomial.
change
  (size
    (LR.lazard_resolvent_cubic c ^+ 2 +
      - (LR.lazard_resolvent_discriminant c *:
          LR.lazard_resolvent_line c)) = 7%N).
have hdom :
    ltn (size
        (- (LR.lazard_resolvent_discriminant c *:
          LR.lazard_resolvent_line c)))
      (size (LR.lazard_resolvent_cubic c ^+ 2)).
  rewrite lazard_resolvent_cubic_square_size size_polyN.
  have hline : ltn (size (LR.lazard_resolvent_line c)) 7.
    by rewrite lazard_resolvent_line_size.
  exact: leq_ltn_trans
    (size_scale_leq (LR.lazard_resolvent_discriminant c)
      (LR.lazard_resolvent_line c)) hline.
by rewrite (size_polyDl hdom) lazard_resolvent_cubic_square_size.
Qed.

Theorem lazard_resolvent_polynomial_monic
    (c : RP.LazardDepressedRootCoefficients F) :
  LR.lazard_resolvent_polynomial c \is monic.
Proof.
apply/monicP.
rewrite /LR.lazard_resolvent_polynomial.
change
  (lead_coef
    (LR.lazard_resolvent_cubic c ^+ 2 +
      - (LR.lazard_resolvent_discriminant c *:
          LR.lazard_resolvent_line c)) = 1).
have hdom :
    ltn (size
        (- (LR.lazard_resolvent_discriminant c *:
          LR.lazard_resolvent_line c)))
      (size (LR.lazard_resolvent_cubic c ^+ 2)).
  rewrite lazard_resolvent_cubic_square_size size_polyN.
  have hline : ltn (size (LR.lazard_resolvent_line c)) 7.
    by rewrite lazard_resolvent_line_size.
  exact: leq_ltn_trans
    (size_scale_leq (LR.lazard_resolvent_discriminant c)
      (LR.lazard_resolvent_line c)) hline.
rewrite (lead_coefDl hdom) lead_coef_exp.
have /monicP hcubic := lazard_resolvent_cubic_monic c.
by rewrite hcubic expr2 mulr1.
Qed.

End RootCertificate.

Print Assumptions lazard_resolvent_root_fraction_free_identity.
Print Assumptions lazard_resolvent_root_i4.
Print Assumptions lazard_resolvent_polynomial_size.
Print Assumptions lazard_resolvent_polynomial_monic.

End PolynomialFormulasLazardQuinticResolventRootCertificate.
