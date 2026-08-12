From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticPaddedSymmetrization
  SexticRationalRootSearch QuinticRecursiveFactor
  SexticComputedResolvents SexticNewtonPowerSums
  LazardQuinticRootProjections
  LazardQuinticVieta
  QuinticCanonicalDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The explicit homogeneous scale relating the executable integral Dummit
    resolvent to its monic scalar-resolvent semantics. *)
Module PolynomialFormulasLazardQuinticExecutableScale.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module V := PolynomialFormulasLazardQuinticVieta.
Module QF := PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CR := PolynomialFormulasSexticComputedResolvents.
Module NPS := PolynomialFormulasSexticNewtonPowerSums.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Local Open Scope ring_scope.

Section Scale.

Variable F : fieldType.

(** The ordinary finite product of a five-tuple is its fifth elementary
    symmetric function. *)
Lemma lazard_five_tuple_productE (roots : 5.-tuple F) :
  \prod_(i : 'I_5) tnth roots i =
    V.lazard_five_esymm5 (tnth roots).
Proof.
rewrite !big_ord_recl !big_ord0 /V.lazard_five_esymm5.
have h0 : (@ord0 4) = QF.o0 by apply: val_inj.
have h1 : lift (@ord0 4) (@ord0 3) = QF.o1 by apply: val_inj.
have h2 : lift (@ord0 4) (lift (@ord0 3) (@ord0 2)) = QF.o2
  by apply: val_inj.
have h3 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (@ord0 1))) = QF.o3
  by apply: val_inj.
have h4 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (lift (@ord0 1) (@ord0 0)))) =
      QF.o4 by apply: val_inj.
by rewrite h4 h3 h2 h1 h0 mulr1 !mulrA.
Qed.

(** For the monic depressed quintic [X^5 + pX^3 + qX^2 + rX + s],
    the product of the five roots is [-s]. *)
Theorem lazard_depressed_root_product p q r s (roots : 5.-tuple F)
    (hvieta :
      V.lazard_depressed_five_root_relations p q r s (tnth roots)) :
  \prod_(i : 'I_5) tnth roots i = - s.
Proof.
rewrite lazard_five_tuple_productE.
exact: V.lazard_vieta_product hvieta.
Qed.

Corollary lazard_depressed_root_product_of_coefficients
    (c : RP.LazardDepressedRootCoefficients F) (roots : 5.-tuple F)
    (hvieta :
      V.lazard_depressed_five_root_relations
        (RP.lazard_root_p c) (RP.lazard_root_q c)
        (RP.lazard_root_r c) (RP.lazard_root_s c) (tnth roots)) :
  \prod_(i : 'I_5) tnth roots i = - RP.lazard_root_s c.
Proof. exact: lazard_depressed_root_product hvieta. Qed.

(** Hence the homogeneous Dummit scale [120 * product roots] is the explicit
    coefficient-side scalar [-(120*s)]. *)
Theorem lazard_depressed_resolvent_scale p q r s (roots : 5.-tuple F)
    (hvieta :
      V.lazard_depressed_five_root_relations p q r s (tnth roots)) :
  120%:R * \prod_(i : 'I_5) tnth roots i = - (120%:R * s).
Proof.
by rewrite (lazard_depressed_root_product hvieta) mulrN.
Qed.

(** Direct executable-polynomial form: the already certified integral
    coefficient list is the monic scalar resolvent multiplied by the now
    explicit depressed scale [-(120*s)]. *)
Theorem lazard_depressed_scaled_resolvent_poly_correct
    p q r s (roots : 5.-tuple F) (f : QRF.monic_quintic)
    (hcoeff :
      @CR.cast_int_values F
          (CR.monic_elementary_values
            (QRF.quintic_sextic_embedding f)) =
        NPS.elementary_values (QPS.pad_quintic_roots roots))
    (hvieta :
      V.lazard_depressed_five_root_relations p q r s (tnth roots)) :
  map_poly (intr : int -> F)
      (RRS.coefficient_list_poly_int
        (QPS.quintic_scaled_resolvent f)) =
    (- (120%:R * s)) *: TV.quintic_scalar_resolvent roots.
Proof.
rewrite (@CD.quintic_scaled_resolvent_poly_correct F roots f hcoeff).
by rewrite (lazard_depressed_resolvent_scale hvieta).
Qed.

End Scale.

Print Assumptions lazard_depressed_root_product.
Print Assumptions lazard_depressed_resolvent_scale.
Print Assumptions lazard_depressed_scaled_resolvent_poly_correct.

End PolynomialFormulasLazardQuinticExecutableScale.
