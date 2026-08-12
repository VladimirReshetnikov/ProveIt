From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction
  Fin5TransitiveClassification
  LazardGeneralResolventCriterion LazardSection5ExactStabilizers
  LazardQuinticRootRadicals LazardQuinticRootInvariantENonzeroF20
  LazardQuinticRootMembershipDescent
  LazardQuinticCanonicalEpsilonNonzero.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Literal two-coset orbit products for the degree-five sharpness claims in
    Section 5 of Lazard's paper.  The relevant relative quotients are
    [D5/C5] and [F20/D5].  This includes the intermediate discriminant
    invariant [T' U'] as well as [T'], [U'], and [epsilon].  Their two
    displayed values are [(t,-t)], and
    distinctness is derived from [t != 0] and [2 != 0]; it is not supplied
    as a separability or coset-distinctness certificate. *)
Module PolynomialFormulasLazardSection5DegreeFiveRelativeResolvents.

Import GRing.Theory.
Module QF := PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module Class := PolynomialFormulasFin5TransitiveClassification.
Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module Exact := PolynomialFormulasLazardSection5ExactStabilizers.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module ENZ := PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.
Module MD := PolynomialFormulasLazardQuinticRootMembershipDescent.
Module CEN := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module GA := PolynomialFormulasQuinticGaloisAction.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Local Notation D5T := [subg Class.standard_D5].
Local Notation F20T := [subg QF.standard_F20].

(** The relative subgroups, represented as preimages under the subtype
    inclusion morphisms. *)
Definition C5_in_D5 : {group D5T} :=
  sgval @*^-1 QF.standard_C5.

Definition D5_in_F20 : {group F20T} :=
  sgval @*^-1 Class.standard_D5.

Lemma mem_C5_in_D5 (g : D5T) :
  (g \in C5_in_D5) = (sgval g \in QF.standard_C5).
Proof. by rewrite /C5_in_D5 morphpreE inE. Qed.

Lemma mem_D5_in_F20 (g : F20T) :
  (g \in D5_in_F20) = (sgval g \in Class.standard_D5).
Proof. by rewrite /D5_in_F20 morphpreE inE. Qed.

Definition d5_reflection : D5T := subg Class.reflection.

Definition f20_multiplier_two : F20T := subg QF.multiplier_two.

Lemma d5_reflectionE : sgval d5_reflection = Class.reflection.
Proof.
rewrite /d5_reflection subgK //.
by rewrite /Class.standard_D5 join_subG; apply/orP; right; rewrite cycle_id.
Qed.

Lemma f20_multiplier_twoE :
  sgval f20_multiplier_two = QF.multiplier_two.
Proof.
by rewrite /f20_multiplier_two subgK //
  QF.multiplier_two_mem_standard_F20.
Qed.

(** Kernel-checked finite certificates that these really are the two
    relative right cosets. *)
Definition C5_D5_two_cosets_check : bool :=
  [forall g : D5T,
    (C5_in_D5 :* g == C5_in_D5) ||
    (C5_in_D5 :* g == C5_in_D5 :* d5_reflection)].

Lemma C5_D5_two_cosets_checkP : C5_D5_two_cosets_check.
Proof. vm_compute. Qed.

Definition D5_F20_two_cosets_check : bool :=
  [forall g : F20T,
    (D5_in_F20 :* g == D5_in_F20) ||
    (D5_in_F20 :* g == D5_in_F20 :* f20_multiplier_two)].

Lemma D5_F20_two_cosets_checkP : D5_F20_two_cosets_check.
Proof. vm_compute. Qed.

Lemma C5_D5_other_coset_ne_base :
  C5_in_D5 :* d5_reflection != C5_in_D5.
Proof. vm_compute. Qed.

Lemma D5_F20_other_coset_ne_base :
  D5_in_F20 :* f20_multiplier_two != D5_in_F20.
Proof. vm_compute. Qed.

(** Every element of the standard [F20] is either in [D5] or has a
    [D5]-element followed by the displayed multiplier-two representative.
    This finite certificate lets the representative-value theorem below
    identify the signed quotient function with the literal root action for
    every representative, not only for the two chosen representatives. *)
Definition standard_F20_D5_decomposition_check : bool :=
  [forall s : QF.S5, (s \in QF.standard_F20) ==>
    ((s \in Class.standard_D5) ||
      [exists d : QF.S5,
        (d \in Class.standard_D5) &&
        (s == d * QF.multiplier_two)])].

Lemma standard_F20_D5_decomposition_checkP :
  standard_F20_D5_decomposition_check.
Proof. vm_compute. Qed.

Lemma standard_F20_D5_decomposition (s : QF.S5) :
  s \in QF.standard_F20 ->
  s \in Class.standard_D5 \/
    exists d : QF.S5,
      d \in Class.standard_D5 /\ s = d * QF.multiplier_two.
Proof.
move=> hs.
have h := implyP (forallP standard_F20_D5_decomposition_checkP s) hs.
case/orP: h=> [hD | /existsP [d /andP [hd /eqP hsd]]].
- by left.
- by right; exists d.
Qed.

Lemma C5_D5_two_cosets C :
  C \in GC.lazard_right_coset_orbit C5_in_D5 ->
  C = C5_in_D5 \/ C = C5_in_D5 :* d5_reflection.
Proof.
case/rcosetsP=> g _ ->.
have h := forallP C5_D5_two_cosets_checkP g.
case/orP: h=> /eqP h.
- by left.
- by right.
Qed.

Lemma D5_F20_two_cosets C :
  C \in GC.lazard_right_coset_orbit D5_in_F20 ->
  C = D5_in_F20 \/ C = D5_in_F20 :* f20_multiplier_two.
Proof.
case/rcosetsP=> g _ ->.
have h := forallP D5_F20_two_cosets_checkP g.
case/orP: h=> /eqP h.
- by left.
- by right.
Qed.

(** The quotient-indexed signed value and its literal orbit product. *)
Section SignedTwoCoset.

Variables (F : fieldType) (hT : finGroupType).
Variable G : {group hT}.

Definition signed_relative_value (t : F) (C : {set hT}) : F :=
  if C == G then t else -t.

Definition signed_relative_resolvent (t : F) : {poly F} :=
  GC.lazard_orbit_resolvent G (signed_relative_value t).

Lemma value_ne_neg_of_ne_zero_of_two_ne_zero (t : F) :
  t != 0 -> (2%:R : F) != 0 -> t != -t.
Proof.
move=> t_neq0 two_neq0; apply/eqP=> h.
have hsum : t + t = 0 by rewrite h addNr.
have hproduct : (2%:R : F) * t = 0.
  by rewrite mulr_natl mulr2n hsum.
have hnonzero := mulf_neq0 two_neq0 t_neq0.
by move: hnonzero; rewrite hproduct eqxx.
Qed.

Lemma signed_relative_value_injective
    (other : {set hT})
    (two_cosets : forall C,
      C \in GC.lazard_right_coset_orbit G -> C = G \/ C = other)
    (other_ne : other != G) (t : F)
    (t_neq0 : t != 0) (two_neq0 : (2%:R : F) != 0) :
  {in GC.lazard_right_coset_orbit G &,
    injective (signed_relative_value t)}.
Proof.
have t_ne_neg := value_ne_neg_of_ne_zero_of_two_ne_zero
  t_neq0 two_neq0.
move=> C D Cmem Dmem hvalue.
case: (two_cosets C Cmem)=> ->;
case: (two_cosets D Dmem)=> ->.
- exact: erefl.
- move: t_ne_neg.
  rewrite /signed_relative_value eqxx (negPf other_ne)=> t_ne_neg.
  by move: t_ne_neg; rewrite hvalue eqxx.
- move: t_ne_neg.
  rewrite /signed_relative_value eqxx (negPf other_ne)=> t_ne_neg.
  by move: t_ne_neg; rewrite -hvalue eqxx.
- exact: erefl.
Qed.

Theorem signed_relative_resolvent_separable
    (other : {set hT})
    (two_cosets : forall C,
      C \in GC.lazard_right_coset_orbit G -> C = G \/ C = other)
    (other_ne : other != G) (t : F)
    (t_neq0 : t != 0) (two_neq0 : (2%:R : F) != 0) :
  separable_poly (signed_relative_resolvent t).
Proof.
rewrite /signed_relative_resolvent /GC.lazard_orbit_resolvent
  separable_prod_XsubC /GC.lazard_orbit_value_sequence.
apply/dinjectiveP.
exact: signed_relative_value_injective
  two_cosets other_ne t_neq0 two_neq0.
Qed.

End SignedTwoCoset.

(** The displayed generator actions. *)
Section RootActions.

Variable F : fieldType.

Lemma lazard_root_T_prime_reflection (roots : 5.-tuple F) :
  RR.lazard_root_T_prime
      (TV.permute_quintic_roots Class.reflection roots) =
    - RR.lazard_root_T_prime roots.
Proof.
by rewrite /Class.reflection expr2 TV.permute_quintic_roots_mul
  ENZ.lazard_root_T_prime_multiplier_two
  ENZ.lazard_root_U_prime_multiplier_two.
Qed.

Lemma lazard_root_U_prime_reflection (roots : 5.-tuple F) :
  RR.lazard_root_U_prime
      (TV.permute_quintic_roots Class.reflection roots) =
    - RR.lazard_root_U_prime roots.
Proof.
rewrite /Class.reflection expr2 TV.permute_quintic_roots_mul
  ENZ.lazard_root_U_prime_multiplier_two
  ENZ.lazard_root_T_prime_multiplier_two.
by rewrite opprK.
Qed.

Lemma lazard_root_T_prime_standard_C5
    (roots : 5.-tuple F) (g : QF.S5) :
  g \in QF.standard_C5 ->
  RR.lazard_root_T_prime (TV.permute_quintic_roots g roots) =
    RR.lazard_root_T_prime roots.
Proof.
move/cycleP=> [n ->].
exact: MD.lazard_root_function_expg
  ENZ.lazard_root_T_prime_five_cycle.
Qed.

Lemma lazard_root_U_prime_standard_C5
    (roots : 5.-tuple F) (g : QF.S5) :
  g \in QF.standard_C5 ->
  RR.lazard_root_U_prime (TV.permute_quintic_roots g roots) =
    RR.lazard_root_U_prime roots.
Proof.
move/cycleP=> [n ->].
exact: MD.lazard_root_function_expg
  ENZ.lazard_root_U_prime_five_cycle.
Qed.

Lemma lazard_root_epsilon_five_cycle
    (omega : F) (roots : 5.-tuple F) :
  RR.lazard_root_epsilon omega
      (TV.permute_quintic_roots QF.five_cycle roots) =
    RR.lazard_root_epsilon omega roots.
Proof.
by rewrite /RR.lazard_root_epsilon
  MD.lazard_epsilon_product_five_cycle.
Qed.

Lemma lazard_root_epsilon_multiplier_two
    (omega : F) (roots : 5.-tuple F) :
  RR.lazard_root_epsilon omega
      (TV.permute_quintic_roots QF.multiplier_two roots) =
    - RR.lazard_root_epsilon omega roots.
Proof.
by rewrite /RR.lazard_root_epsilon
  MD.lazard_epsilon_product_multiplier_two mulrN.
Qed.

Lemma lazard_root_epsilon_reflection
    (omega : F) (roots : 5.-tuple F) :
  RR.lazard_root_epsilon omega
      (TV.permute_quintic_roots Class.reflection roots) =
    RR.lazard_root_epsilon omega roots.
Proof.
by rewrite /Class.reflection expr2 TV.permute_quintic_roots_mul
  !lazard_root_epsilon_multiplier_two opprK.
Qed.

Lemma lazard_root_epsilon_five_cycle_expg
    (omega : F) (n : nat) (roots : 5.-tuple F) :
  RR.lazard_root_epsilon omega
      (TV.permute_quintic_roots (QF.five_cycle ^+ n) roots) =
    RR.lazard_root_epsilon omega roots.
Proof.
exact: MD.lazard_root_function_expg
  (lazard_root_epsilon_five_cycle omega).
Qed.

Lemma lazard_root_epsilon_standard_D5
    (omega : F) (roots : 5.-tuple F) (g : QF.S5) :
  g \in Class.standard_D5 ->
  RR.lazard_root_epsilon omega (TV.permute_quintic_roots g roots) =
    RR.lazard_root_epsilon omega roots.
Proof.
move=> hg; case: (Exact.standard_D5_decomposition hg)=> k [-> | ->].
- exact: lazard_root_epsilon_five_cycle_expg.
- by rewrite TV.permute_quintic_roots_mul
    lazard_root_epsilon_five_cycle_expg
    lazard_root_epsilon_reflection.
Qed.

(** Lazard's evident degree-ten discriminant relative invariant [T' U']. *)
Definition lazard_root_discriminant_product (roots : 5.-tuple F) : F :=
  RR.lazard_root_T_prime roots * RR.lazard_root_U_prime roots.

Lemma lazard_root_discriminant_product_reflection
    (roots : 5.-tuple F) :
  lazard_root_discriminant_product
      (TV.permute_quintic_roots Class.reflection roots) =
    lazard_root_discriminant_product roots.
Proof.
by rewrite /lazard_root_discriminant_product
  lazard_root_T_prime_reflection lazard_root_U_prime_reflection
  mulNr mulrN opprK.
Qed.

Lemma lazard_root_discriminant_product_standard_D5
    (roots : 5.-tuple F) (g : QF.S5) :
  g \in Class.standard_D5 ->
  lazard_root_discriminant_product
      (TV.permute_quintic_roots g roots) =
    lazard_root_discriminant_product roots.
Proof.
move=> hg; case: (Exact.standard_D5_decomposition hg)=> k [-> | ->].
- rewrite /lazard_root_discriminant_product.
  by rewrite
    (MD.lazard_root_function_expg ENZ.lazard_root_T_prime_five_cycle)
    (MD.lazard_root_function_expg ENZ.lazard_root_U_prime_five_cycle).
- rewrite TV.permute_quintic_roots_mul
    lazard_root_discriminant_product_reflection
    /lazard_root_discriminant_product.
  by rewrite
    (MD.lazard_root_function_expg ENZ.lazard_root_T_prime_five_cycle)
    (MD.lazard_root_function_expg ENZ.lazard_root_U_prime_five_cycle).
Qed.

Lemma lazard_root_discriminant_product_multiplier_two
    (roots : 5.-tuple F) :
  lazard_root_discriminant_product
      (TV.permute_quintic_roots QF.multiplier_two roots) =
    - lazard_root_discriminant_product roots.
Proof.
rewrite /lazard_root_discriminant_product
  ENZ.lazard_root_T_prime_multiplier_two
  ENZ.lazard_root_U_prime_multiplier_two mulrN.
by rewrite [RR.lazard_root_U_prime roots * RR.lazard_root_T_prime roots]mulrC.
Qed.

End RootActions.

(** [T' U'] on the literal relative quotient [F20/D5]. *)
Section DiscriminantD5F20Resolvent.

Variable F : fieldType.
Variable roots : 5.-tuple F.

Definition lazard_D5_F20_discriminant_value : {set F20T} -> F :=
  signed_relative_value D5_in_F20
    (lazard_root_discriminant_product roots).

Definition lazard_D5_F20_discriminant_relative_resolvent : {poly F} :=
  GC.lazard_orbit_resolvent D5_in_F20
    lazard_D5_F20_discriminant_value.

Lemma lazard_D5_F20_discriminant_value_base :
  lazard_D5_F20_discriminant_value D5_in_F20 =
    lazard_root_discriminant_product roots.
Proof.
by rewrite /lazard_D5_F20_discriminant_value
  /signed_relative_value eqxx.
Qed.

Lemma lazard_D5_F20_discriminant_value_multiplier_two :
  lazard_D5_F20_discriminant_value
      (D5_in_F20 :* f20_multiplier_two) =
    lazard_root_discriminant_product
      (TV.permute_quintic_roots QF.multiplier_two roots).
Proof.
rewrite /lazard_D5_F20_discriminant_value /signed_relative_value
  (negPf D5_F20_other_coset_ne_base).
exact: esym (lazard_root_discriminant_product_multiplier_two roots).
Qed.

(** The quotient-indexed signed function is literally the value of [T'U']
    on every standard-[F20] representative. *)
Lemma lazard_D5_F20_discriminant_value_representative (g : F20T) :
  lazard_D5_F20_discriminant_value (D5_in_F20 :* g) =
    lazard_root_discriminant_product
      (TV.permute_quintic_roots (sgval g) roots).
Proof.
case: (standard_F20_D5_decomposition (subgP g))=> [hgD | [d [hd hgd]]].
- have hgDsub : g \in D5_in_F20 by rewrite mem_D5_in_F20.
  rewrite /lazard_D5_F20_discriminant_value /signed_relative_value
    (rcoset_id hgDsub) eqxx.
  exact: esym (lazard_root_discriminant_product_standard_D5 roots hgD).
- pose dF : F20T := subg d.
  have hdF : sgval dF = d.
    rewrite /dF subgK //.
    exact: (subsetP Class.standard_D5_sub_standard_F20) hd.
  have hdDsub : dF \in D5_in_F20 by rewrite mem_D5_in_F20 hdF.
  have hg : g = dF * f20_multiplier_two.
    apply: val_inj.
    by rewrite /= hdF f20_multiplier_twoE hgd.
  have hcoset :
      D5_in_F20 :* g = D5_in_F20 :* f20_multiplier_two.
    by rewrite hg -rcosetM (rcoset_id hdDsub).
  rewrite /lazard_D5_F20_discriminant_value /signed_relative_value
    hcoset (negPf D5_F20_other_coset_ne_base) hgd
    TV.permute_quintic_roots_mul.
  rewrite (lazard_root_discriminant_product_standard_D5
    (TV.permute_quintic_roots QF.multiplier_two roots) hd).
  exact: esym (lazard_root_discriminant_product_multiplier_two roots).
Qed.

Theorem lazard_root_discriminant_product_D5_F20_relative_resolvent_separable
    (roots_injective : injective (tnth roots))
    (two_neq0 : (2%:R : F) != 0) :
  separable_poly lazard_D5_F20_discriminant_relative_resolvent.
Proof.
rewrite /lazard_D5_F20_discriminant_relative_resolvent
  /lazard_D5_F20_discriminant_value.
apply: signed_relative_resolvent_separable
  D5_F20_two_cosets D5_F20_other_coset_ne_base _ two_neq0.
rewrite /lazard_root_discriminant_product.
exact: mulf_neq0 (RR.lazard_root_T_prime_neq0 roots_injective)
  (RR.lazard_root_U_prime_neq0 roots_injective).
Qed.

End DiscriminantD5F20Resolvent.

(** [T'] and [U'] on the literal relative quotient [D5/C5]. *)
Section C5D5Resolvents.

Variable F : fieldType.
Variable roots : 5.-tuple F.

Definition lazard_C5_D5_T_value : {set D5T} -> F :=
  signed_relative_value C5_in_D5 (RR.lazard_root_T_prime roots).

Definition lazard_C5_D5_U_value : {set D5T} -> F :=
  signed_relative_value C5_in_D5 (RR.lazard_root_U_prime roots).

Definition lazard_C5_D5_T_relative_resolvent : {poly F} :=
  GC.lazard_orbit_resolvent C5_in_D5 lazard_C5_D5_T_value.

Definition lazard_C5_D5_U_relative_resolvent : {poly F} :=
  GC.lazard_orbit_resolvent C5_in_D5 lazard_C5_D5_U_value.

Lemma lazard_C5_D5_T_value_base :
  lazard_C5_D5_T_value C5_in_D5 = RR.lazard_root_T_prime roots.
Proof. by rewrite /lazard_C5_D5_T_value /signed_relative_value eqxx. Qed.

Lemma lazard_C5_D5_T_value_reflection :
  lazard_C5_D5_T_value (C5_in_D5 :* d5_reflection) =
    RR.lazard_root_T_prime
      (TV.permute_quintic_roots Class.reflection roots).
Proof.
rewrite /lazard_C5_D5_T_value /signed_relative_value
  (negPf C5_D5_other_coset_ne_base).
exact: esym (lazard_root_T_prime_reflection roots).
Qed.

Lemma lazard_C5_D5_U_value_base :
  lazard_C5_D5_U_value C5_in_D5 = RR.lazard_root_U_prime roots.
Proof. by rewrite /lazard_C5_D5_U_value /signed_relative_value eqxx. Qed.

Lemma lazard_C5_D5_U_value_reflection :
  lazard_C5_D5_U_value (C5_in_D5 :* d5_reflection) =
    RR.lazard_root_U_prime
      (TV.permute_quintic_roots Class.reflection roots).
Proof.
rewrite /lazard_C5_D5_U_value /signed_relative_value
  (negPf C5_D5_other_coset_ne_base).
exact: esym (lazard_root_U_prime_reflection roots).
Qed.

Theorem lazard_root_T_prime_C5_D5_relative_resolvent_separable
    (roots_injective : injective (tnth roots))
    (two_neq0 : (2%:R : F) != 0) :
  separable_poly lazard_C5_D5_T_relative_resolvent.
Proof.
rewrite /lazard_C5_D5_T_relative_resolvent
  /lazard_C5_D5_T_value.
exact: signed_relative_resolvent_separable
  C5_D5_two_cosets C5_D5_other_coset_ne_base
  (RR.lazard_root_T_prime_neq0 roots_injective) two_neq0.
Qed.

Theorem lazard_root_U_prime_C5_D5_relative_resolvent_separable
    (roots_injective : injective (tnth roots))
    (two_neq0 : (2%:R : F) != 0) :
  separable_poly lazard_C5_D5_U_relative_resolvent.
Proof.
rewrite /lazard_C5_D5_U_relative_resolvent
  /lazard_C5_D5_U_value.
exact: signed_relative_resolvent_separable
  C5_D5_two_cosets C5_D5_other_coset_ne_base
  (RR.lazard_root_U_prime_neq0 roots_injective) two_neq0.
Qed.

End C5D5Resolvents.

(** Paper-facing [C5 < D5] wrappers for an irreducible rational quintic.
    The generic endpoints expose the precise mathematical inputs
    (duplicate-free roots and [2 != 0]); these wrappers derive both from the
    irreducible rational polynomial, so no separability certificate is left
    to the caller. *)
Section IrreducibleRationalC5D5Resolvents.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

Lemma lazard_irreducible_rational_two_neq0 : (2%:R : L) != 0.
Proof.
by rewrite -[2%:R](rmorph_nat
  (char0_ratr (char_numfield p)) 2) fmorph_eq0.
Qed.

Theorem lazard_irreducible_rational_root_T_prime_C5_D5_relative_resolvent_separable :
  separable_poly (@lazard_C5_D5_T_relative_resolvent L roots).
Proof.
apply: lazard_root_T_prime_C5_D5_relative_resolvent_separable.
- exact: (@GA.quintic_root_tuple_injective p p_size p_irr).
- exact: lazard_irreducible_rational_two_neq0.
Qed.

Theorem lazard_irreducible_rational_root_U_prime_C5_D5_relative_resolvent_separable :
  separable_poly (@lazard_C5_D5_U_relative_resolvent L roots).
Proof.
apply: lazard_root_U_prime_C5_D5_relative_resolvent_separable.
- exact: (@GA.quintic_root_tuple_injective p p_size p_irr).
- exact: lazard_irreducible_rational_two_neq0.
Qed.

Theorem lazard_irreducible_rational_root_discriminant_product_D5_F20_relative_resolvent_separable :
  separable_poly
    (@lazard_D5_F20_discriminant_relative_resolvent L roots).
Proof.
apply: lazard_root_discriminant_product_D5_F20_relative_resolvent_separable.
- exact: (@GA.quintic_root_tuple_injective p p_size p_irr).
- exact: lazard_irreducible_rational_two_neq0.
Qed.

End IrreducibleRationalC5D5Resolvents.

(** [epsilon] on the literal relative quotient [F20/D5]. *)
Section D5F20Resolvent.

Variable F : fieldType.
Variable omega : F.
Variable roots : 5.-tuple F.

Definition lazard_D5_F20_epsilon_value : {set F20T} -> F :=
  signed_relative_value D5_in_F20 (RR.lazard_root_epsilon omega roots).

Definition lazard_D5_F20_epsilon_relative_resolvent : {poly F} :=
  GC.lazard_orbit_resolvent D5_in_F20 lazard_D5_F20_epsilon_value.

Lemma lazard_D5_F20_epsilon_value_base :
  lazard_D5_F20_epsilon_value D5_in_F20 =
    RR.lazard_root_epsilon omega roots.
Proof.
by rewrite /lazard_D5_F20_epsilon_value
  /signed_relative_value eqxx.
Qed.

Lemma lazard_D5_F20_epsilon_value_multiplier_two :
  lazard_D5_F20_epsilon_value
      (D5_in_F20 :* f20_multiplier_two) =
    RR.lazard_root_epsilon omega
      (TV.permute_quintic_roots QF.multiplier_two roots).
Proof.
rewrite /lazard_D5_F20_epsilon_value /signed_relative_value
  (negPf D5_F20_other_coset_ne_base).
exact: esym (lazard_root_epsilon_multiplier_two omega roots).
Qed.

Theorem lazard_root_epsilon_D5_F20_relative_resolvent_separable
    (epsilon_neq0 : RR.lazard_root_epsilon omega roots != 0)
    (two_neq0 : (2%:R : F) != 0) :
  separable_poly lazard_D5_F20_epsilon_relative_resolvent.
Proof.
rewrite /lazard_D5_F20_epsilon_relative_resolvent
  /lazard_D5_F20_epsilon_value.
exact: signed_relative_resolvent_separable
  D5_F20_two_cosets D5_F20_other_coset_ne_base
  epsilon_neq0 two_neq0.
Qed.

End D5F20Resolvent.

(** On a canonical irreducible depressed rational quintic, epsilon
    nonvanishing and [2 != 0] are both theorems, so the paper-facing
    separability result has no nonvanishing premise. *)
Section CanonicalEpsilonResolvent.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let L := numfield p.

Lemma lazard_canonical_two_neq0 : (2%:R : L) != 0.
Proof.
by rewrite -[2%:R](rmorph_nat
  (char0_ratr (char_numfield p)) 2) fmorph_eq0.
Qed.

Lemma lazard_selected_roots_injective
    (p_irr : irreducible_poly p) (i : 'I_6) :
  injective (tnth (ID.lazard_selected_roots f i)).
Proof.
move=> a b.
rewrite /ID.lazard_selected_roots !TV.tnth_permute_quintic_roots=> hij.
apply: perm_inj.
exact: (@GA.quintic_root_tuple_injective p
  (CD.size_rational_monic_quintic f) p_irr _ _ hij).
Qed.

Theorem lazard_selected_root_T_prime_C5_D5_relative_resolvent_separable
    (p_irr : irreducible_poly p) (i : 'I_6) :
  separable_poly
    (@lazard_C5_D5_T_relative_resolvent L
      (ID.lazard_selected_roots f i)).
Proof.
apply: lazard_root_T_prime_C5_D5_relative_resolvent_separable.
- exact: lazard_selected_roots_injective p_irr i.
- exact: lazard_canonical_two_neq0.
Qed.

Theorem lazard_selected_root_U_prime_C5_D5_relative_resolvent_separable
    (p_irr : irreducible_poly p) (i : 'I_6) :
  separable_poly
    (@lazard_C5_D5_U_relative_resolvent L
      (ID.lazard_selected_roots f i)).
Proof.
apply: lazard_root_U_prime_C5_D5_relative_resolvent_separable.
- exact: lazard_selected_roots_injective p_irr i.
- exact: lazard_canonical_two_neq0.
Qed.

Theorem lazard_selected_root_epsilon_D5_F20_relative_resolvent_separable
    (p_irr : irreducible_poly p)
    (hdepressed : CEN.lazard_canonical_quintic_depressed f)
    (i : 'I_6) (omega : L)
    (omega_primitive : 5.-primitive_root omega) :
  separable_poly
    (@lazard_D5_F20_epsilon_relative_resolvent L omega
      (ID.lazard_selected_roots f i)).
Proof.
apply: lazard_root_epsilon_D5_F20_relative_resolvent_separable.
- exact: CEN.lazard_selected_root_epsilon_neq0
    p_irr hdepressed omega_primitive.
- exact: lazard_canonical_two_neq0.
Qed.

(** All three degree-five sharpness candidates on the same selected ordering.
    No injectivity, nonvanishing, coset, or separability certificate occurs
    among the hypotheses. *)
Theorem lazard_selected_section5_degree_five_relative_resolvents_separable
    (p_irr : irreducible_poly p)
    (hdepressed : CEN.lazard_canonical_quintic_depressed f)
    (i : 'I_6) (omega : L)
    (omega_primitive : 5.-primitive_root omega) :
  separable_poly
      (@lazard_C5_D5_T_relative_resolvent L
        (ID.lazard_selected_roots f i)) /\
  separable_poly
      (@lazard_C5_D5_U_relative_resolvent L
        (ID.lazard_selected_roots f i)) /\
  separable_poly
      (@lazard_D5_F20_epsilon_relative_resolvent L omega
        (ID.lazard_selected_roots f i)).
Proof.
split.
- exact: (@lazard_selected_root_T_prime_C5_D5_relative_resolvent_separable
    f p_irr i).
- split.
  + exact: (@lazard_selected_root_U_prime_C5_D5_relative_resolvent_separable
      f p_irr i).
  + exact: (@lazard_selected_root_epsilon_D5_F20_relative_resolvent_separable
      f p_irr hdepressed i omega omega_primitive).
Qed.

End CanonicalEpsilonResolvent.

End PolynomialFormulasLazardSection5DegreeFiveRelativeResolvents.
