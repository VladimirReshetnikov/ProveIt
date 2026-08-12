From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.
From PolynomialFormulas Require Import
  AbelRuffini QuinticRadicalDecidability
  LazardQuinticRootProjections LazardQuinticGeneralDepression
  LazardQuinticRationalScalingAdapter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** End-to-end rational front end for a genuinely general quintic.

    [LazardQuinticRationalScalingAdapter] accepts arbitrary rational
    coefficients, but its final formula theorem starts with a *monic
    depressed* quintic.  This file closes the remaining normalization gap.
    It defines the actual general and depressed polynomials attached to
    [LazardGeneralQuinticCoefficients rat], proves their exact affine
    relation as polynomials (not merely at a supplied root), transports
    irreducibility and MathComp--Abel's explicit [algterm rat] formulas, and
    finally composes the existing denominator-safe common-compositum result.

    No equality between independently chosen splitting fields is assumed:
    the final package stays in the common overfield constructed by the
    depressed rational adapter and translates its five outputs by the
    rational Tschirnhaus shift. *)
Module PolynomialFormulasLazardQuinticGeneralRationalEndToEnd.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Notation ratrC := (@ratr algC).

Module AR := LeanProofs.PolynomialFormulasAbelRuffini.
Module QRD := PolynomialFormulasQuinticRadicalDecidability.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module GD := PolynomialFormulasLazardQuinticGeneralDepression.
Module RSA := PolynomialFormulasLazardQuinticRationalScalingAdapter.
Module O := PolynomialFormulasLazardOptimality.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.

Section PolynomialNormalization.

Variable c : GD.LazardGeneralQuinticCoefficients rat.

(** The literal polynomial [a X^5 + b X^4 + ... + f].  The [Poly]
    representation makes the size statement independent of cancellation
    tactics. *)
Definition lazard_general_rational_polynomial : {poly rat} :=
  Poly [:: GD.lazard_general_f c; GD.lazard_general_e c;
    GD.lazard_general_d c; GD.lazard_general_c c;
    GD.lazard_general_b c; GD.lazard_general_a c].

(** The monic depressed polynomial obtained from the coefficient formulas
    already proved in [LazardQuinticGeneralDepression]. *)
Definition lazard_general_depressed_polynomial : {poly rat} :=
  let d := GD.lazard_depress_general c in
  Poly [:: RP.lazard_root_s d; RP.lazard_root_r d; RP.lazard_root_q d;
    RP.lazard_root_p d; 0; 1].

Lemma lazard_general_rational_polynomial_horner x :
  lazard_general_rational_polynomial.[x] =
    GD.lazard_general_quintic_eval c x.
Proof.
rewrite /lazard_general_rational_polynomial horner_Poly /=
  /GD.lazard_general_quintic_eval.
ring.
Qed.

Lemma lazard_general_depressed_polynomial_horner x :
  lazard_general_depressed_polynomial.[x] =
    PolynomialFormulasLazardQuinticVieta.lazard_depressed_quintic_eval
      (RP.lazard_root_p (GD.lazard_depress_general c))
      (RP.lazard_root_q (GD.lazard_depress_general c))
      (RP.lazard_root_r (GD.lazard_depress_general c))
      (RP.lazard_root_s (GD.lazard_depress_general c)) x.
Proof.
rewrite /lazard_general_depressed_polynomial horner_Poly /=
  /PolynomialFormulasLazardQuinticVieta.lazard_depressed_quintic_eval.
ring.
Qed.

Lemma size_lazard_general_rational_polynomial
    (ha : GD.lazard_general_a c != 0) :
  size lazard_general_rational_polynomial = 6%N.
Proof.
rewrite /lazard_general_rational_polynomial (@PolyK _ 0) //=.
Qed.

Lemma size_lazard_general_depressed_polynomial :
  size lazard_general_depressed_polynomial = 6%N.
Proof.
rewrite /lazard_general_depressed_polynomial (@PolyK _ 0) //=.
Qed.

Lemma lazard_general_depressed_polynomial_monic :
  lazard_general_depressed_polynomial \is monic.
Proof.
apply/monicP.
rewrite lead_coefE size_lazard_general_depressed_polynomial
  /lazard_general_depressed_polynomial coef_Poly /=.
reflexivity.
Qed.

Lemma lazard_general_depressed_polynomial_depressed :
  RSA.lazard_rational_quintic_depressed
    lazard_general_depressed_polynomial.
Proof.
by rewrite /RSA.lazard_rational_quintic_depressed
  /lazard_general_depressed_polynomial coef_Poly.
Qed.

(** Difference between the two sides of the desired polynomial identity. *)
Definition lazard_general_translation_difference : {poly rat} :=
  lazard_general_rational_polynomial \Po
      ('X - (GD.lazard_depression_shift c)%:P) -
    GD.lazard_general_a c *: lazard_general_depressed_polynomial.

Lemma lazard_general_translation_difference_horner
    (ha : GD.lazard_general_a c != 0) y :
  lazard_general_translation_difference.[y] = 0.
Proof.
rewrite /lazard_general_translation_difference hornerD hornerN
  horner_comp hornerXsubC hornerZ
  lazard_general_rational_polynomial_horner
  lazard_general_depressed_polynomial_horner.
exact: (@GD.lazard_general_depression_eval rat c ha
  (by rewrite pnatr_eq0) y).
Qed.

Lemma size_lazard_general_translation_difference_le
    (ha : GD.lazard_general_a c != 0) :
  size lazard_general_translation_difference <= 6%N.
Proof.
rewrite /lazard_general_translation_difference subr_eq_add_opp.
apply: leq_trans (size_polyD _ _).
rewrite maxn_leq.
apply/andP; split.
- move: (size_comp_poly_leq lazard_general_rational_polynomial
    ('X - (GD.lazard_depression_shift c)%:P)).
  by rewrite (size_lazard_general_rational_polynomial ha) size_XsubC /=.
- by rewrite size_opp size_scale //
    size_lazard_general_depressed_polynomial.
Qed.

Definition lazard_six_rational_test_points : seq rat :=
  [:: 0; 1; 2; 3; 4; 5].

Lemma lazard_six_rational_test_points_size :
  size lazard_six_rational_test_points = 6%N.
Proof. reflexivity. Qed.

Lemma lazard_six_rational_test_points_uniq :
  uniq lazard_six_rational_test_points.
Proof. by rewrite /lazard_six_rational_test_points /=. Qed.

(** Exact polynomial-level monicization and depression identity.  The proof
    uses the already proved scalar identity at six distinct rational points;
    both sides have degree at most five, so the difference polynomial is
    zero. *)
Theorem lazard_general_polynomial_depression
    (ha : GD.lazard_general_a c != 0) :
  lazard_general_rational_polynomial \Po
      ('X - (GD.lazard_depression_shift c)%:P) =
    GD.lazard_general_a c *: lazard_general_depressed_polynomial.
Proof.
have hall : all (root lazard_general_translation_difference)
    lazard_six_rational_test_points.
  apply/allP=> y _.
  apply/rootP.
  exact: lazard_general_translation_difference_horner ha y.
have hzero : lazard_general_translation_difference = 0.
  apply: roots_geq_poly_eq0 hall lazard_six_rational_test_points_uniq.
  rewrite lazard_six_rational_test_points_size.
  exact: size_lazard_general_translation_difference_le ha.
move: hzero.
by rewrite /lazard_general_translation_difference subr_eq0.
Qed.

(** The polynomial identity remains exact after embedding the coefficients
    into any field extension. *)
Theorem lazard_general_depression_horner
    (ha : GD.lazard_general_a c != 0)
    (K : fieldType) (phi : {rmorphism rat -> K}) (y : K) :
  (map_poly phi lazard_general_rational_polynomial).
      [y - phi (GD.lazard_depression_shift c)] =
    phi (GD.lazard_general_a c) *
      (map_poly phi lazard_general_depressed_polynomial).[y].
Proof.
have h := congr1 (fun p : {poly rat} => (map_poly phi p).[y])
  (lazard_general_polynomial_depression ha).
move: h.
by rewrite map_comp_poly horner_comp map_polyXsubC hornerXsubC
  map_polyZ hornerZ.
Qed.

(** Root equality at the inverse Tschirnhaus coordinate. *)
Theorem lazard_general_root_at_depressed_coordinate
    (ha : GD.lazard_general_a c != 0)
    (K : fieldType) (phi : {rmorphism rat -> K}) (y : K) :
  root (map_poly phi lazard_general_rational_polynomial)
      (y - phi (GD.lazard_depression_shift c)) =
    root (map_poly phi lazard_general_depressed_polynomial) y.
Proof.
have haK : phi (GD.lazard_general_a c) != 0 by rewrite fmorph_eq0.
rewrite !rootE (lazard_general_depression_horner ha phi y).
by rewrite mulf_eq0 (negPf haK) orFb.
Qed.

(** Forward-coordinate spelling: [x] is an original root exactly when
    [x + b/(5a)] is a depressed root. *)
Theorem lazard_general_root_iff_depressed_coordinate
    (ha : GD.lazard_general_a c != 0)
    (K : fieldType) (phi : {rmorphism rat -> K}) (x : K) :
  root (map_poly phi lazard_general_rational_polynomial) x =
    root (map_poly phi lazard_general_depressed_polynomial)
      (x + phi (GD.lazard_depression_shift c)).
Proof.
have h := lazard_general_root_at_depressed_coordinate ha phi
  (x + phi (GD.lazard_depression_shift c)).
by rewrite addrK in h.
Qed.

Theorem lazard_general_root_bijection
    (ha : GD.lazard_general_a c != 0)
    (K : fieldType) (phi : {rmorphism rat -> K}) :
  (forall x : K,
    root (map_poly phi lazard_general_rational_polynomial) x =
      root (map_poly phi lazard_general_depressed_polynomial)
        (x + phi (GD.lazard_depression_shift c))) /\
  (forall y : K,
    root (map_poly phi lazard_general_depressed_polynomial) y =
      root (map_poly phi lazard_general_rational_polynomial)
        (y - phi (GD.lazard_depression_shift c))).
Proof.
split=> z.
- exact: lazard_general_root_iff_depressed_coordinate ha phi z.
- exact: esym (lazard_general_root_at_depressed_coordinate ha phi z).
Qed.

(* -------------------------------------------------------------------- *)
(** * Irreducibility transport *)

Lemma irreducible_of_comp_XaddC
    (K : fieldType) (p : {poly K}) (d : K) :
  irreducible_poly (p \Po ('X + d%:P)) -> irreducible_poly p.
Proof.
move=> [pcomp_gt1 pcomp_irred]; split.
- move: pcomp_gt1.
  by rewrite (size_comp_poly2 p) ?size_XaddC.
- move=> q q_size1 q_dvd_p.
  have qcomp_size1 : size (q \Po ('X + d%:P)) != 1%N.
    by rewrite (size_comp_poly2 q) ?size_XaddC.
  have qcomp_dvd :
      q \Po ('X + d%:P) %| p \Po ('X + d%:P) :=
    dvdp_comp_poly _ q_dvd_p.
  have qcomp_eq := pcomp_irred _ qcomp_size1 qcomp_dvd.
  apply/andP; case/andP: qcomp_eq=> qcp pcq; split.
  + move/(dvdp_comp_poly ('X - d%:P)): qcp.
    by rewrite !comp_polyXaddC_K.
  + move/(dvdp_comp_poly ('X - d%:P)): pcq.
    by rewrite !comp_polyXaddC_K.
Qed.

Lemma irreducible_poly_comp_XaddC_iff
    (K : fieldType) (p : {poly K}) (d : K) :
  irreducible_poly (p \Po ('X + d%:P)) <-> irreducible_poly p.
Proof.
split.
- exact: irreducible_of_comp_XaddC.
- move=> hp.
  apply: (@irreducible_of_comp_XaddC K
    (p \Po ('X + d%:P)) (- d)).
  by rewrite rmorphN -subr_eq_add_opp comp_polyXaddC_K.
Qed.

(** Irreducibility of the original nonmonic polynomial is equivalent to
    irreducibility of its monic depressed translate. *)
Theorem lazard_general_irreducible_iff_depressed
    (ha : GD.lazard_general_a c != 0) :
  irreducible_poly lazard_general_rational_polynomial <->
    irreducible_poly lazard_general_depressed_polynomial.
Proof.
have htranslate :
    irreducible_poly
        (lazard_general_rational_polynomial \Po
          ('X - (GD.lazard_depression_shift c)%:P)) <->
      irreducible_poly lazard_general_rational_polynomial.
  have h := irreducible_poly_comp_XaddC_iff
    lazard_general_rational_polynomial
    (- GD.lazard_depression_shift c).
  move: h.
  by rewrite rmorphN -subr_eq_add_opp.
rewrite -htranslate lazard_general_polynomial_depression.
exact: RSA.irreducible_poly_scale_iff ha.
Qed.

(* -------------------------------------------------------------------- *)
(** * Explicit [algterm rat] transport *)

Definition lazard_algterm_add_rational
    (d : rat) (t : algterm rat) : algterm rat :=
  BinOp Add t (Base d).

Definition lazard_algterm_sub_rational
    (d : rat) (t : algterm rat) : algterm rat :=
  BinOp Add t (Base (- d)).

Lemma lazard_algterm_add_rational_eval d t :
  algT_eval ratrC (lazard_algterm_add_rational d t) =
    algT_eval ratrC t + ratrC d.
Proof. reflexivity. Qed.

Lemma lazard_algterm_sub_rational_eval d t :
  algT_eval ratrC (lazard_algterm_sub_rational d t) =
    algT_eval ratrC t - ratrC d.
Proof. by rewrite /= rmorphN subr_eq_add_opp. Qed.

(** The explicit per-root radical-expression predicate is genuinely
    transported from the original polynomial, rather than redefined on the
    depressed one. *)
Theorem lazard_general_radical_formula_iff_depressed
    (ha : GD.lazard_general_a c != 0) :
  AR.radical_formula_solves lazard_general_rational_polynomial <->
    AR.radical_formula_solves lazard_general_depressed_polynomial.
Proof.
rewrite /AR.radical_formula_solves; split.
- move=> horiginal y hy.
  pose x := y - ratrC (GD.lazard_depression_shift c).
  have hx : x \in root
      (map_poly ratrC lazard_general_rational_polynomial).
    rewrite /x.
    by move: hy; rewrite -(@lazard_general_root_at_depressed_coordinate
      ha algC ratrC y).
  have [t ht] := horiginal x hx.
  exists (lazard_algterm_add_rational
    (GD.lazard_depression_shift c) t).
  by rewrite lazard_algterm_add_rational_eval ht /x subrK.
- move=> hdepressed x hx.
  pose y := x + ratrC (GD.lazard_depression_shift c).
  have hy : y \in root
      (map_poly ratrC lazard_general_depressed_polynomial).
    rewrite /y.
    by move: hx; rewrite (@lazard_general_root_iff_depressed_coordinate
      ha algC ratrC x).
  have [t ht] := hdepressed y hy.
  exists (lazard_algterm_sub_rational
    (GD.lazard_depression_shift c) t).
  by rewrite lazard_algterm_sub_rational_eval ht /y addrK.
Qed.

End PolynomialNormalization.

(* -------------------------------------------------------------------- *)
(** * Composition with the arbitrary-rational depressed adapter *)

(** The executable rational-resolvent condition belonging to the depressed
    polynomial of the original coefficient record. *)
Definition lazard_general_rational_resolvent_has_root
    (c : GD.LazardGeneralQuinticCoefficients rat) : Prop :=
  RRS.has_rational_root
    (QPS.quintic_scaled_resolvent
      (RSA.lazard_quintic_integer_data
        (lazard_general_depressed_polynomial c))).

(** Exact multiplicity-sensitive factorization attached to a five-entry
    output.  The leading coefficient is explicit because the original
    polynomial need not be monic. *)
Definition lazard_general_rational_output_factorization
    (c : GD.LazardGeneralQuinticCoefficients rat)
    (K : fieldExtType rat) (roots : 'I_5 -> K) : Prop :=
  map_poly (in_alg K) (lazard_general_rational_polynomial c) =
    in_alg K (GD.lazard_general_a c) *:
      \prod_(z <- [seq roots k | k <- enum 'I_5]) ('X - z%:P).

(** A prover-neutral semantic output package.  The witnesses constructed
    below are definitionally the denominator-safe Lazard outputs, divided by
    the denominator scale and then translated by [-b/(5a)]. *)
Definition lazard_general_rational_output_package
    (c : GD.LazardGeneralQuinticCoefficients rat) : Prop :=
  exists (K : fieldExtType rat) (L : {subfield K})
      (omega : K) (roots : 'I_5 -> K),
    5.-primitive_root omega /\
    @O.radical_extension rat K (1%AS : {subfield K}) L /\
    (forall k : 'I_5, roots k \in L) /\
    injective roots /\
    lazard_general_rational_output_factorization c K roots /\
    (forall k : 'I_5,
      root (map_poly (in_alg K)
        (lazard_general_rational_polynomial c)) (roots k)) /\
    (forall z : K,
      root (map_poly (in_alg K)
        (lazard_general_rational_polynomial c)) z ->
      exists k : 'I_5, z = roots k).

Section GeneralComposition.

Variable c : GD.LazardGeneralQuinticCoefficients rat.
Hypothesis ha : GD.lazard_general_a c != 0.

Let p := lazard_general_depressed_polynomial c.
Let p_size : size p = 6%N :=
  size_lazard_general_depressed_polynomial c.
Let p_monic : p \is monic :=
  lazard_general_depressed_polynomial_monic c.

(** Five distinct returned roots of this degree-five polynomial determine
    the whole polynomial, including multiplicities.  This small lemma keeps
    the exact factorization independent of the Lazard-specific construction. *)
Lemma lazard_general_output_factorization_of_sound_injective
    (K : fieldExtType rat) (roots : 'I_5 -> K)
    (hinjective : injective roots)
    (hsound : forall k : 'I_5,
      root (map_poly (in_alg K)
        (lazard_general_rational_polynomial c)) (roots k)) :
  lazard_general_rational_output_factorization c K roots.
Proof.
rewrite /lazard_general_rational_output_factorization.
have hlead :
    lead_coef (map_poly (in_alg K)
      (lazard_general_rational_polynomial c)) =
      in_alg K (GD.lazard_general_a c).
  by rewrite lead_coef_map lead_coefE
    (size_lazard_general_rational_polynomial c ha)
    /lazard_general_rational_polynomial coef_Poly.
rewrite -hlead.
apply: all_roots_prod_XsubC.
- by rewrite size_map_poly
    (size_lazard_general_rational_polynomial c ha)
    size_map size_enum_ord.
- rewrite all_map.
  apply/allP=> k _.
  exact: hsound k.
- rewrite uniq_rootsE map_inj_uniq ?enum_uniq //.
  exact: hinjective.
Qed.

Lemma lazard_general_output_package_of_depressed_package :
  RSA.lazard_rational_common_compositum_output_package p ->
  lazard_general_rational_output_package c.
Proof.
rewrite /RSA.lazard_rational_common_compositum_output_package
  /lazard_general_rational_output_package.
move=> [h [omega [q [i
  [homega [hradical [hmem
    [hinjective [hsound hcomplete]]]]]]]].
pose output := fun k : 'I_5 =>
  RSA.lazard_rational_common_alternate_output h omega i k -
    in_alg _ (GD.lazard_depression_shift c).
have houtput_injective : injective output.
  move=> j k hjk.
  apply: hinjective.
  apply: (addrI (- in_alg _ (GD.lazard_depression_shift c))).
  by rewrite !addrC -!subr_eq_add_opp.
have houtput_sound : forall k : 'I_5,
    root (map_poly (in_alg _)
      (lazard_general_rational_polynomial c)) (output k).
  move=> k.
  rewrite /output
    (@lazard_general_root_at_depressed_coordinate c ha _
      (in_alg _) (RSA.lazard_rational_common_alternate_output h omega i k)).
  exact: hsound k.
have houtput_factorization :
    lazard_general_rational_output_factorization c _ output.
  exact: lazard_general_output_factorization_of_sound_injective
    houtput_injective houtput_sound.
exists _, (RSA.lazard_rational_common_alternate_field h omega i),
  omega, output.
repeat split.
- exact: homega.
- exact: hradical.
- move=> k.
  apply: rpredB (hmem k).
  exact: RSA.lazard_rational_common_bottom_mem h omega i
    (GD.lazard_depression_shift c).
- exact: houtput_injective.
- exact: houtput_factorization.
- exact: houtput_sound.
- move=> z hz.
  have hzdep :
      root (map_poly (in_alg _)
        (lazard_general_depressed_polynomial c))
        (z + in_alg _ (GD.lazard_depression_shift c)).
    move: hz.
    by rewrite (@lazard_general_root_iff_depressed_coordinate c ha _
      (in_alg _) z).
  have [k hk] := hcomplete _ hzdep.
  exists k.
  by rewrite /output -hk addrK.
Qed.

(** Direct rational-resolvent entry point for an arbitrary nondegenerate
    rational quintic. *)
Theorem exists_lazard_general_rational_output_of_resolvent
    (p_irr : irreducible_poly
      (lazard_general_rational_polynomial c))
    (hq : lazard_general_rational_resolvent_has_root c) :
  lazard_general_rational_output_package c.
Proof.
apply: lazard_general_output_package_of_depressed_package.
apply: (@RSA.exists_lazard_rational_common_compositum_coherent_alternate_radical_tower
    p p_size p_monic).
- exact: (proj1 (lazard_general_irreducible_iff_depressed c ha)) p_irr.
- exact: lazard_general_depressed_polynomial_depressed c.
- exact: hq.
Qed.

(** Fully composed endpoint from the explicit radical-expression property
    of the *original*, possibly nonmonic and nondepressed, polynomial. *)
Theorem exists_lazard_general_rational_output_of_radical_formula
    (p_irr : irreducible_poly
      (lazard_general_rational_polynomial c))
    (p_radical : AR.radical_formula_solves
      (lazard_general_rational_polynomial c)) :
  lazard_general_rational_output_package c.
Proof.
apply: lazard_general_output_package_of_depressed_package.
apply: (@RSA.exists_lazard_rational_common_compositum_of_radical_formula
  p p_size p_monic).
- exact: (proj1 (lazard_general_irreducible_iff_depressed c ha)) p_irr.
- exact: lazard_general_depressed_polynomial_depressed c.
- exact: (proj1 (lazard_general_radical_formula_iff_depressed c ha))
    p_radical.
Qed.

(** Equivalent spelling using solvability of the actual Galois group of the
    original general polynomial.  The existing MathComp--Abel reflector
    first turns this into explicit [algterm rat] solvability; the preceding
    theorem then performs the honest affine transport. *)
Theorem exists_lazard_general_rational_output_of_galois_solvable
    (p_irr : irreducible_poly
      (lazard_general_rational_polynomial c))
    (p_solvable : solvable
      'Gal({:numfield (lazard_general_rational_polynomial c)} / 1%AS)) :
  lazard_general_rational_output_package c.
Proof.
apply: exists_lazard_general_rational_output_of_radical_formula p_irr.
exact: elimT
  (QRD.quintic_every_root_has_radical_expressionP
    (size_lazard_general_rational_polynomial c ha)) p_solvable.
Qed.

End GeneralComposition.

End PolynomialFormulasLazardQuinticGeneralRationalEndToEnd.
