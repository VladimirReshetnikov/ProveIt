From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardGeneralResolventExplicit LazardResolventMinPolyOrbit
  LazardSymmetricRationalGalois.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Concrete symmetric-rational specialization of Lazard's resolvent
    generator and minimal-polynomial clauses.

    [LazardSymmetricRationalGalois] constructs the extension

      K(e_1,...,e_n) <= K(X_1,...,X_n)

    as an actual MathComp splitting field and proves that its complete Galois
    group is the faithful permutation image of ['S_n].
    [LazardResolventMinPolyOrbit] proves abstractly that an element with exact
    relative stabilizer generates the corresponding fixed field and that its
    duplicate-free right-coset orbit product is its minimal polynomial.

    This file supplies the previously missing composition.  An invariant
    polynomial with exact formal stabilizer [G] is embedded in the concrete
    rational-function field; its Galois stabilizer is proved to be precisely
    the image of [G].  The mapped formal universal resolvent is then proved,
    rather than assumed, to be the ordinary minimal polynomial. *)
Module PolynomialFormulasLazardSymmetricRationalResolventBridge.

Import GRing.Theory.
Import FracField.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module GE := PolynomialFormulasLazardGeneralResolventExplicit.
Module RO := PolynomialFormulasLazardResolventMinPolyOrbit.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SRF := PolynomialFormulasLazardSymmetricRationalFunctions.
Module FE := PolynomialFormulasLazardSymmetricRationalFiniteExtension.
Module SG := PolynomialFormulasLazardSymmetricRationalGalois.

Section ConcreteBridge.

Variables (K : fieldType) (n : nat).

Local Notation MP := {mpoly K[n]}.
Local Notation ESRF :=
  (FE.lazard_elementary_symmetric_rational_field K n).
Local Notation RFE :=
  (FE.lazard_rational_function_extension K n).
Local Notation SplittingRFE :=
  (SG.lazard_symmetric_rational_splitting_field K n).
Local Notation FullRFE := ({:RFE} : {vspace RFE}).
Local Notation GalFull := (gal_of FullRFE).
Local Notation FullGal :=
  ('Gal(FullRFE / (1%VS : {vspace RFE}))%G).

(**************************************************************************)
(** * Exact stabilizer after passage to the concrete Galois extension *)

Definition lazard_fraction_invariant (p : MP) : RFE :=
  (@FracField.tofrac MP p).

Lemma lazard_fraction_invariant_injective :
  injective lazard_fraction_invariant.
Proof.
move=> p q hpq; apply/eqP.
rewrite -tofrac_eq.
exact/eqP: hpq.
Qed.

Lemma lazard_permutation_galois_fraction_invariantE
    (s : 'S_n) (p : MP) :
  SG.lazard_permutation_galois K n s
      (lazard_fraction_invariant p) =
    lazard_fraction_invariant (IM.mpoly_left_action s^-1 p).
Proof.
rewrite SG.lazard_permutation_galoisE
  FE.lazard_fraction_permutation_AEndE
  SRF.lazard_fraction_permutation_tofrac.
by [].
Qed.

Definition lazard_invariant_galois_subgroup (G : {group 'S_n}) :
    {group GalFull} :=
  (SG.lazard_permutation_galois_morphism K n @* G)%G.

Lemma lazard_permutation_galois_mem_invariant_subgroup
    (G : {group 'S_n}) (s : 'S_n) :
  (SG.lazard_permutation_galois K n s
      \in lazard_invariant_galois_subgroup G) = (s \in G).
Proof.
apply/idP/idP.
- move/morphimP=> [t tG hts].
  have -> : t = s.
    apply: SG.lazard_permutation_galois_injective.
    exact: hts.
  exact: tG.
- move=> sG; apply/morphimP; exists s; first exact: sG.
  by [].
Qed.

Lemma lazard_invariant_galois_subgroup_sub_full
    (G : {group 'S_n}) :
  lazard_invariant_galois_subgroup G \subset FullGal.
Proof.
apply/subsetP=> g /morphimP[s sG ->].
apply: (subsetP (SG.lazard_permutation_galois_image_sub_full K n)).
exact: SG.lazard_permutation_galois_mem_image.
Qed.

(** The full fixed field is literally the embedded elementary-symmetric
    rational-function field, represented by MathComp's base line [1]. *)
Theorem lazard_concrete_full_fixed_field :
  fixedField FullGal = (1%VS : {subfield RFE}).
Proof.
rewrite SG.lazard_full_symmetric_rational_galois_group.
exact: SG.lazard_permutation_galois_image_fixed_field.
Qed.

Variables (G : {group 'S_n}) (invariant : MP).
Hypothesis invariant_stabilizer_exact :
  @GE.lazard_invariant_stabilizer_exact K n G invariant.

Let GalG : {group GalFull} :=
  lazard_invariant_galois_subgroup G.
Let a : RFE := lazard_fraction_invariant invariant.

Lemma lazard_fraction_invariant_mem_full : a \in FullRFE.
Proof. exact: memvf. Qed.

(** Exact formal stabilizer survives both localization and the faithful
    isomorphism from permutations to Galois automorphisms. *)
Theorem lazard_concrete_relative_stabilizer_exact :
  forall g : GalFull, g \in FullGal -> (g a = a <-> g \in GalG).
Proof.
move=> g gFull.
rewrite SG.lazard_full_symmetric_rational_galois_group in gFull.
move/morphimP: gFull=> [s _ ->].
rewrite lazard_permutation_galois_fraction_invariantE
  lazard_permutation_galois_mem_invariant_subgroup.
split.
- move=> hlocalized.
  have hfixed : IM.mpoly_left_action s^-1 invariant = invariant :=
    lazard_fraction_invariant_injective hlocalized.
  have sinvG := (proj1 (invariant_stabilizer_exact s^-1)) hfixed.
  by rewrite groupV in sinvG.
- move=> sG.
  have sinvG : s^-1 \in G by rewrite groupV.
  have hfixed := (proj2 (invariant_stabilizer_exact s^-1)) sinvG.
  by rewrite hfixed.
Qed.

(**************************************************************************)
(** * The mapped formal orbit product *)

Definition lazard_formal_fraction_orbit_values : seq RFE :=
  map lazard_fraction_invariant
    (GC.lazard_orbit_value_sequence G
      (@GE.lazard_formal_orbit_value K n G invariant)).

Definition lazard_formal_fraction_resolvent : {poly RFE} :=
  \prod_(z <- lazard_formal_fraction_orbit_values) ('X - z%:P).

Lemma lazard_formal_fraction_resolventE :
  map_poly (@FracField.tofrac MP)
      (@GE.lazard_paper_universal_invariant_resolvent
        K n G invariant) =
    lazard_formal_fraction_resolvent.
Proof.
rewrite /GE.lazard_paper_universal_invariant_resolvent
  /GE.lazard_universal_invariant_resolvent
  /GC.lazard_orbit_resolvent map_prod_XsubC
  /lazard_formal_fraction_resolvent
  /lazard_formal_fraction_orbit_values.
by rewrite big_map.
Qed.

Lemma lazard_formal_fraction_orbit_values_uniq :
  uniq lazard_formal_fraction_orbit_values.
Proof.
rewrite /lazard_formal_fraction_orbit_values
  (map_inj_uniq lazard_fraction_invariant_injective).
exact: (@GE.lazard_formal_orbit_conjugates_uniq_of_exact_stabilizer
  K n G invariant invariant_stabilizer_exact).
Qed.

Lemma lazard_embedded_formal_value_is_minPoly_root
    (C : {set 'S_n}) :
  root (minPoly (fixedField FullGal) a)
    (lazard_fraction_invariant
      (@GE.lazard_formal_orbit_value K n G invariant C)).
Proof.
have hvalue :
    SG.lazard_permutation_galois K n (repr C) a =
      lazard_fraction_invariant
        (@GE.lazard_formal_orbit_value K n G invariant C).
  by rewrite lazard_permutation_galois_fraction_invariantE.
rewrite -hvalue.
apply: root_minPoly_gal (fixedField_bound FullGal) _
  lazard_fraction_invariant_mem_full.
rewrite gal_fixedField.
apply: (subsetP (SG.lazard_permutation_galois_image_sub_full K n)).
exact: SG.lazard_permutation_galois_mem_image.
Qed.

Lemma lazard_formal_fraction_orbit_values_are_minPoly_roots :
  all (root (minPoly (fixedField FullGal) a))
    lazard_formal_fraction_orbit_values.
Proof.
rewrite /lazard_formal_fraction_orbit_values
  /GC.lazard_orbit_value_sequence.
apply/allP=> z /mapP[p p_mem ->].
move/mapP: p_mem=> [C Cenum ->].
exact: lazard_embedded_formal_value_is_minPoly_root.
Qed.

Lemma lazard_formal_fraction_resolvent_dvd_minPoly :
  lazard_formal_fraction_resolvent %|
    minPoly (fixedField FullGal) a.
Proof.
rewrite /lazard_formal_fraction_resolvent.
apply: uniq_roots_dvdp.
- exact: lazard_formal_fraction_orbit_values_are_minPoly_roots.
- by rewrite uniq_rootsE; exact: lazard_formal_fraction_orbit_values_uniq.
Qed.

(**************************************************************************)
(** * Degree comparison and the final equalities *)

Lemma lazard_invariant_galois_subgroup_card :
  #|GalG| = #|G|.
Proof.
rewrite /GalG /lazard_invariant_galois_subgroup.
rewrite (card_injm (SG.lazard_permutation_galois_injm K n)) ?subsetT //.
Qed.

Lemma lazard_concrete_relative_index :
  #|FullGal : GalG| = #|[set: 'S_n] : G|.
Proof.
rewrite /indexg lazard_invariant_galois_subgroup_card
  SG.lazard_full_symmetric_rational_galois_group_card
  cardsT card_Sn.
by [].
Qed.

Lemma lazard_formal_fraction_resolvent_size :
  size lazard_formal_fraction_resolvent =
    #|[set: 'S_n] : G|.+1.
Proof.
rewrite /lazard_formal_fraction_resolvent size_prod_XsubC
  /lazard_formal_fraction_orbit_values size_map
  /GC.lazard_orbit_value_sequence size_map -cardE
  /GC.lazard_right_coset_orbit /indexg.
by [].
Qed.

Lemma lazard_concrete_adjoin_degree :
  adjoin_degree (fixedField FullGal) a = #|FullGal : GalG|.
Proof.
exact: (@RO.lazard_relative_adjoin_degree
  ESRF SplittingRFE FullRFE FullGal GalG
  (lazard_invariant_galois_subgroup_sub_full G)
  a lazard_fraction_invariant_mem_full
  lazard_concrete_relative_stabilizer_exact).
Qed.

Lemma lazard_concrete_minPoly_size :
  size (minPoly (fixedField FullGal) a) =
    #|FullGal : GalG|.+1.
Proof.
by rewrite size_minPoly lazard_concrete_adjoin_degree.
Qed.

(** The mapped universal invariant resolvent is now an actual
    minimal-polynomial theorem, not a supplied certificate. *)
Theorem lazard_formal_fraction_resolvent_is_minPoly :
  lazard_formal_fraction_resolvent =
    minPoly (fixedField FullGal) a.
Proof.
apply/eqP.
rewrite -eqp_monic ?monic_prod_XsubC ?monic_minPoly //.
rewrite -(dvdp_size_eqp lazard_formal_fraction_resolvent_dvd_minPoly).
rewrite lazard_formal_fraction_resolvent_size
  lazard_concrete_minPoly_size lazard_concrete_relative_index.
exact: eqxx.
Qed.

Theorem lazard_paper_universal_resolvent_map_is_minPoly :
  map_poly (@FracField.tofrac MP)
      (@GE.lazard_paper_universal_invariant_resolvent
        K n G invariant) =
    minPoly (fixedField FullGal) a.
Proof.
rewrite lazard_formal_fraction_resolventE.
exact: lazard_formal_fraction_resolvent_is_minPoly.
Qed.

(** The same concrete invariant generates the complete subgroup-fixed
    rational-function field. *)
Theorem lazard_fraction_invariant_generates_fixedField :
  <<fixedField FullGal; a>>%AS = fixedField GalG.
Proof.
exact: (@RO.lazard_relative_generates_fixedField
  ESRF SplittingRFE FullRFE FullGal GalG
  (lazard_invariant_galois_subgroup_sub_full G)
  a lazard_fraction_invariant_mem_full
  lazard_concrete_relative_stabilizer_exact).
Qed.

(** Complete paper-facing bridge: elementary-symmetric base field,
    fixed-field generation, and ordinary minimal polynomial. *)
Theorem lazard_symmetric_rational_resolvent_bridge :
  [/
    fixedField FullGal = (1%VS : {subfield RFE}),
    <<fixedField FullGal; a>>%AS = fixedField GalG
  & map_poly (@FracField.tofrac MP)
      (@GE.lazard_paper_universal_invariant_resolvent
        K n G invariant) =
    minPoly (fixedField FullGal) a
  ].
Proof.
split.
- exact: lazard_concrete_full_fixed_field.
- exact: lazard_fraction_invariant_generates_fixedField.
- exact: lazard_paper_universal_resolvent_map_is_minPoly.
Qed.

End ConcreteBridge.

(**************************************************************************)
(** * Converse in the concrete symmetric rational-function presentation *)

(** The abstract converse in [LazardResolventMinPolyOrbit] is phrased for
    an element of an arbitrary finite Galois extension.  The following
    section transports that converse back through the faithful
    ['S_n]-presentation constructed above.  Consequently the literal
    generator/minimal-polynomial definition used by Lazard is equivalent to
    the exact *formal polynomial* stabilizer; the latter is no longer an
    extra certificate when one starts from the literal definition. *)
Section ConcreteBridgeConverse.

Variables (K : fieldType) (n : nat).

Local Notation MP := {mpoly K[n]}.
Local Notation ESRF :=
  (FE.lazard_elementary_symmetric_rational_field K n).
Local Notation RFE :=
  (FE.lazard_rational_function_extension K n).
Local Notation SplittingRFE :=
  (SG.lazard_symmetric_rational_splitting_field K n).
Local Notation FullRFE := ({:RFE} : {vspace RFE}).
Local Notation GalFull := (gal_of FullRFE).
Local Notation FullGal :=
  ('Gal(FullRFE / (1%VS : {vspace RFE}))%G).

Variables (G : {group 'S_n}) (invariant : MP).

Let GalG : {group GalFull} :=
  lazard_invariant_galois_subgroup K n G.
Let a : RFE := lazard_fraction_invariant K n invariant.

(** Lazard's literal definition in the concrete elementary-symmetric
    rational-function field.  The first conjunct records the concrete base
    field, while the last two are respectively the generator and ordinary
    minimal-polynomial clauses. *)
Definition lazard_concrete_literal_resolvent_definition : Prop :=
  [/
    fixedField FullGal = (1%VS : {subfield RFE}),
    <<fixedField FullGal; a>>%AS = fixedField GalG
  & map_poly (@FracField.tofrac MP)
      (@GE.lazard_paper_universal_invariant_resolvent
        K n G invariant) =
    minPoly (fixedField FullGal) a
  ].

(** Concrete converse and forward bridge in one statement.  The reverse
    implication uses only the generator conjunct: Galois correspondence
    recovers the stabilizer of the localized invariant, and injectivity of
    polynomial localization then recovers the exact renaming stabilizer of
    the original multivariate polynomial. *)
Theorem lazard_invariant_stabilizer_exact_iff_literal_definition :
  @GE.lazard_invariant_stabilizer_exact K n G invariant <->
  lazard_concrete_literal_resolvent_definition.
Proof.
split.
- move=> exact_stabilizer.
  exact: (@lazard_symmetric_rational_resolvent_bridge
    K n G invariant exact_stabilizer).
- move=> [_ generates _].
  have relative_exact :
      @RO.lazard_relative_stabilizer_exact
        ESRF SplittingRFE FullRFE FullGal GalG a :=
    (proj2
      (@RO.lazard_relative_stabilizer_exact_iff_generates_fixedField
        ESRF SplittingRFE FullRFE FullGal GalG
        (lazard_invariant_galois_subgroup_sub_full K n G)
        a (memvf a))) generates.
  move=> s; split.
  + move=> sinvariant.
    have gFull :
        SG.lazard_permutation_galois K n s^-1 \in FullGal.
      apply: (subsetP
        (SG.lazard_permutation_galois_image_sub_full K n)).
      exact: SG.lazard_permutation_galois_mem_image.
    have gfix :
        SG.lazard_permutation_galois K n s^-1 a = a.
      rewrite /a
        lazard_permutation_galois_fraction_invariantE invgK
        sinvariant.
      exact: erefl.
    have gG := (proj1 (relative_exact _ gFull)) gfix.
    move: gG.
    by rewrite /GalG
      lazard_permutation_galois_mem_invariant_subgroup groupV.
  + move=> sG.
    have sinvG : s^-1 \in G by rewrite groupV.
    have gG :
        SG.lazard_permutation_galois K n s^-1 \in GalG.
      by rewrite /GalG
        lazard_permutation_galois_mem_invariant_subgroup.
    have gFull :
        SG.lazard_permutation_galois K n s^-1 \in FullGal.
      apply: (subsetP
        (SG.lazard_permutation_galois_image_sub_full K n)).
      exact: SG.lazard_permutation_galois_mem_image.
    have gfix := (proj2 (relative_exact _ gFull)) gG.
    rewrite /a lazard_permutation_galois_fraction_invariantE
      invgK in gfix.
    exact: (lazard_fraction_invariant_injective K n gfix).
Qed.

End ConcreteBridgeConverse.

End PolynomialFormulasLazardSymmetricRationalResolventBridge.
