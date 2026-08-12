From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A finite-Galois version of the missing minimal-polynomial part of
    Lazard's definition of a resolvent invariant.

    This module deliberately starts *after* the rational-function-field
    construction.  In a finite Galois extension [E / fixedField H], an
    element [a] whose stabilizer in [H] is exactly [G] does generate
    [fixedField G] over [fixedField H].  Its minimal polynomial is the
    product of its distinct conjugates indexed by the right cosets [G\H].

    Thus exact stabilizer is not being renamed as Lazard's definition here:
    the fixed-field generation and minimal-polynomial conclusions are proved
    from it using MathComp's fundamental theorem of Galois theory.  The
    companion [LazardSymmetricRationalResolventBridge] supplies the separate
    construction and specializes this theorem to Lazard's universal
    rational-function invariant. *)
Module PolynomialFormulasLazardResolventMinPolyOrbit.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Section RelativeOrbit.

Variables (F : fieldType) (L : splittingFieldType F).
Variable E : {subfield L}.
Variables (H G : {group gal_of E}).
Hypothesis G_sub_H : G \subset H.
Variable a : L.
Hypothesis a_mem_E : a \in E.

(** The exact stabilizer hypothesis, stated only inside the ambient group
    [H].  It is the hypothesis from which the actual fixed-field-generator
    statement will be derived below. *)
Definition lazard_relative_stabilizer_exact : Prop :=
  forall s : gal_of E, s \in H -> (s a = a <-> s \in G).

Hypothesis stabilizer_exact : lazard_relative_stabilizer_exact.

(** MathComp composes [gal_of] elements in the order
    [(x * y) a = y (x a)].  Consequently an orbit value is constant on a
    right coset [G :* x], exactly as in Lazard's convention. *)
Definition lazard_relative_orbit_value (C : {set gal_of E}) : L :=
  repr C a.

Definition lazard_relative_orbit_values : seq L :=
  map lazard_relative_orbit_value (enum (rcosets G H)).

Definition lazard_relative_orbit_resolvent : {poly L} :=
  \prod_(z <- lazard_relative_orbit_values) ('X - z%:P).

Lemma lazard_relative_orbit_value_rcoset x :
  x \in H -> lazard_relative_orbit_value (G :* x) = x a.
Proof.
move=> xH; rewrite /lazard_relative_orbit_value.
case: repr_rcosetP=> g gG.
rewrite galM //.
have gH : g \in H := subsetP G_sub_H g gG.
have ga : g a = a := (proj2 (stabilizer_exact g gH)) gG.
by rewrite ga.
Qed.

Lemma lazard_relative_repr_mem C :
  C \in rcosets G H -> repr C \in H.
Proof.
case/rcosetsP=> x xH ->.
case: repr_rcosetP=> g gG.
by rewrite groupM // (subsetP G_sub_H g gG).
Qed.

(** Exact stabilizer makes the canonical orbit values collision-free. *)
Lemma lazard_relative_orbit_value_injective :
  {in rcosets G H &, injective lazard_relative_orbit_value}.
Proof.
move=> C D Cmem Dmem hCD.
have rCH : repr C \in H := lazard_relative_repr_mem Cmem.
have rDH : repr D \in H := lazard_relative_repr_mem Dmem.
have rCrDV_H : repr C * (repr D)^-1 \in H.
  by rewrite groupM // groupV.
have rCrDV_fix : (repr C * (repr D)^-1)%g a = a.
  rewrite galM //.
  rewrite /lazard_relative_orbit_value in hCD.
  rewrite hCD -galM // mulgV gal_id.
have rCrDV_G : repr C * (repr D)^-1 \in G :=
  (proj1 (stabilizer_exact _ rCrDV_H)) rCrDV_fix.
have coset_eq : G :* repr C = G :* repr D.
  apply/rcoset_eqP/rcosetP.
  exists (repr C * (repr D)^-1); first exact: rCrDV_G.
  by rewrite mulgA mulVg mulg1.
have C_repr : G :* repr C = C.
  case/rcosetsP: Cmem=> x _ ->.
  exact: rcoset_repr x.
have D_repr : G :* repr D = D.
  case/rcosetsP: Dmem=> x _ ->.
  exact: rcoset_repr x.
exact: (etrans (esym C_repr) (etrans coset_eq D_repr)).
Qed.

Lemma lazard_relative_orbit_values_uniq :
  uniq lazard_relative_orbit_values.
Proof.
rewrite /lazard_relative_orbit_values.
apply/dinjectiveP.
exact: lazard_relative_orbit_value_injective.
Qed.

(** Every listed orbit value is a conjugate root of the minimal polynomial
    over the [H]-fixed field. *)
Lemma lazard_relative_orbit_values_are_minPoly_roots :
  all (root (minPoly (fixedField H) a)) lazard_relative_orbit_values.
Proof.
rewrite /lazard_relative_orbit_values.
apply/allP=> z /mapP[C Cenum ->].
have Cmem : C \in rcosets G H by move: Cenum; rewrite mem_enum.
apply: root_minPoly_gal (fixedField_bound H) _ a_mem_E.
by rewrite gal_fixedField; exact: lazard_relative_repr_mem Cmem.
Qed.

Lemma lazard_relative_orbit_resolvent_dvd_minPoly :
  lazard_relative_orbit_resolvent %|
    minPoly (fixedField H) a.
Proof.
rewrite /lazard_relative_orbit_resolvent.
apply: uniq_roots_dvdp.
- exact: lazard_relative_orbit_values_are_minPoly_roots.
- by rewrite uniq_rootsE; exact: lazard_relative_orbit_values_uniq.
Qed.

(** The element lies in the [G]-fixed field, so adjoining it to the
    [H]-fixed field gives a subfield of [fixedField G]. *)
Lemma lazard_relative_element_mem_fixedField :
  a \in fixedField G.
Proof.
apply/fixedFieldP=> // s sG.
have sH : s \in H := subsetP G_sub_H s sG.
exact: (proj2 (stabilizer_exact s sH)) sG.
Qed.

Lemma lazard_relative_adjoin_sub_fixedField :
  (<<fixedField H; a>> <= fixedField G)%VS.
Proof.
apply/FadjoinP; split.
- exact: fixedFieldS G_sub_H.
- exact: lazard_relative_element_mem_fixedField.
Qed.

Lemma lazard_relative_fixedField_dimension :
  \dim_(fixedField H) (fixedField G) = #|H : G|.
Proof.
have G_sub_gal : G \subset 'Gal(E / fixedField H).
  by rewrite gal_fixedField.
have hdim := dim_fixed_galois (fixedField_galois H) G_sub_gal.
by rewrite gal_fixedField in hdim.
Qed.

Lemma lazard_relative_adjoin_degree_le_index :
  adjoin_degree (fixedField H) a <= #|H : G|.
Proof.
rewrite adjoin_degreeE.
apply: leq_trans
  (leq_div2r (dimvS lazard_relative_adjoin_sub_fixedField)).
by rewrite lazard_relative_fixedField_dimension.
Qed.

Lemma lazard_relative_index_le_adjoin_degree :
  #|H : G| <= adjoin_degree (fixedField H) a.
Proof.
have hle := dvdp_leq (monic_neq0 (monic_minPoly (fixedField H) a))
  lazard_relative_orbit_resolvent_dvd_minPoly.
move: hle.
rewrite /lazard_relative_orbit_resolvent size_prod_XsubC
  /lazard_relative_orbit_values size_map -cardE
  /indexg size_minPoly.
by [].
Qed.

Lemma lazard_relative_adjoin_degree :
  adjoin_degree (fixedField H) a = #|H : G|.
Proof.
apply/eqP.
by rewrite eqn_leq lazard_relative_adjoin_degree_le_index
  lazard_relative_index_le_adjoin_degree.
Qed.

(** This is the literal fixed-field-generation clause in Lazard's
    definition, in the finite-Galois setting. *)
Theorem lazard_relative_generates_fixedField :
  <<fixedField H; a>>%AS = fixedField G.
Proof.
apply/eqP; rewrite eqEdim lazard_relative_adjoin_sub_fixedField /=.
rewrite (dim_sup_field (subv_adjoin (fixedField H) a)).
rewrite (dim_sup_field (fixedFieldS G_sub_H)).
rewrite -adjoin_degreeE lazard_relative_adjoin_degree.
by rewrite lazard_relative_fixedField_dimension.
Qed.

(** This is the literal minimal-polynomial clause: the orbit product, not
    merely an arbitrary polynomial with the same roots, is the minimal
    polynomial over the [H]-fixed field. *)
Theorem lazard_relative_orbit_resolvent_is_minPoly :
  lazard_relative_orbit_resolvent = minPoly (fixedField H) a.
Proof.
apply/eqP.
rewrite -eqp_monic ?monic_prod_XsubC ?monic_minPoly //.
rewrite -(dvdp_size_eqp lazard_relative_orbit_resolvent_dvd_minPoly).
rewrite /lazard_relative_orbit_resolvent size_prod_XsubC
  /lazard_relative_orbit_values size_map -cardE
  /indexg size_minPoly lazard_relative_adjoin_degree.
exact: eqxx.
Qed.

Theorem lazard_relative_generator_and_minPoly :
  <<fixedField H; a>>%AS = fixedField G /\
  lazard_relative_orbit_resolvent = minPoly (fixedField H) a.
Proof.
split.
- exact: lazard_relative_generates_fixedField.
- exact: lazard_relative_orbit_resolvent_is_minPoly.
Qed.

End RelativeOrbit.

Section RelativeOrbitConverse.

Variables (F : fieldType) (L : splittingFieldType F).
Variable E : {subfield L}.
Variables (H G : {group gal_of E}).
Hypothesis G_sub_H : G \subset H.
Variable a : L.
Hypothesis a_mem_E : a \in E.

(** Literal converse to the generator clause.  The reverse implication is
    proved from the generated-field equality: an element of [H] fixing [a]
    fixes every polynomial expression in [a], hence the whole simple
    extension, and [gal_fixedField] then identifies it with an element of
    [G]. *)
Theorem lazard_relative_stabilizer_exact_iff_generates_fixedField :
  @lazard_relative_stabilizer_exact F L E H G a <->
  <<fixedField H; a>>%AS = fixedField G.
Proof.
split.
- move=> stabilizer_exact.
  exact: (@lazard_relative_generates_fixedField
    F L E H G G_sub_H a a_mem_E stabilizer_exact).
- move=> generates s sH; split.
  + move=> sa.
    have adjoin_sub_E :
        (<<fixedField H; a>> <= E)%VS.
      by apply/FadjoinP; split; [exact: fixedField_bound H | exact: a_mem_E].
    have sGalH : s \in 'Gal(E / fixedField H).
      by rewrite gal_fixedField.
    have sGalAdjoin : s \in 'Gal(E / <<fixedField H; a>>).
      rewrite gal_kHom //.
      apply/kAHomP=> z /Fadjoin_polyP[p pH ->].
      by rewrite -horner_map
        (fixedPoly_gal (fixedField_bound H) sGalH pH) /= sa.
    move: sGalAdjoin.
    by rewrite generates gal_fixedField.
  + move=> sG.
    have aG : a \in fixedField G.
      rewrite -generates.
      exact: memv_adjoin.
    have sGalG : s \in 'Gal(E / fixedField G).
      by rewrite gal_fixedField.
    exact: (fixed_gal (fixedField_bound G) sGalG aG).
Qed.

(** Lazard's generator and minimal-polynomial clauses, bundled as an iff.
    The minimal-polynomial conjunct is redundant in the reverse direction:
    the generator equality alone recovers the exact stabilizer by the
    preceding theorem. *)
Theorem lazard_relative_stabilizer_exact_iff_generator_and_minPoly :
  @lazard_relative_stabilizer_exact F L E H G a <->
  <<fixedField H; a>>%AS = fixedField G /\
  @lazard_relative_orbit_resolvent F L E H G a =
    minPoly (fixedField H) a.
Proof.
split.
- move=> stabilizer_exact.
  exact: (@lazard_relative_generator_and_minPoly
    F L E H G G_sub_H a a_mem_E stabilizer_exact).
- move=> [generates _].
  exact: (proj2
    (@lazard_relative_stabilizer_exact_iff_generates_fixedField
      F L E H G G_sub_H a a_mem_E) generates).
Qed.

End RelativeOrbitConverse.

End PolynomialFormulasLazardResolventMinPolyOrbit.
