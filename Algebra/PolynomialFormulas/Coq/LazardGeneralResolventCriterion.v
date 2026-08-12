From HB Require Import structures.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The group-theoretic core of Lazard's general resolvent criterion.

    The ambient group [H] of the paper is represented here by the finite
    group type [hT]; an arbitrary inclusion [G <= H] is therefore obtained
    by taking [hT] to be the subtype of [H] and [G] to be a subgroup of it.
    The roots of the specialized resolvent are indexed by the right cosets
    [G :* x].  MathComp's right-translation action proves, rather than
    assumes, that the stabilizer of this coset is the conjugate [G :^ x].

    The interface below asks only for the data used by the proof:

    - fixed elements are exactly the image of the base field;
    - the specialized orbit values are equivariant;
    - the base-field resolvent becomes the product over those values; and
    - for the converse, the specialized values are collision-free.

    The last condition is derived separately from separability of the
    resolvent, matching the second implication in Lazard's Theorem 1. *)
Module PolynomialFormulasLazardGeneralResolventCriterion.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Section RightCosetOrbit.

Variable hT : finGroupType.
Variable G : {group hT}.

(** The homogeneous space [H / G], represented by all right cosets of [G]
    in the full ambient finite group [hT]. *)
Definition lazard_right_coset_orbit : {set {set hT}} :=
  rcosets G [set : hT].

Lemma lazard_right_coset_mem x :
  G :* x \in lazard_right_coset_orbit.
Proof.
apply/rcosetsP; exists x; first by rewrite inE.
exact: erefl.
Qed.

Lemma lazard_right_coset_action_mem C x :
  C \in lazard_right_coset_orbit ->
  C :* x \in lazard_right_coset_orbit.
Proof.
case/rcosetsP=> y _ ->.
rewrite -rcosetM.
exact: lazard_right_coset_mem (y * x).
Qed.

End RightCosetOrbit.

Section OrbitPolynomial.

Variables (L : fieldType) (hT : finGroupType).
Variable G : {group hT}.
Variable value : {set hT} -> L.

Definition lazard_orbit_value_sequence : seq L :=
  map value (enum (lazard_right_coset_orbit G)).

Definition lazard_orbit_resolvent : {poly L} :=
  \prod_(z <- lazard_orbit_value_sequence) ('X - z%:P).

Lemma lazard_orbit_resolvent_rootP z :
  reflect
    (exists2 C, C \in lazard_right_coset_orbit G & value C = z)
    (root lazard_orbit_resolvent z).
Proof.
rewrite /lazard_orbit_resolvent root_prod_XsubC.
apply: (iffP idP).
- move/mapP=> [C Cmem value_z].
  exists C; last exact: esym value_z.
  by move: Cmem; rewrite mem_enum.
- move=> [C Cmem value_z].
  apply/mapP; exists C; last exact: esym value_z.
  by rewrite mem_enum.
Qed.

End OrbitPolynomial.

Section GeneralCriterion.

Variables (K L : fieldType) (gammaT hT : finGroupType).
Variable embed : {rmorphism K -> L}.
Variable Gamma : {group gammaT}.
Variable G : {group hT}.
Variable rho : gammaT -> hT.
Variable sigma : gammaT -> {rmorphism L -> L}.
Variable value : {set hT} -> L.
Variable R : {poly K}.

(** Abstract fixed-field descent.  In the intended application [Gamma] is
    the Galois group of a splitting field, [sigma] is its field action, and
    this equivalence is the fixed-field theorem. *)
Hypothesis base_fixed_iff : forall z : L,
  ((forall gamma : gammaT, gamma \in Gamma -> sigma gamma z = z) <->
    exists q : K, z = embed q).

(** Compatibility between the Galois action on values and the induced
    permutation [rho] of the roots. *)
Hypothesis orbit_value_equivariant :
  forall (gamma : gammaT) (C : {set hT}),
    gamma \in Gamma ->
    C \in lazard_right_coset_orbit G ->
    sigma gamma (value C) = value (C :* rho gamma).

(** Specialization of the universal resolvent: after extending scalars,
    its roots are exactly the values on the finite coset orbit. *)
Hypothesis resolvent_factorization :
  map_poly embed R = lazard_orbit_resolvent G value.

(** Lazard Theorem 1, forward direction, with the honest conjugate
    conclusion made explicit in the hypothesis.  No separability is used. *)
Theorem lazard_resolvent_has_base_root_of_image_sub_conjugate x :
  rho @: Gamma \subset G :^ x ->
  exists q : K, root R q.
Proof.
move=> image_sub.
have coset_mem : G :* x \in lazard_right_coset_orbit G :=
  @lazard_right_coset_mem hT G x.
have coset_fixed : G :* x \in 'Fix_('Rs)(rho @: Gamma).
  by rewrite sub_afixRs_norms.
have value_fixed : forall gamma : gammaT, gamma \in Gamma ->
    sigma gamma (value (G :* x)) = value (G :* x).
  move=> gamma gamma_mem.
  rewrite (@orbit_value_equivariant gamma (G :* x) gamma_mem coset_mem).
  have rho_mem : rho gamma \in rho @: Gamma.
    apply/imsetP; by exists gamma.
  have coset_act : G :* x :* rho gamma = G :* x.
    move: (elimT afixP coset_fixed _ rho_mem).
    by rewrite /= rcosetE.
  by rewrite coset_act.
have [q value_q] :=
  (proj1 (base_fixed_iff (value (G :* x))) value_fixed).
exists q.
rewrite -(mapf_root embed R q) resolvent_factorization
  /lazard_orbit_resolvent /lazard_orbit_value_sequence
  root_prod_XsubC.
apply/mapP; exists (G :* x).
- by rewrite mem_enum.
- exact: esym value_q.
Qed.

(** The literal [image <= G] form is the base-coset instance of the
    conjugate statement. *)
Corollary lazard_resolvent_has_base_root_of_image_sub_group :
  rho @: Gamma \subset G ->
  exists q : K, root R q.
Proof.
move=> image_sub.
apply: (@lazard_resolvent_has_base_root_of_image_sub_conjugate 1).
by rewrite conjsg1.
Qed.

(** Converse with the exact collision-free hypothesis needed in the proof.
    A rational root selects one coset; equivariance and injectivity force the
    whole image of [Gamma] to fix it, and MathComp identifies that stabilizer
    with a conjugate of [G]. *)
Theorem lazard_image_sub_conjugate_of_resolvent_has_base_root
    (orbit_values_injective :
      {in lazard_right_coset_orbit G &, injective value}) :
  (exists q : K, root R q) ->
  exists x : hT, rho @: Gamma \subset G :^ x.
Proof.
move=> [q root_q].
have root_map : root (map_poly embed R) (embed q).
  by rewrite (mapf_root embed R q) root_q.
rewrite resolvent_factorization /lazard_orbit_resolvent
  /lazard_orbit_value_sequence root_prod_XsubC in root_map.
case/mapP: root_map=> C C_enum value_q.
have C_mem : C \in lazard_right_coset_orbit G.
  by move: C_enum; rewrite mem_enum.
case/rcosetsP: C_mem=> x _ C_eq; subst C.
exists x.
rewrite -sub_afixRs_norms.
apply/afixP=> _ /imsetP[gamma gamma_mem ->].
rewrite /= rcosetE.
apply: orbit_values_injective.
- rewrite -rcosetM.
  exact: (@lazard_right_coset_mem hT G (x * rho gamma)).
- exact: (@lazard_right_coset_mem hT G x).
- rewrite -(@orbit_value_equivariant gamma (G :* x) gamma_mem
    (@lazard_right_coset_mem hT G x)).
  have value_base : exists q0 : K, value (G :* x) = embed q0.
    exists q.
    exact: esym value_q.
  exact: (proj2 (base_fixed_iff (value (G :* x))) value_base
    gamma gamma_mem).
Qed.

(** The polynomial separability premise in Lazard's statement implies the
    collision-free value hypothesis because the specialized factorization is
    a product of linear factors indexed by all cosets. *)
Lemma lazard_orbit_values_injective_of_resolvent_separable
    (R_separable : separable_poly R) :
  {in lazard_right_coset_orbit G &, injective value}.
Proof.
apply/dinjectiveP.
rewrite /dinjectiveb.
move: R_separable.
by rewrite -(separable_map embed) resolvent_factorization
  /lazard_orbit_resolvent /lazard_orbit_value_sequence
  separable_prod_XsubC.
Qed.

(** The complete abstract criterion.  An unspecified base-field root can
    identify any coset, so the correct conclusion is containment in some
    conjugate of [G], equivalently a relabeling of the roots. *)
Theorem lazard_resolvent_has_base_root_iff_image_sub_conjugate
    (R_separable : separable_poly R) :
  (exists q : K, root R q) <->
  exists x : hT, rho @: Gamma \subset G :^ x.
Proof.
split.
- apply: lazard_image_sub_conjugate_of_resolvent_has_base_root.
  exact: lazard_orbit_values_injective_of_resolvent_separable.
- move=> [x image_sub].
  exact: lazard_resolvent_has_base_root_of_image_sub_conjugate image_sub.
Qed.

End GeneralCriterion.

(** A concrete fixed-field adapter for MathComp's bundled Galois theory.

    Here the coefficient field is the field type carried by the subfield
    [K], and the value field is the field type carried by [E].  Thus every
    resolvent value is bundled together with its proof of membership in the
    extension field.  The restricted action below has underlying value
    [g z]; the only extra work is to re-bundle [g z] in [E], using
    [memv_gal].  Consequently the fixed-element condition required by the
    abstract criterion is not an additional certificate: it follows from
    [galois_fixedField]. *)
Section MathCompGaloisAdapter.

Variables (F : fieldType) (L : splittingFieldType F).
Variables (K E : {subfield L}).
Hypothesis galois_K_E : galois K E.

Let sub_K_E : (K <= E)%VS.
Proof.
have /and3P [sKE _ _] := galois_K_E.
exact: sKE.
Qed.

Definition lazard_base_embedding_fun (q : subvs_of K) : subvs_of E :=
  Subvs ((subvP sub_K_E) (val q) (valP q)).

Lemma lazard_base_embedding_zmod_morphism :
  zmod_morphism lazard_base_embedding_fun.
Proof. by move=> x y; apply: val_inj. Qed.

Lemma lazard_base_embedding_monoid_morphism :
  monoid_morphism lazard_base_embedding_fun.
Proof.
split.
- apply: val_inj.
  by rewrite /lazard_base_embedding_fun /= !algid1.
- move=> x y.
  apply: val_inj.
  by rewrite /lazard_base_embedding_fun /=.
Qed.

Definition lazard_base_embedding :
    {rmorphism subvs_of K -> subvs_of E} :=
  HB.pack lazard_base_embedding_fun
    (GRing.isZmodMorphism.Build _ _ lazard_base_embedding_fun
      lazard_base_embedding_zmod_morphism)
    (GRing.isMonoidMorphism.Build _ _ lazard_base_embedding_fun
      lazard_base_embedding_monoid_morphism).

Lemma lazard_base_embeddingE (q : subvs_of K) :
  val (lazard_base_embedding q) = val q.
Proof. by []. Qed.

Definition lazard_galois_action_fun
    (g : gal_of E) (z : subvs_of E) : subvs_of E :=
  Subvs (memv_gal g (valP z)).

Lemma lazard_galois_action_zmod_morphism (g : gal_of E) :
  zmod_morphism (lazard_galois_action_fun g).
Proof. by move=> x y; apply: val_inj; rewrite /= rmorphB. Qed.

Lemma lazard_galois_action_monoid_morphism (g : gal_of E) :
  monoid_morphism (lazard_galois_action_fun g).
Proof.
split.
- apply: val_inj.
  by rewrite /lazard_galois_action_fun /= !algid1 rmorph1.
- move=> x y; apply: val_inj.
  by rewrite /lazard_galois_action_fun /= rmorphM.
Qed.

Definition lazard_galois_action (g : gal_of E) :
    {rmorphism subvs_of E -> subvs_of E} :=
  HB.pack (lazard_galois_action_fun g)
    (GRing.isZmodMorphism.Build _ _ (lazard_galois_action_fun g)
      (lazard_galois_action_zmod_morphism g))
    (GRing.isMonoidMorphism.Build _ _ (lazard_galois_action_fun g)
      (lazard_galois_action_monoid_morphism g)).

Lemma lazard_galois_actionE (g : gal_of E) (z : subvs_of E) :
  val (lazard_galois_action g z) = g (val z).
Proof. by []. Qed.

(** Standard Galois descent for an element of [E].  In the forward
    direction [fixedFieldP] puts its underlying value in the fixed field,
    [galois_fixedField] identifies that field with [K], and [Subvs] bundles
    the resulting membership proof as an actual coefficient. *)
Theorem lazard_galois_base_fixed_iff (z : subvs_of E) :
  ((forall g : gal_of E, g \in 'Gal(E / K)%G ->
      lazard_galois_action g z = z) <->
    exists q : subvs_of K, z = lazard_base_embedding q).
Proof.
split.
- move=> fixed_z.
  have z_fixed_field : val z \in fixedField 'Gal(E / K)%G.
    apply/fixedFieldP; first exact: valP z.
    move=> g gEK.
    have hfixed := congr1 val (fixed_z g gEK).
    by rewrite lazard_galois_actionE in hfixed.
  have fixed_fieldE : fixedField 'Gal(E / K)%G = K.
    exact: (elimT galois_fixedField galois_K_E).
  rewrite fixed_fieldE in z_fixed_field.
  exists (Subvs z_fixed_field).
  apply: val_inj.
  by [].
- move=> [q ->] g gEK.
  apply: val_inj.
  rewrite lazard_galois_actionE lazard_base_embeddingE.
  exact: fixed_gal sub_K_E gEK (valP q).
Qed.

Variables (hT : finGroupType).
Variable G : {group hT}.
Variable rho : gal_of E -> hT.
Variable value : {set hT} -> subvs_of E.
Variable R : {poly subvs_of K}.

Hypothesis galois_orbit_value_equivariant :
  forall (g : gal_of E) (C : {set hT}),
    g \in 'Gal(E / K)%G ->
    C \in lazard_right_coset_orbit G ->
    lazard_galois_action g (value C) = value (C :* rho g).

Hypothesis galois_resolvent_factorization :
  map_poly lazard_base_embedding R = lazard_orbit_resolvent G value.

(** Lazard's complete general resolvent criterion with the fixed-field
    premise discharged by MathComp's Galois theorem.  The only remaining
    mathematical inputs are the resolvent's equivariance, its specialized
    factorization, and the separability premise appearing in Lazard's
    converse. *)
Corollary lazard_galois_resolvent_has_base_root_iff_image_sub_conjugate
    (R_separable : separable_poly R) :
  (exists q : subvs_of K, root R q) <->
  exists x : hT, rho @: 'Gal(E / K)%G \subset G :^ x.
Proof.
exact: (@lazard_resolvent_has_base_root_iff_image_sub_conjugate
  (subvs_of K) (subvs_of E) (gal_of E) hT
  lazard_base_embedding 'Gal(E / K)%G G rho lazard_galois_action
  value R lazard_galois_base_fixed_iff
  galois_orbit_value_equivariant galois_resolvent_factorization R_separable).
Qed.

End MathCompGaloisAdapter.

End PolynomialFormulasLazardGeneralResolventCriterion.
