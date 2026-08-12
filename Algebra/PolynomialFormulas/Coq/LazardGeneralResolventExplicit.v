From HB Require Import structures.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardGeneralResolventCriterion LazardInvariantMultinomials.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The explicit invariant-polynomial adapter for Lazard's Theorem 1.

    The abstract criterion in [LazardGeneralResolventCriterion] accepts an
    equivariant function on cosets and a specialized factorization.  Here
    both are derived from an actual multivariate polynomial over the base
    field.  For a right coset [G :* x] the formal conjugate is [x^-1 . P].
    The inverse is forced by the use of right cosets.  Subgroup invariance
    makes this independent of the representative.

    After evaluation at an ordered root tuple, the ordinary algebra laws of
    multivariate evaluation prove Galois equivariance.  The orbit product is
    consequently fixed coefficientwise.  MathComp's Galois fixed-field
    theorem then constructs a polynomial over the base field whose scalar
    extension is exactly that product.  Thus neither equivariance nor
    factorization is a premise of the final criterion.  The exact-stabilizer
    refinement below proves that the formal coset conjugates are distinct.
    Separability remains in the specialized converse because evaluation can
    still create collisions.  A minimal-polynomial identification additionally
    needs the documented rational-function fixed-field bridge. *)
Module PolynomialFormulasLazardGeneralResolventExplicit.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.
Local Open Scope mpoly_scope.

Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module IM := PolynomialFormulasLazardInvariantMultinomials.

Section FormalOrbit.

Variables (K : fieldType) (n : nat).
Variable G : {group 'S_n}.
Variable invariant : {mpoly K[n]}.

Definition lazard_invariant_under : Prop :=
  forall g : 'S_n, g \in G ->
    IM.mpoly_left_action g invariant = invariant.

(** Exact stabilizer in the full permutation group is the group-theoretic
    refinement used here as a proxy for the paper's phrase that the invariant
    ``belongs to [G]''.  It makes the formal coset conjugates distinct, but by
    itself does not prove the paper's fixed-field-generation sentence. *)
Definition lazard_invariant_stabilizer_exact : Prop :=
  forall s : 'S_n,
    IM.mpoly_left_action s invariant = invariant <-> s \in G.

Lemma lazard_invariant_stabilizer_exact_under :
  lazard_invariant_stabilizer_exact -> lazard_invariant_under.
Proof.
move=> exact_stabilizer g gG.
exact: (proj2 (exact_stabilizer g)) gG.
Qed.

Variable invariant_under : lazard_invariant_under.

(** The formal conjugate on an arbitrary set.  Only its values on the right
    coset orbit are used.  MathComp's [repr] is canonical, while the next
    lemma proves that the resulting polynomial does not depend on that
    choice. *)
Definition lazard_formal_orbit_value (C : {set 'S_n}) : {mpoly K[n]} :=
  IM.mpoly_left_action (repr C)^-1 invariant.

Lemma lazard_formal_orbit_value_rcoset (x : 'S_n) :
  lazard_formal_orbit_value (G :* x) =
    IM.mpoly_left_action x^-1 invariant.
Proof.
rewrite /lazard_formal_orbit_value.
case: repr_rcosetP=> g Gg.
rewrite invMg IM.mpoly_left_actionM.
by rewrite invariant_under ?groupV.
Qed.

(** Right translation of cosets becomes left action by the inverse
    permutation on formal conjugates. *)
Lemma lazard_formal_orbit_value_right_action C s :
  C \in GC.lazard_right_coset_orbit G ->
  lazard_formal_orbit_value (C :* s) =
    IM.mpoly_left_action s^-1 (lazard_formal_orbit_value C).
Proof.
case/rcosetsP=> x _ ->.
rewrite -rcosetM !lazard_formal_orbit_value_rcoset invMg.
exact: IM.mpoly_left_actionM.
Qed.

(** The universal orbit resolvent before any roots are substituted. *)
Definition lazard_universal_invariant_resolvent :
    {poly {mpoly K[n]}} :=
  GC.lazard_orbit_resolvent G lazard_formal_orbit_value.

End FormalOrbit.

Section ExactFormalOrbit.

Variables (K : fieldType) (n : nat).
Variable G : {group 'S_n}.
Variable invariant : {mpoly K[n]}.
Variable invariant_stabilizer_exact :
  @lazard_invariant_stabilizer_exact K n G invariant.

Let invariant_under : @lazard_invariant_under K n G invariant :=
  lazard_invariant_stabilizer_exact_under invariant_stabilizer_exact.

(** Exact stabilizer means that equality of two formal conjugates already
    forces equality of their indexing right cosets. *)
Theorem lazard_formal_orbit_value_injective_of_exact_stabilizer :
  {in GC.lazard_right_coset_orbit G &,
    injective (@lazard_formal_orbit_value K n G invariant)}.
Proof.
move=> C D Cmem Dmem hCD.
case/rcosetsP: Cmem=> x _ ->.
case/rcosetsP: Dmem=> y _ ->.
rewrite !(@lazard_formal_orbit_value_rcoset
  K n G invariant invariant_under) in hCD.
have hxy := congr1 (IM.mpoly_left_action x) hCD.
rewrite -!IM.mpoly_left_actionM mulgV IM.mpoly_left_action1 in hxy.
have hstab :
    IM.mpoly_left_action (x * y^-1) invariant = invariant := esym hxy.
have xyG := (proj1 (invariant_stabilizer_exact (x * y^-1))) hstab.
apply/rcoset_eqP/rcosetP.
exists (x * y^-1); first exact: xyG.
by rewrite mulgA mulVg mulg1.
Qed.

Corollary lazard_formal_orbit_value_eq_iff_of_exact_stabilizer C D :
  C \in GC.lazard_right_coset_orbit G ->
  D \in GC.lazard_right_coset_orbit G ->
  ((@lazard_formal_orbit_value K n G invariant C =
      @lazard_formal_orbit_value K n G invariant D) <-> C = D).
Proof.
move=> Cmem Dmem; split.
- exact: lazard_formal_orbit_value_injective_of_exact_stabilizer Cmem Dmem.
- by move=> ->.
Qed.

(** The coefficient-polynomial conjugates in Lazard's universal resolvent
    are duplicate-free before any specialization of the variables. *)
Theorem lazard_formal_orbit_conjugates_uniq_of_exact_stabilizer :
  uniq (GC.lazard_orbit_value_sequence G
    (@lazard_formal_orbit_value K n G invariant)).
Proof.
rewrite /GC.lazard_orbit_value_sequence.
apply/dinjectiveP.
exact: lazard_formal_orbit_value_injective_of_exact_stabilizer.
Qed.

(** The universal polynomial used by the paper-facing exact-stabilizer
    theorems below.  Its underlying product does not depend on the proof of
    invariance; exact stabilizer enters the duplicate-free conclusions. *)
Definition lazard_paper_universal_invariant_resolvent :
    {poly {mpoly K[n]}} :=
  @lazard_universal_invariant_resolvent K n G invariant.

(** Consequently the universal orbit product is square-free/separable over
    the polynomial coefficient ring.  A later numerical specialization may
    still identify conjugates, so this theorem deliberately does not remove
    the separability premise from the specialized Galois converse. *)
Theorem lazard_paper_universal_invariant_resolvent_separable :
  separable_poly lazard_paper_universal_invariant_resolvent.
Proof.
rewrite /lazard_paper_universal_invariant_resolvent
  /lazard_universal_invariant_resolvent
  /GC.lazard_orbit_resolvent separable_prod_XsubC.
exact: lazard_formal_orbit_conjugates_uniq_of_exact_stabilizer.
Qed.

(** The minimal-polynomial sentence needs a field, not merely the polynomial
    coefficient ring used above.  The companion files
    [LazardSymmetricRationalFiniteExtension],
    [LazardSymmetricRationalGalois], and
    [LazardSymmetricRationalResolventBridge] now construct that field,
    identify its full Galois group with ['S_n], transport exact stabilizers,
    and prove that the mapped product above is the ordinary minimal
    polynomial.  It is intentionally not inferred here merely from
    duplicate-free formal conjugates. *)

End ExactFormalOrbit.

Section MultinomialSpecialization.

Variables (K E : fieldType) (n : nat).
Variable embed : {rmorphism K -> E}.
Variable roots : n.-tuple E.

Definition lazard_mpoly_specialize_fun (p : {mpoly K[n]}) : E :=
  (map_mpoly embed p).@[tnth roots].

Lemma lazard_mpoly_specialize_zmod_morphism :
  zmod_morphism lazard_mpoly_specialize_fun.
Proof.
move=> p q.
by rewrite /lazard_mpoly_specialize_fun !raddfB.
Qed.

Lemma lazard_mpoly_specialize_monoid_morphism :
  monoid_morphism lazard_mpoly_specialize_fun.
Proof.
split=> [|p q].
- by rewrite /lazard_mpoly_specialize_fun !rmorph1.
- by rewrite /lazard_mpoly_specialize_fun !rmorphM.
Qed.

Definition lazard_mpoly_specialize :
    {rmorphism {mpoly K[n]} -> E} :=
  HB.pack lazard_mpoly_specialize_fun
    (GRing.isZmodMorphism.Build _ _ lazard_mpoly_specialize_fun
      lazard_mpoly_specialize_zmod_morphism)
    (GRing.isMonoidMorphism.Build _ _ lazard_mpoly_specialize_fun
      lazard_mpoly_specialize_monoid_morphism).

Lemma lazard_mpoly_specializeE p :
  lazard_mpoly_specialize p = (map_mpoly embed p).@[tnth roots].
Proof. by []. Qed.

(** Coefficient change commutes with the explicit permutation action. *)
Lemma map_mpoly_left_action (s : 'S_n) (p : {mpoly K[n]}) :
  map_mpoly embed (IM.mpoly_left_action s p) =
    IM.mpoly_left_action s (map_mpoly embed p).
Proof.
apply/mpolyP=> m.
by rewrite /IM.mpoly_left_action !mcoeff_map_mpoly !mcoeff_sym.
Qed.

(** Evaluation after a variable permutation. *)
Lemma meval_mpoly_left_action (s : 'S_n) (q : {mpoly E[n]}) :
  (IM.mpoly_left_action s q).@[tnth roots] =
    q.@[fun i => tnth roots (s^-1 i)].
Proof.
rewrite /IM.mpoly_left_action.
rewrite -{1}(comp_mpoly_id (msym s^-1 q)).
rewrite msym_mPo comp_mpoly_meval.
apply: meval_eq=> i.
by rewrite !tnth_mktuple mevalXU.
Qed.

Variables (G : {group 'S_n}) (invariant : {mpoly K[n]}).

Definition lazard_specialized_orbit_value (C : {set 'S_n}) : E :=
  lazard_mpoly_specialize embed roots
    (@lazard_formal_orbit_value K n G invariant C).

(** Specialization of the universal product is literally the product of the
    specialized conjugates. *)
Theorem lazard_universal_invariant_resolvent_specializes :
  map_poly (lazard_mpoly_specialize embed roots)
      (@lazard_universal_invariant_resolvent K n G invariant) =
    GC.lazard_orbit_resolvent G lazard_specialized_orbit_value.
Proof.
rewrite /lazard_universal_invariant_resolvent
  /GC.lazard_orbit_resolvent map_prod_XsubC
  /GC.lazard_orbit_value_sequence /lazard_specialized_orbit_value.
by rewrite big_map.
Qed.

End MultinomialSpecialization.

Section PaperMultinomialSpecialization.

Variables (K E : fieldType) (n : nat).
Variable embed : {rmorphism K -> E}.
Variable roots : n.-tuple E.
Variable G : {group 'S_n}.
Variable invariant : {mpoly K[n]}.

(** Paper-facing specialization wrapper: the exact-stabilizer invariant
    supplies duplicate-free formal conjugates and a separable universal
    product, while the reusable adapter gives its evaluated coset product. *)
Theorem lazard_paper_universal_invariant_resolvent_specializes
    (invariant_stabilizer_exact :
      @lazard_invariant_stabilizer_exact K n G invariant) :
  [/
    uniq (GC.lazard_orbit_value_sequence G
      (@lazard_formal_orbit_value K n G invariant)),
    separable_poly (@lazard_paper_universal_invariant_resolvent
      K n G invariant)
  & map_poly (lazard_mpoly_specialize embed roots)
      (@lazard_paper_universal_invariant_resolvent
        K n G invariant) =
    GC.lazard_orbit_resolvent G
      (@lazard_specialized_orbit_value
        K E n embed roots G invariant)].
Proof.
split.
- exact: (@lazard_formal_orbit_conjugates_uniq_of_exact_stabilizer
    K n G invariant invariant_stabilizer_exact).
- exact: (@lazard_paper_universal_invariant_resolvent_separable
    K n G invariant invariant_stabilizer_exact).
- exact: (@lazard_universal_invariant_resolvent_specializes
    K E n embed roots G invariant).
Qed.

End PaperMultinomialSpecialization.

Section ExplicitGaloisAdapter.

Variables (F : fieldType) (L : splittingFieldType F).
Variables (K E : {subfield L}).
Hypothesis galois_K_E : galois K E.

Let sub_K_E : (K <= E)%VS.
Proof.
have /and3P [sKE _ _] := galois_K_E.
exact: sKE.
Qed.

Variables (n : nat) (G : {group 'S_n}).
Variable invariant : {mpoly (subvs_of K)[n]}.
Variable invariant_under :
  @lazard_invariant_under (subvs_of K) n G invariant.
Variable roots : n.-tuple (subvs_of E).
Variable rho : gal_of E -> 'S_n.
Hypothesis roots_equivariant :
  forall (g : gal_of E) (i : 'I_n),
    g \in 'Gal(E / K)%G ->
    GC.lazard_galois_action g (tnth roots i) =
      tnth roots (rho g i).

Local Notation base_embed :=
  (@GC.lazard_base_embedding F L K E galois_K_E).
Local Notation gal_action :=
  (@GC.lazard_galois_action F L E).

Definition lazard_explicit_orbit_value (C : {set 'S_n}) : subvs_of E :=
  lazard_mpoly_specialize base_embed roots
    (@lazard_formal_orbit_value
      (subvs_of K) n G invariant C).

Definition lazard_explicit_orbit_resolvent : {poly subvs_of E} :=
  GC.lazard_orbit_resolvent G lazard_explicit_orbit_value.

Lemma lazard_galois_action_base_embed
    (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) (c : subvs_of K) :
  gal_action g (base_embed c) = base_embed c.
Proof.
apply: (proj2 (GC.lazard_galois_base_fixed_iff galois_K_E
  (base_embed c))).
exists c; exact: erefl.
Qed.

(** A Galois automorphism commutes with evaluation of every explicit
    base-coefficient multivariate polynomial. *)
Lemma lazard_galois_action_mpoly_specialize
    (g : gal_of E) (gEK : g \in 'Gal(E / K)%G)
    (p : {mpoly (subvs_of K)[n]}) :
  gal_action g (lazard_mpoly_specialize base_embed roots p) =
    (map_mpoly base_embed p).@[
      fun i => gal_action g (tnth roots i)].
Proof.
elim/mpolyind: p=> [|c m p hm hc ih].
- by rewrite !raddf0.
- rewrite !raddfD /= !map_mpolyZ map_mpolyX !mevalD !mevalZ !mevalX.
  rewrite !rmorphD !rmorphM lazard_galois_action_base_embed // ih.
  congr (_ * _ + _).
  rewrite rmorph_prod.
  apply: eq_bigr=> i _.
  by rewrite rmorphXn.
Qed.

(** The abstract equivariance premise is now a consequence of the root
    permutation and the explicit polynomial definition. *)
Theorem lazard_explicit_orbit_value_equivariant
    (g : gal_of E) (C : {set 'S_n}) :
  g \in 'Gal(E / K)%G ->
  C \in GC.lazard_right_coset_orbit G ->
  gal_action g (lazard_explicit_orbit_value C) =
    lazard_explicit_orbit_value (C :* rho g).
Proof.
move=> gEK Cmem.
rewrite /lazard_explicit_orbit_value
  lazard_galois_action_mpoly_specialize //.
have hroots :
    (fun i => gal_action g (tnth roots i)) =1
    (fun i => tnth roots (rho g i)).
  move=> i; exact: roots_equivariant.
rewrite (meval_eq _ hroots).
rewrite -(@meval_mpoly_left_action
  (subvs_of E) n roots (rho g)^-1 (map_mpoly base_embed
    (@lazard_formal_orbit_value
      (subvs_of K) n G invariant C))).
rewrite invgK -map_mpoly_left_action.
by rewrite -(@lazard_formal_orbit_value_right_action
  (subvs_of K) n G invariant invariant_under C (rho g) Cmem).
Qed.

(** Right translation permutes the finite enumeration of the coset orbit. *)
Lemma lazard_right_translate_enum_perm (s : 'S_n) :
  perm_eq
    (map (fun C : {set 'S_n} => C :* s)
      (enum (GC.lazard_right_coset_orbit G)))
    (enum (GC.lazard_right_coset_orbit G)).
Proof.
apply: uniq_perm.
- rewrite map_inj_uniq ?enum_uniq //.
  exact: rcoset_inj.
- exact: enum_uniq.
- move=> C; apply/mapP/idP.
  + move=> [D].
    rewrite mem_enum=> Dmem ->.
    rewrite mem_enum.
    exact: GC.lazard_right_coset_action_mem Dmem.
  + rewrite mem_enum=> Cmem.
    exists (C :* s^-1).
    * rewrite mem_enum.
      exact: GC.lazard_right_coset_action_mem Cmem.
    * by rewrite -rcosetM mulVg rcoset1.
Qed.

(** Hence the explicit orbit product is fixed by every relative Galois
    automorphism. *)
Theorem lazard_explicit_orbit_resolvent_galois_fixed
    (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) :
  map_poly (gal_action g) lazard_explicit_orbit_resolvent =
    lazard_explicit_orbit_resolvent.
Proof.
rewrite /lazard_explicit_orbit_resolvent
  /GC.lazard_orbit_resolvent map_prod_XsubC
  /GC.lazard_orbit_value_sequence !big_map !big_enum.
under [LHS] eq_bigr=> C Cmem do
  rewrite lazard_explicit_orbit_value_equivariant //.
rewrite -!big_enum -big_map.
exact: (perm_big _ (lazard_right_translate_enum_perm (rho g))).
Qed.

(** Each coefficient has an actual proof of membership in the base
    subfield, obtained from the fixed-field theorem. *)
Lemma lazard_explicit_orbit_resolvent_coefficient_mem_base i :
  val (lazard_explicit_orbit_resolvent`_i) \in K.
Proof.
have fixed_coefficient :
    forall g : gal_of E, g \in 'Gal(E / K)%G ->
      gal_action g (lazard_explicit_orbit_resolvent`_i) =
        lazard_explicit_orbit_resolvent`_i.
  move=> g gEK.
  have := congr1 (fun q : {poly subvs_of E} => q`_i)
    (lazard_explicit_orbit_resolvent_galois_fixed gEK).
  by rewrite coef_map in this.
have [q value_q] :=
  (proj1 (GC.lazard_galois_base_fixed_iff galois_K_E
    (lazard_explicit_orbit_resolvent`_i)) fixed_coefficient).
rewrite value_q GC.lazard_base_embeddingE.
exact: valP q.
Qed.

(** The base-field resolvent is assembled coefficientwise from those
    fixed-field membership proofs. *)
Definition lazard_explicit_base_resolvent : {poly subvs_of K} :=
  \poly_(i < size lazard_explicit_orbit_resolvent)
    (Subvs (lazard_explicit_orbit_resolvent_coefficient_mem_base i)).

(** Its scalar extension is exactly the explicit orbit product; the
    factorization premise of the abstract adapter is therefore discharged. *)
Theorem lazard_explicit_base_resolvent_map :
  map_poly base_embed lazard_explicit_base_resolvent =
    lazard_explicit_orbit_resolvent.
Proof.
apply/polyP=> i; apply: val_inj.
rewrite coef_map GC.lazard_base_embeddingE
  /lazard_explicit_base_resolvent coef_poly.
case: ifP=> hi /=; first exact: erefl.
have hsize : size lazard_explicit_orbit_resolvent <= i by
  rewrite leqNgt.
by rewrite nth_default.
Qed.

(** Forward implication of Lazard's criterion.  No separability appears. *)
Theorem lazard_explicit_base_resolvent_has_root_of_image_sub_group :
  rho @: 'Gal(E / K)%G \subset G ->
  exists q : subvs_of K, root lazard_explicit_base_resolvent q.
Proof.
move=> image_sub.
exact: (@GC.lazard_resolvent_has_base_root_of_image_sub_group
  (subvs_of K) (subvs_of E) (gal_of E) 'S_n
  base_embed 'Gal(E / K)%G G rho gal_action
  lazard_explicit_orbit_value lazard_explicit_base_resolvent
  (GC.lazard_galois_base_fixed_iff galois_K_E)
  lazard_explicit_orbit_value_equivariant
  lazard_explicit_base_resolvent_map image_sub).
Qed.

(** The complete explicit invariant-resolvent criterion.  Separability is
    used only by the implication from a base-field root to subgroup
    containment. *)
Theorem lazard_explicit_base_resolvent_has_root_iff_image_sub_conjugate
    (R_separable : separable_poly lazard_explicit_base_resolvent) :
  (exists q : subvs_of K, root lazard_explicit_base_resolvent q) <->
  exists x : 'S_n, rho @: 'Gal(E / K)%G \subset G :^ x.
Proof.
exact: (@GC.lazard_galois_resolvent_has_base_root_iff_image_sub_conjugate
  F L K E galois_K_E 'S_n G rho lazard_explicit_orbit_value
  lazard_explicit_base_resolvent
  lazard_explicit_orbit_value_equivariant
  lazard_explicit_base_resolvent_map R_separable).
Qed.

End ExplicitGaloisAdapter.

Section OrderedRootPresentation.

Variables (F : fieldType) (L : splittingFieldType F).
Variables (K E : {subfield L}).
Hypothesis galois_K_E : galois K E.

Variables (n : nat) (G : {group 'S_n}).
Variable invariant : {mpoly (subvs_of K)[n]}.
Variable invariant_under :
  @lazard_invariant_under (subvs_of K) n G invariant.

Variable basePolynomial : {poly subvs_of K}.
Variable roots : n.-tuple (subvs_of E).

Local Notation base_embed :=
  (@GC.lazard_base_embedding F L K E galois_K_E).
Local Notation gal_action :=
  (@GC.lazard_galois_action F L E).

(** A literal ordered-root presentation in MathComp form.  The associate
    factorization records that the polynomial splits completely in [E], and
    [uniq] is the tuple form of nodup. *)
Definition lazard_ordered_root_presentation : Prop :=
  uniq roots /\
  map_poly base_embed basePolynomial %=
    \prod_(z <- roots) ('X - z%:P).

Hypothesis root_presentation : lazard_ordered_root_presentation.

Let roots_nodup : uniq roots := root_presentation.1.
Let roots_factorization :
    map_poly base_embed basePolynomial %=
      \prod_(z <- roots) ('X - z%:P) :=
  root_presentation.2.

(** A relative Galois automorphism fixes the scalar extension of the
    presented base polynomial coefficientwise. *)
Lemma lazard_ordered_base_polynomial_galois_fixed
    (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) :
  map_poly (gal_action g) (map_poly base_embed basePolynomial) =
    map_poly base_embed basePolynomial.
Proof.
rewrite map_poly_comp.
apply/eq_map_poly=> c /=.
exact: (@lazard_galois_action_base_embed
  F L K E galois_K_E g gEK c).
Qed.

(** Completeness of the split factorization implies that relative Galois
    automorphisms permute the supplied ordered root tuple. *)
Lemma lazard_ordered_gal_perm_eq
    (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) :
  perm_eq [seq gal_action g x | x <- roots] roots.
Proof.
apply: prod_XsubC_eq; apply/eqP.
rewrite -eqp_monic ?monic_prod_XsubC //.
rewrite -(eqp_rtrans roots_factorization) big_map.
apply: (@eqp_trans _
  (map_poly (gal_action g \o base_embed) basePolynomial)); last first.
  apply/eqpW/eq_map_poly=> c /=.
  exact: (@lazard_galois_action_base_embed
    F L K E galois_K_E g gEK c).
rewrite map_poly_comp /=.
have := roots_factorization; rewrite -(eqp_map (gal_action g)) /=.
move=> /eqp_rtrans /= ->; apply/eqpW; rewrite rmorph_prod /=.
by apply: eq_bigr=> x; rewrite rmorphB /= map_polyX map_polyC /=.
Qed.

(** The selected permutation is total on the ambient automorphism type.  On
    the relative Galois subgroup it is extracted from the preceding proved
    permutation equality; outside that subgroup its value is irrelevant and
    is chosen to be the identity. *)
Definition lazard_ordered_gal_perm (g : gal_of E) : 'S_n :=
  if boolP (g \in 'Gal(E / K)%G) is ReflectT gEK then
    projT1 (sig_eqW (tuple_permP
      (lazard_ordered_gal_perm_eq gEK)))
  else 1.

Lemma lazard_ordered_root_tnth i :
  tnth roots i = nth 0 roots i.
Proof. by rewrite (tnth_nth 0). Qed.

Lemma lazard_ordered_gal_permP
    (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) (i : 'I_n) :
  tnth roots (lazard_ordered_gal_perm g i) =
    gal_action g (tnth roots i).
Proof.
rewrite !lazard_ordered_root_tnth /lazard_ordered_gal_perm.
case: boolP=> [gEK'|gNEK].
- case: sig_eqW=> /= s.
  move=> /(congr1 (((@nth _ 0))^~ i)).
  rewrite (nth_map 0) ?size_tuple // => ->.
  Unshelve.
  by rewrite (nth_map i) ?size_enum_ord //
    nth_ord_enum lazard_ordered_root_tnth.
- by move: gEK; rewrite (negbTE gNEK).
Qed.

(** Nodup labels make the selected permutations a genuine representation on
    the relative Galois subgroup. *)
Lemma lazard_ordered_root_tnth_injective : injective (tnth roots).
Proof.
move=> i j hij; apply: val_inj.
apply: (uniqP 0 roots_nodup);
  rewrite ?inE ?size_tuple ?ltn_ord //.
by move: hij; rewrite !(@tnth_nth n (subvs_of E) 0).
Qed.

Lemma lazard_ordered_gal_perm_is_morphism :
  {in 'Gal(E / K)%G &,
    {morph lazard_ordered_gal_perm :
      x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move=> u v uEK vEK; apply/permP=> i.
apply: lazard_ordered_root_tnth_injective.
rewrite permM !lazard_ordered_gal_permP ?groupM //.
apply: val_inj.
rewrite !GC.lazard_galois_actionE galM; last exact: valP (tnth roots i).
by [].
Qed.

(** The root-equivariance premise used by the explicit adapter, now derived
    rather than supplied. *)
Lemma lazard_ordered_roots_equivariant
    (g : gal_of E) (i : 'I_n) :
  g \in 'Gal(E / K)%G ->
  gal_action g (tnth roots i) =
    tnth roots (lazard_ordered_gal_perm g i).
Proof.
move=> gEK.
exact: esym (lazard_ordered_gal_permP gEK i).
Qed.

(** The concrete base resolvent obtained from the literal polynomial/root
    presentation. *)
Definition lazard_ordered_base_resolvent : {poly subvs_of K} :=
  @lazard_explicit_base_resolvent
    F L K E galois_K_E n G invariant invariant_under roots
    lazard_ordered_gal_perm lazard_ordered_roots_equivariant.

Theorem lazard_ordered_base_resolvent_map :
  map_poly base_embed lazard_ordered_base_resolvent =
    @lazard_explicit_orbit_resolvent
      F L K E galois_K_E n G invariant roots.
Proof.
exact: (@lazard_explicit_base_resolvent_map
  F L K E galois_K_E n G invariant invariant_under roots
  lazard_ordered_gal_perm lazard_ordered_roots_equivariant).
Qed.

(** Forward implication with no caller-supplied root action and no
    separability premise. *)
Theorem lazard_ordered_base_resolvent_has_root_of_image_sub_group :
  lazard_ordered_gal_perm @: 'Gal(E / K)%G \subset G ->
  exists q : subvs_of K, root lazard_ordered_base_resolvent q.
Proof.
exact: (@lazard_explicit_base_resolvent_has_root_of_image_sub_group
  F L K E galois_K_E n G invariant invariant_under roots
  lazard_ordered_gal_perm lazard_ordered_roots_equivariant).
Qed.

(** Complete literal-presentation form of Lazard's Theorem 1.  Resolvent
    separability remains only in the converse. *)
Theorem lazard_ordered_base_resolvent_has_root_iff_image_sub_conjugate
    (R_separable : separable_poly lazard_ordered_base_resolvent) :
  (exists q : subvs_of K, root lazard_ordered_base_resolvent q) <->
  exists x : 'S_n,
    lazard_ordered_gal_perm @: 'Gal(E / K)%G \subset G :^ x.
Proof.
exact: (@lazard_explicit_base_resolvent_has_root_iff_image_sub_conjugate
  F L K E galois_K_E n G invariant invariant_under roots
  lazard_ordered_gal_perm lazard_ordered_roots_equivariant R_separable).
Qed.

End OrderedRootPresentation.

(** * Paper-facing exact-stabilizer/root-presentation composition

    The ordered-root theorem above is deliberately reusable under the weaker
    hypothesis that the displayed polynomial is merely [G]-invariant.  This
    wrapper is the literal paper interface: exact renaming stabilizer derives
    that invariance, while the duplicate-free associate factorization derives
    the root permutation and its equivariance.  Thus no orbit map,
    orbit-injectivity, factorization of the resolvent, fixed-field fact, or
    Galois-action certificate is supplied separately. *)
Section PaperOrderedRootPresentation.

Variables (F : fieldType) (L : splittingFieldType F).
Variables (K E : {subfield L}).
Hypothesis galois_K_E : galois K E.

Variables (n : nat) (G : {group 'S_n}).
Variable invariant : {mpoly (subvs_of K)[n]}.
Hypothesis invariant_stabilizer_exact :
  @lazard_invariant_stabilizer_exact (subvs_of K) n G invariant.

Variable basePolynomial : {poly subvs_of K}.
Variable roots : n.-tuple (subvs_of E).
Hypothesis root_presentation :
  @lazard_ordered_root_presentation
    F L K E galois_K_E n basePolynomial roots.

Let invariant_under :
    @lazard_invariant_under (subvs_of K) n G invariant :=
  lazard_invariant_stabilizer_exact_under invariant_stabilizer_exact.

Local Notation base_embed :=
  (@GC.lazard_base_embedding F L K E galois_K_E).

(** The paper-facing specialized resolvent.  The proof of ordinary
    invariance is fixed internally by [invariant_stabilizer_exact]. *)
Definition lazard_paper_ordered_base_resolvent : {poly subvs_of K} :=
  @lazard_ordered_base_resolvent
    F L K E galois_K_E n G invariant invariant_under
    basePolynomial roots root_presentation.

Theorem lazard_paper_ordered_base_resolvent_map :
  map_poly base_embed lazard_paper_ordered_base_resolvent =
    @lazard_explicit_orbit_resolvent
      F L K E galois_K_E n G invariant roots.
Proof.
exact: (@lazard_ordered_base_resolvent_map
  F L K E galois_K_E n G invariant invariant_under
  basePolynomial roots root_presentation).
Qed.

(** Fixed displayed subgroup, forward direction.  This implication uses no
    separability premise. *)
Theorem lazard_paper_ordered_base_resolvent_has_root_of_image_sub_group :
  (@lazard_ordered_gal_perm
      F L K E galois_K_E n basePolynomial roots root_presentation)
      @: 'Gal(E / K)%G \subset G ->
  exists q : subvs_of K,
    root lazard_paper_ordered_base_resolvent q.
Proof.
exact: (@lazard_ordered_base_resolvent_has_root_of_image_sub_group
  F L K E galois_K_E n G invariant invariant_under
  basePolynomial roots root_presentation).
Qed.

(** Corrected complete form of Lazard's Theorem 1.  Under an arbitrary
    labelling, a base-field root selects an unspecified coset and hence only
    containment in a conjugate of the displayed [G]. *)
Theorem lazard_paper_ordered_base_resolvent_has_root_iff_image_sub_conjugate
    (R_separable :
      separable_poly lazard_paper_ordered_base_resolvent) :
  (exists q : subvs_of K,
      root lazard_paper_ordered_base_resolvent q) <->
  exists x : 'S_n,
    (@lazard_ordered_gal_perm
      F L K E galois_K_E n basePolynomial roots root_presentation)
      @: 'Gal(E / K)%G \subset G :^ x.
Proof.
exact: (@lazard_ordered_base_resolvent_has_root_iff_image_sub_conjugate
  F L K E galois_K_E n G invariant invariant_under
  basePolynomial roots root_presentation R_separable).
Qed.

End PaperOrderedRootPresentation.

End PolynomialFormulasLazardGeneralResolventExplicit.
