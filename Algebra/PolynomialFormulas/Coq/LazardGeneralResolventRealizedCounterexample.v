From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0 abel.
From PolynomialFormulas Require Import
  LazardGeneralResolventConjugacyCounterexample
  LazardGeneralResolventThetaAdapter
  LazardOptimalityTheoremThreeFormulaBridge
  LazardQuinticCanonicalEpsilonNonzero
  QuinticFiveCycle QuinticScalarResolventSeparable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A polynomial realization of the conjugacy correction to Lazard
    Theorem 1.

    The companion finite-group file proves that a conjugate copy of [F20]
    fixes a non-base coset without being contained in the displayed copy.
    Here the same phenomenon is realized by the actual cyclic quintic used
    in the optimality counterexamples, the complete ordered roots in its
    canonical splitting field, and their faithful Galois action.

    The directly computed rational root of the executable Dummit resolvent
    selects a root ordering whose image lies in the standard [F20].
    Transitivity supplies a conjugate five-cycle in the original image.  A
    finite [S5] calculation then shows that the selected image contains the
    literal standard five-cycle.  Relabelling once more by the explicit
    three-cycle puts the image in the corresponding conjugate [F20] and
    makes it contain the displayed conjugated five-cycle outside the
    standard [F20].  No inverse-Galois or supplied action hypothesis occurs
    in the final theorem. *)
Module PolynomialFormulasLazardGeneralResolventRealizedCounterexample.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Module Finite :=
  PolynomialFormulasLazardGeneralResolventConjugacyCounterexample.
Module ThetaAdapter :=
  PolynomialFormulasLazardGeneralResolventThetaAdapter.
Module Explicit := PolynomialFormulasLazardGeneralResolventExplicit.
Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module Bridge :=
  PolynomialFormulasLazardOptimalityTheoremThreeFormulaBridge.
Module F20 := PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module RO := PolynomialFormulasLazardQuinticRootOrdering.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module Five := PolynomialFormulasQuinticFiveCycle.
Module Sep := PolynomialFormulasQuinticScalarResolventSeparable.
Module CD := PolynomialFormulasQuinticCanonicalDecision.

Definition p : {poly rat} := Bridge.cyclic_depressed_Q.
Definition p_size : size p = 6%N := Bridge.cyclic_depressed_Q_size.
Definition L : splittingFieldType rat := numfield p.
Definition ratrL : {rmorphism rat -> L} :=
  char0_ratr (char_numfield p).
Definition canonical_roots : 5.-tuple L :=
  @GA.quintic_root_tuple p p_size.

(* -------------------------------------------------------------------- *)
(** * The selected and deliberately relabelled actual Galois actions *)

(** The image after the rational theta root has selected index [i]. *)
Definition selected_galois_image (i : 'I_6) : {group F20.S5} :=
  (@GA.quintic_galois_image
      p p_size Bridge.cyclic_depressed_Q_irreducible) :^
    F20.representative i.

(** The actual image after the additional three-cycle relabelling. *)
Definition relabelled_galois_image (i : 'I_6) : {group F20.S5} :=
  selected_galois_image i :^ Finite.relabelling.

(** The complete root tuple associated with that additional relabelling.
    The inverse is forced by MathComp's right-action convention for
    [permute_quintic_roots]. *)
Definition relabelled_roots (i : 'I_6) : 5.-tuple L :=
  TV.permute_quintic_roots Finite.relabelling^-1
    (@ID.lazard_selected_roots Bridge.cyclic_depressed_data i).

(** The corresponding pointwise permutation of the root labels. *)
Definition relabelled_gal_perm
    (i : 'I_6) (g : gal_of {:L}) : F20.S5 :=
  ((@GA.quintic_gal_perm p p_size g) ^ F20.representative i) ^
    Finite.relabelling.

(** The named subgroup is exactly the image of the displayed relabelled
    action, rather than merely an ambient group chosen to contain it. *)
Lemma relabelled_gal_perm_mem_image
    (i : 'I_6) (g : gal_of {:L})
    (gGal : g \in 'Gal({:L} / 1%AS)%G) :
  relabelled_gal_perm i g \in relabelled_galois_image i.
Proof.
rewrite /relabelled_gal_perm /relabelled_galois_image
  /selected_galois_image !mem_conjg !conjgK.
rewrite /GA.quintic_galois_image.
apply/morphimP; by exists g.
Qed.

Lemma relabelled_galois_image_has_action_witness
    (i : 'I_6) (x : F20.S5) :
  x \in relabelled_galois_image i ->
  exists2 g : gal_of {:L},
    g \in 'Gal({:L} / 1%AS)%G & x = relabelled_gal_perm i g.
Proof.
rewrite /relabelled_galois_image /selected_galois_image
  !mem_conjg /GA.quintic_galois_image.
case/morphimP=> g _ gGal hxg.
exists g; first exact: gGal.
rewrite /relabelled_gal_perm -hxg !conjgKV.
exact: erefl.
Qed.

(** This is the genuine action on the displayed root tuple, derived from
    the canonical splitting-field action. *)
Lemma relabelled_roots_gal (i : 'I_6) (g : gal_of {:L}) :
  map_tuple g (relabelled_roots i) =
    TV.permute_quintic_roots (relabelled_gal_perm i g)
      (relabelled_roots i).
Proof.
apply: eq_from_tnth=> k.
rewrite tnth_map /relabelled_roots /ID.lazard_selected_roots
  !TV.tnth_permute_quintic_roots.
rewrite -(@GA.quintic_gal_permP p p_size g
  ((F20.representative i)^-1 (Finite.relabelling^-1 k))).
rewrite /relabelled_gal_perm !F20.conjg_permE.
by rewrite !permK.
Qed.

(** The relabelled tuple still consists of five distinct roots. *)
Lemma relabelled_roots_injective (i : 'I_6) :
  injective (tnth (relabelled_roots i)).
Proof.
apply: RO.lazard_permute_root_tuple_injective.
apply: RO.lazard_permute_root_tuple_injective.
exact: (@GA.quintic_root_tuple_injective
  p p_size Bridge.cyclic_depressed_Q_irreducible).
Qed.

(** Relabelling changes neither the exact five-factor product nor the
    polynomial it represents. *)
Lemma relabelled_roots_factorization_eqp (i : 'I_6) :
  map_poly ratrL p %=
    \prod_(z <- relabelled_roots i) ('X - z%:P).
Proof.
rewrite /relabelled_roots /ID.lazard_selected_roots
  !CE.lazard_prod_XsubC_permute_quintic.
rewrite /ratrL char0_ratrE.
exact: (@GA.quintic_ratr_factorization p p_size).
Qed.

(** Since the rational quintic and the five-factor product are both monic,
    the preceding associate factorization is literal equality. *)
Lemma relabelled_roots_factorization (i : 'I_6) :
  map_poly ratrL p =
    \prod_(z <- relabelled_roots i) ('X - z%:P).
Proof.
apply/eqP.
rewrite -eqp_monic.
- exact: relabelled_roots_factorization_eqp.
- by rewrite map_monic Bridge.cyclic_depressed_Q_monic.
- exact: monic_prod_XsubC.
Qed.

(* -------------------------------------------------------------------- *)
(** * Literal generic-paper-resolvent realization

    The generic ordered-root interface uses bundled elements of the base and
    splitting subfields.  The following definitions only add and remove
    those subtype wrappers; their underlying values are the already proved
    [relabelled_roots]. *)

Definition cyclic_base_subfield : {subfield L} := 1%AS.
Definition cyclic_splitting_subfield : {subfield L} := {:L}.

Definition ratr_base :
    {rmorphism rat -> subvs_of cyclic_base_subfield} :=
  in_alg (subvs_of cyclic_base_subfield).

(** The canonical number field is a Galois splitting field of this
    irreducible rational quintic. *)
Lemma cyclic_splitting_galois :
  galois cyclic_base_subfield cyclic_splitting_subfield.
Proof.
rewrite /cyclic_base_subfield /cyclic_splitting_subfield.
exact: galois_numfield p.
Qed.

Local Notation cyclic_base_embed :=
  (@GC.lazard_base_embedding rat L cyclic_base_subfield
    cyclic_splitting_subfield cyclic_splitting_galois).

(** The root tuple bundled in the full splitting subfield. *)
Definition relabelled_roots_subfield (i : 'I_6) :
    5.-tuple (subvs_of cyclic_splitting_subfield) :=
  [tuple vsproj cyclic_splitting_subfield
    (tnth (relabelled_roots i) k) | k < 5].

Lemma tnth_relabelled_roots_subfield (i : 'I_6) k :
  tnth (relabelled_roots_subfield i) k =
    vsproj cyclic_splitting_subfield (tnth (relabelled_roots i) k).
Proof. by rewrite /relabelled_roots_subfield tnth_mktuple. Qed.

Lemma map_vsval_relabelled_roots_subfield (i : 'I_6) :
  map_tuple vsval (relabelled_roots_subfield i) = relabelled_roots i.
Proof.
apply: eq_from_tnth=> k.
rewrite tnth_map tnth_relabelled_roots_subfield.
exact: vsprojK (memvf (tnth (relabelled_roots i) k)).
Qed.

Lemma relabelled_roots_subfield_injective (i : 'I_6) :
  injective (tnth (relabelled_roots_subfield i)).
Proof.
move=> a b hab.
apply: (relabelled_roots_injective i).
have hval := congr1 vsval hab.
move: hval.
by rewrite !tnth_relabelled_roots_subfield !vsprojK ?memvf.
Qed.

Definition cyclic_base_polynomial :
    {poly subvs_of cyclic_base_subfield} := map_poly ratr_base p.

(** The subtype-bundled tuple is an exact ordered-root presentation for the
    same rational quintic.  Equality is checked after the injective forgetful
    map [vsval], where it is precisely
    [relabelled_roots_factorization]. *)
Lemma cyclic_ordered_root_presentation (i : 'I_6) :
  @Explicit.lazard_ordered_root_presentation
    rat L cyclic_base_subfield cyclic_splitting_subfield
      cyclic_splitting_galois 5 cyclic_base_polynomial
        (relabelled_roots_subfield i).
Proof.
split.
- apply/tuple_uniqP=> a b hab.
  exact: relabelled_roots_subfield_injective hab.
- apply/eqpW.
  apply: (map_poly_inj (vsval :
    {rmorphism subvs_of cyclic_splitting_subfield -> L})).
  rewrite rmorph_prod /= big_map.
  under [RHS]eq_bigr=> z _ do
    rewrite rmorphB /= map_polyX map_polyC /=.
  have hroots := congr1 val (map_vsval_relabelled_roots_subfield i).
  rewrite hroots.
  rewrite /cyclic_base_polynomial -!map_poly_comp.
  rewrite (eq_map_poly (fmorph_eq_rat _)).
  exact: relabelled_roots_factorization.
Qed.

(** The generic paper-facing resolver instantiated with the actual rational
    theta invariant and the exact root presentation above. *)
Definition cyclic_paper_theta_resolvent (i : 'I_6) :
    {poly subvs_of cyclic_base_subfield} :=
  @Explicit.lazard_paper_ordered_base_resolvent
    rat L cyclic_base_subfield cyclic_splitting_subfield
    cyclic_splitting_galois 5 F20.standard_F20
    (ThetaAdapter.lazard_theta_invariant
      (subvs_of cyclic_base_subfield))
    (ThetaAdapter.lazard_theta_exact_stabilizer ratr_base)
    cyclic_base_polynomial (relabelled_roots_subfield i)
    (cyclic_ordered_root_presentation i).

(** This is the realized form of the scalar-sextic adapter: the concrete
    scalar resolver is literally the scalar extension of the generic paper
    resolver. *)
Lemma cyclic_paper_theta_resolvent_map_eq_scalar (i : 'I_6) :
  map_poly cyclic_base_embed (cyclic_paper_theta_resolvent i) =
    TV.quintic_scalar_resolvent (relabelled_roots_subfield i).
Proof.
exact: (@ThetaAdapter.lazard_paper_ordered_theta_resolvent_map_eq_scalar_resolvent
  L cyclic_base_subfield cyclic_splitting_subfield
  cyclic_splitting_galois cyclic_base_polynomial
  (relabelled_roots_subfield i) (cyclic_ordered_root_presentation i)).
Qed.

Lemma map_subfield_scalar_resolvent (i : 'I_6) :
  map_poly (vsval :
      {rmorphism subvs_of cyclic_splitting_subfield -> L})
      (TV.quintic_scalar_resolvent (relabelled_roots_subfield i)) =
    TV.quintic_scalar_resolvent (relabelled_roots i).
Proof.
rewrite ThetaAdapter.map_quintic_scalar_resolvent.
by rewrite map_vsval_relabelled_roots_subfield.
Qed.

Lemma cyclic_paper_theta_resolvent_separable (i : 'I_6) :
  separable_poly (cyclic_paper_theta_resolvent i).
Proof.
have hsep :
    separable_poly (TV.quintic_scalar_resolvent (relabelled_roots i)).
  rewrite /relabelled_roots /ID.lazard_selected_roots
    !TV.quintic_scalar_resolvent_permute.
  exact: (@Sep.canonical_quintic_scalar_resolvent_separable
    Bridge.cyclic_depressed_data
    Bridge.cyclic_depressed_Q_irreducible).
rewrite -map_subfield_scalar_resolvent separable_map in hsep.
move: hsep.
rewrite -cyclic_paper_theta_resolvent_map_eq_scalar separable_map.
by [].
Qed.

(** The intrinsic permutation selected by the generic exact-root
    presentation. *)
Definition cyclic_ordered_gal_perm (i : 'I_6)
    (g : gal_of cyclic_splitting_subfield) : F20.S5 :=
  @Explicit.lazard_ordered_gal_perm
    rat L cyclic_base_subfield cyclic_splitting_subfield
    cyclic_splitting_galois 5 cyclic_base_polynomial
    (relabelled_roots_subfield i) (cyclic_ordered_root_presentation i) g.

(** The generic intrinsic action is pointwise the already constructed
    relabelled action.  This is proved from the two root-equivariance
    theorems and injectivity of the exact root tuple. *)
Lemma cyclic_ordered_gal_permE (i : 'I_6)
    (g : gal_of cyclic_splitting_subfield)
    (gGal : g \in
      'Gal(cyclic_splitting_subfield / cyclic_base_subfield)%G) :
  cyclic_ordered_gal_perm i g = relabelled_gal_perm i g.
Proof.
apply/permP=> k.
apply: (relabelled_roots_subfield_injective i).
rewrite /cyclic_ordered_gal_perm
  (@Explicit.lazard_ordered_gal_permP
    rat L cyclic_base_subfield cyclic_splitting_subfield
    cyclic_splitting_galois 5 cyclic_base_polynomial
    (relabelled_roots_subfield i) (cyclic_ordered_root_presentation i)
    g gGal k).
apply: val_inj.
rewrite GC.lazard_galois_actionE
  !tnth_relabelled_roots_subfield !vsprojK ?memvf.
have hgal := congr1 (fun t : 5.-tuple L => tnth t k)
  (relabelled_roots_gal i g).
move: hgal.
by rewrite tnth_map TV.tnth_permute_quintic_roots.
Qed.

(** Hence the image appearing in the generic criterion is literally the
    realized relabelled Galois image. *)
Lemma cyclic_ordered_gal_imageE (i : 'I_6) :
  cyclic_ordered_gal_perm i @:
      'Gal(cyclic_splitting_subfield / cyclic_base_subfield)%G =
    relabelled_galois_image i.
Proof.
apply/setP=> x; apply/imsetP/idP.
- move=> [g gGal ->].
  rewrite cyclic_ordered_gal_permE //.
  exact: relabelled_gal_perm_mem_image.
- move=> hx.
  have [g gGal hxg] := relabelled_galois_image_has_action_witness hx.
  apply/imsetP; exists g; first exact: gGal.
  by rewrite cyclic_ordered_gal_permE // hxg.
Qed.

(** Literal invocation of the generic corrected Theorem 1 for the realized
    quintic.  No separate scalar criterion is invoked here: separability is
    transported above, and the action image is identified by the preceding
    theorem. *)
Theorem cyclic_paper_theta_resolvent_has_root_iff_image_sub_conjugate
    (i : 'I_6) :
  (exists q : subvs_of cyclic_base_subfield,
      root (cyclic_paper_theta_resolvent i) q) <->
  exists x : F20.S5,
    relabelled_galois_image i \subset F20.standard_F20 :^ x.
Proof.
have hcriterion :=
  (@Explicit.lazard_paper_ordered_base_resolvent_has_root_iff_image_sub_conjugate
    rat L cyclic_base_subfield cyclic_splitting_subfield
    cyclic_splitting_galois 5 F20.standard_F20
    (ThetaAdapter.lazard_theta_invariant
      (subvs_of cyclic_base_subfield))
    (ThetaAdapter.lazard_theta_exact_stabilizer ratr_base)
    cyclic_base_polynomial (relabelled_roots_subfield i)
    (cyclic_ordered_root_presentation i)
    (cyclic_paper_theta_resolvent_separable i)).
move: hcriterion.
rewrite -/cyclic_paper_theta_resolvent
  -/cyclic_ordered_gal_perm cyclic_ordered_gal_imageE.
by [].
Qed.

(* -------------------------------------------------------------------- *)
(** * The standard five-cycle occurs in the selected actual image *)

(** The standard [C5] is a Sylow-five subgroup of its normalizer [F20]. *)
Lemma standard_C5_sylow_standard_F20 :
  5.-Sylow(F20.standard_F20) F20.standard_C5.
Proof.
rewrite pHallE (normG F20.standard_C5)
  F20.card_standard_C5 F20.card_standard_F20.
by [].
Qed.

(** An order-five element of [F20] generates another Sylow-five subgroup. *)
Lemma order_five_cycle_sylow_standard_F20
    (x : F20.S5) (hxF20 : x \in F20.standard_F20)
    (hxorder : #[x] = 5%N) :
  5.-Sylow(F20.standard_F20) <[x]>.
Proof.
rewrite pHallE cycle_subG hxF20 -orderE hxorder
  F20.card_standard_F20.
by [].
Qed.

(** Since [F20] is the normalizer of the standard [C5], Sylow conjugacy
    inside [F20] identifies every such cyclic subgroup with that [C5]. *)
Lemma order_five_cycle_eq_standard_C5
    (x : F20.S5) (hxF20 : x \in F20.standard_F20)
    (hxorder : #[x] = 5%N) :
  <[x]> = F20.standard_C5.
Proof.
have hxSylow := order_five_cycle_sylow_standard_F20 hxF20 hxorder.
have [y hyF20 hcycle] := Sylow_trans
  standard_C5_sylow_standard_F20 hxSylow.
have hnormal : F20.standard_C5 :^ y = F20.standard_C5.
  apply/normP.
  exact: hyF20.
by rewrite hcycle hnormal.
Qed.

(** Every order-five element of the standard [F20] therefore generates its
    unique order-five subgroup, the standard [C5].  The Boolean statement is
    retained for compatibility, but its proof performs no enumeration. *)
Definition five_cycle_normalization_certificate : bool :=
  [forall x : [subg F20.standard_F20],
    (#[sgval x] == 5%N) ==>
      (F20.five_cycle \in <[sgval x]>)].

Lemma five_cycle_normalization_certificate_true :
  five_cycle_normalization_certificate.
Proof.
apply/forallP=> x; apply/implyP=> /eqP hxorder.
rewrite (order_five_cycle_eq_standard_C5 (valP x) hxorder).
exact: cycle_id F20.five_cycle.
Qed.

(** Conjugation preserves order, so the subgroup-local certificate applies
    to any conjugate of the standard five-cycle which lies in [F20]. *)
Lemma five_cycle_mem_cycle_conjugate_of_mem_standard_F20
    (a : F20.S5)
    (ha : F20.five_cycle ^ a \in F20.standard_F20) :
  F20.five_cycle \in <[F20.five_cycle ^ a]>.
Proof.
pose x : [subg F20.standard_F20] :=
  Sub (F20.five_cycle ^ a) ha.
have hcert := forallP five_cycle_normalization_certificate_true x.
apply: (implyP hcert).
by rewrite /x /= orderJ F20.order_five_cycle.
Qed.

(** Rationality of the selected theta value puts every selected Galois
    permutation in the displayed standard [F20]. *)
Lemma selected_galois_image_sub_standard_F20
    (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value canonical_roots i = ratrL q) :
  selected_galois_image i \subset F20.standard_F20.
Proof.
apply/subsetP=> x.
rewrite /selected_galois_image mem_conjg=> hx.
rewrite /GA.quintic_galois_image in hx.
case/morphimP: hx=> g _ gGal hxg.
have hmem := @ID.lazard_selected_gal_perm_mem_standard_F20
  Bridge.cyclic_depressed_data
  Bridge.cyclic_depressed_Q_irreducible i q hi g.
move: hmem.
by rewrite -hxg conjgKV.
Qed.

(** Transitivity of the irreducible quintic, together with the preceding
    containment, forces the selected image to contain the literal standard
    five-cycle. *)
Lemma five_cycle_mem_selected_galois_image
    (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value canonical_roots i = ratrL q) :
  F20.five_cycle \in selected_galois_image i.
Proof.
have [s hs] := Five.transitive_S5_contains_conjugate_five_cycle
  (@GA.quintic_galois_image_transitive
    p p_size Bridge.cyclic_depressed_Q_irreducible).
have hselected :
    (F20.five_cycle ^ s) ^ F20.representative i \in
      selected_galois_image i.
  by rewrite /selected_galois_image mem_conjg conjgK.
have hstandard :
    (F20.five_cycle ^ s) ^ F20.representative i \in
      F20.standard_F20 :=
  subsetP (selected_galois_image_sub_standard_F20 hi) _ hselected.
have hcycle :
    F20.five_cycle \in
      <[F20.five_cycle ^ (s * F20.representative i)]>.
  apply: five_cycle_mem_cycle_conjugate_of_mem_standard_F20.
  by rewrite conjgM.
have hcyclesub :
    <[F20.five_cycle ^ (s * F20.representative i)]> \subset
      selected_galois_image i.
  rewrite cycle_subG -conjgM.
  exact: hselected.
exact: subsetP hcyclesub _ hcycle.
Qed.

(** The corrected containment is precisely the conjugate selected by the
    non-base coset. *)
Lemma relabelled_galois_image_sub_relabelled_F20
    (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value canonical_roots i = ratrL q) :
  relabelled_galois_image i \subset Finite.relabelled_F20.
Proof.
rewrite /relabelled_galois_image /Finite.relabelled_F20.
exact: conjSg (selected_galois_image_sub_standard_F20 hi).
Qed.

(** The displayed standard-[F20] conclusion actually fails: the relabelled
    image contains the concrete conjugated five-cycle already proved to lie
    outside that displayed subgroup. *)
Lemma relabelled_galois_image_not_sub_standard_F20
    (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value canonical_roots i = ratrL q) :
  ~~ (relabelled_galois_image i \subset F20.standard_F20).
Proof.
apply/negP=> hsub.
have hfive : F20.five_cycle \in selected_galois_image i :=
  five_cycle_mem_selected_galois_image hi.
have hbad : Finite.three_conjugated_five_cycle \in
    relabelled_galois_image i.
  rewrite /Finite.three_conjugated_five_cycle
    /relabelled_galois_image mem_conjg conjgK.
  exact: hfive.
have hstandard := subsetP hsub _ hbad.
move: Finite.three_conjugated_five_cycle_notin_standard_F20.
by rewrite hstandard.
Qed.

(* -------------------------------------------------------------------- *)
(** * The actual scalar resolvent and the closed cyclic example *)

(** The executable coefficient computation supplies a genuine base-field
    root of the scalar resolvent on the canonical roots. *)
Lemma exists_cyclic_scalar_resolvent_base_root :
  exists q : rat,
    root (TV.quintic_scalar_resolvent canonical_roots) (ratrL q).
Proof.
have hsemantic :=
  (proj1 (@CD.quintic_scaled_resolvent_has_rational_root_correct
    L ratrL canonical_roots Bridge.cyclic_depressed_data
    CD.canonical_quintic_padded_vieta
    (CD.canonical_quintic_resolvent_scale_nonzero
      Bridge.cyclic_depressed_Q_irreducible)))
    Bridge.cyclic_depressed_resolvent_has_rational_root.
exact: hsemantic.
Qed.

Lemma relabelled_scalar_resolvent_base_root
    (i : 'I_6) (q : rat)
    (hq : root (TV.quintic_scalar_resolvent canonical_roots) (ratrL q)) :
  root (TV.quintic_scalar_resolvent (relabelled_roots i)) (ratrL q).
Proof.
move: hq.
rewrite /relabelled_roots /ID.lazard_selected_roots
  !TV.quintic_scalar_resolvent_permute.
by [].
Qed.

(** Transport the concrete scalar root all the way back through the
    top-subfield projection and the generic paper-resolvent scalar extension.
    Thus the base root used in the literal criterion is a root of the
    generic resolver itself. *)
Lemma cyclic_paper_theta_resolvent_base_root
    (i : 'I_6) (q : rat)
    (hq : root (TV.quintic_scalar_resolvent canonical_roots) (ratrL q)) :
  root (cyclic_paper_theta_resolvent i) (ratr_base q).
Proof.
rewrite -(mapf_root cyclic_base_embed
  (cyclic_paper_theta_resolvent i) (ratr_base q)).
rewrite cyclic_paper_theta_resolvent_map_eq_scalar.
rewrite -(mapf_root
  (vsval : {rmorphism subvs_of cyclic_splitting_subfield -> L})
  (TV.quintic_scalar_resolvent (relabelled_roots_subfield i))
  (cyclic_base_embed (ratr_base q))).
rewrite map_subfield_scalar_resolvent.
have hvalue :
    vsval (cyclic_base_embed (ratr_base q)) = ratrL q.
  move: (fmorph_eq_rat
    ((vsval : {rmorphism subvs_of cyclic_splitting_subfield -> L}) \o
      cyclic_base_embed \o ratr_base) q).
  by rewrite /ratrL char0_ratrE.
rewrite hvalue.
exact: relabelled_scalar_resolvent_base_root hq.
Qed.

Lemma relabelled_scalar_resolvent_separable (i : 'I_6) :
  separable_poly (TV.quintic_scalar_resolvent (relabelled_roots i)).
Proof.
rewrite /relabelled_roots /ID.lazard_selected_roots
  !TV.quintic_scalar_resolvent_permute.
exact: (@Sep.canonical_quintic_scalar_resolvent_separable
  Bridge.cyclic_depressed_data
  Bridge.cyclic_depressed_Q_irreducible).
Qed.

(** Closed polynomial-level counterexample to the fixed displayed subgroup
    converse.  The conclusion simultaneously records:

    - irreducibility of the actual rational quintic;
    - a duplicate-free exact ordering of all five roots;
    - the literal five-factor polynomial identity;
    - the genuine splitting-field Galois action on that ordering;
    - a base-field root and separability of the specialized resolvent;
    - containment in the correct conjugate [F20]; and
    - failure of containment in the displayed standard [F20]. *)
Theorem cyclic_quintic_realizes_fixed_displayed_subgroup_failure :
  exists (q : rat) (i : 'I_6),
    irreducible_poly p /\
    injective (tnth (relabelled_roots i)) /\
    map_poly ratrL p =
      \prod_(z <- relabelled_roots i) ('X - z%:P) /\
    (forall g : gal_of {:L},
      map_tuple g (relabelled_roots i) =
        TV.permute_quintic_roots (relabelled_gal_perm i g)
          (relabelled_roots i)) /\
    root (TV.quintic_scalar_resolvent (relabelled_roots i))
      (ratrL q) /\
    separable_poly
      (TV.quintic_scalar_resolvent (relabelled_roots i)) /\
    relabelled_galois_image i \subset Finite.relabelled_F20 /\
    ~~ (relabelled_galois_image i \subset F20.standard_F20).
Proof.
have [q hq] := exists_cyclic_scalar_resolvent_base_root.
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff
    canonical_roots (ratrL q))) hq.
exists q, i; split; first exact: Bridge.cyclic_depressed_Q_irreducible.
split; first exact: relabelled_roots_injective.
split; first exact: relabelled_roots_factorization.
split; first exact: relabelled_roots_gal.
split; first exact: relabelled_scalar_resolvent_base_root hq.
split; first exact: relabelled_scalar_resolvent_separable.
split.
- exact: relabelled_galois_image_sub_relabelled_F20 hi.
- exact: relabelled_galois_image_not_sub_standard_F20 hi.
Qed.

(** Closed endpoint connecting the realized counterexample to the literal
    generic paper resolver and to the corrected generic Theorem 1.  It
    records the scalar-extension equality, a descended base root,
    separability, the generic root/conjugate-containment equivalence, the
    actual correct conjugate containment, and failure for the displayed
    standard [F20]. *)
Theorem cyclic_quintic_invokes_literal_corrected_theorem_one :
  exists (q : rat) (i : 'I_6),
    map_poly cyclic_base_embed (cyclic_paper_theta_resolvent i) =
      TV.quintic_scalar_resolvent (relabelled_roots_subfield i) /\
    root (cyclic_paper_theta_resolvent i) (ratr_base q) /\
    separable_poly (cyclic_paper_theta_resolvent i) /\
    ((exists z : subvs_of cyclic_base_subfield,
        root (cyclic_paper_theta_resolvent i) z) <->
      exists x : F20.S5,
        relabelled_galois_image i \subset F20.standard_F20 :^ x) /\
    relabelled_galois_image i \subset Finite.relabelled_F20 /\
    ~~ (relabelled_galois_image i \subset F20.standard_F20).
Proof.
have [q hq] := exists_cyclic_scalar_resolvent_base_root.
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff
    canonical_roots (ratrL q))) hq.
exists q, i; split.
- exact: cyclic_paper_theta_resolvent_map_eq_scalar.
- split.
  + exact: cyclic_paper_theta_resolvent_base_root hq.
  + split.
    * exact: cyclic_paper_theta_resolvent_separable.
    * split.
      { exact: cyclic_paper_theta_resolvent_has_root_iff_image_sub_conjugate. }
      split.
      { exact: relabelled_galois_image_sub_relabelled_F20 hi. }
      exact: relabelled_galois_image_not_sub_standard_F20 hi.
Qed.

Print Assumptions five_cycle_normalization_certificate_true.
Print Assumptions relabelled_roots_gal.
Print Assumptions cyclic_quintic_realizes_fixed_displayed_subgroup_failure.
Print Assumptions cyclic_paper_theta_resolvent_map_eq_scalar.
Print Assumptions cyclic_ordered_gal_permE.
Print Assumptions cyclic_ordered_gal_imageE.
Print Assumptions cyclic_paper_theta_resolvent_has_root_iff_image_sub_conjugate.
Print Assumptions cyclic_quintic_invokes_literal_corrected_theorem_one.

End PolynomialFormulasLazardGeneralResolventRealizedCounterexample.
