From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import map_gal.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticChapman.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Chapman's scalar-resolvent no-collision argument over an arbitrary base
    field.  The only characteristic input is the explicit invertibility of
    five. *)
Module PolynomialFormulasQuinticChapmanField.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Module TV := PolynomialFormulasQuinticThetaValues.
Module QC := PolynomialFormulasQuinticChapman.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Section BaseFieldChapman.

Variables (K F : fieldType).
Variable kF : {rmorphism K -> F}.

(** Chapman's center equation descends its distinguished root to the base
    field whenever five is nonzero there. *)
Lemma chapman_center_is_base (roots : 5.-tuple F)
    (five_neq0 : (5%:R : K) != 0)
    (hcenter :
      5%:R * tnth roots o1 =
        tnth roots o0 + tnth roots o1 + tnth roots o2 +
          tnth roots o3 + tnth roots o4)
    (hsum : exists q : K,
      tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4 = kF q) :
  exists q : K, tnth roots o1 = kF q.
Proof.
case: hsum=> q hsum.
have h5F : (5%:R : F) != 0.
  by rewrite -[5%:R](rmorph_nat kF 5) fmorph_eq0 five_neq0.
exists (q / 5%:R).
apply: (mulIf h5F).
rewrite rmorph_div ?unitfE // rmorph_nat divfK //.
by rewrite mulrC hcenter hsum.
Qed.

Variable p : {poly K}.

(** A degree-five irreducible polynomial cannot have a root in the embedded
    base field. *)
Lemma irreducible_quintic_root_not_base
    (p_size : size p = 6%N) (p_irr : irreducible_poly p) x :
  root (map_poly kF p) x -> forall q : K, x <> kF q.
Proof.
move=> hx q hxq; subst x.
have hpq : root p q.
  move: hx.
  by rewrite !rootE horner_map fmorph_eq0.
have hdiv : ('X - q%:P) %| p by rewrite dvdp_XsubCl.
have hsize : size ('X - q%:P) != 1%N by rewrite size_XsubC.
have heqp := p_irr.2 _ hsize hdiv.
have hs := eqp_size heqp.
by move: hs; rewrite size_XsubC p_size.
Qed.

Variable roots : 5.-tuple F.

Lemma chapman_collisions_impossible_for_irreducible_quintic_over_base
    (five_neq0 : (5%:R : K) != 0)
    (p_size : size p = 6%N) (p_irr : irreducible_poly p)
    (hroots : injective (tnth roots))
    (hroot1 : root (map_poly kF p) (tnth roots o1))
    (hsum : exists q : K,
      tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4 = kF q) :
  ~ (TV.quintic_theta_value roots theta_i1 =
       TV.quintic_theta_value roots theta_i2 /\
     TV.quintic_theta_value roots theta_i3 =
       TV.quintic_theta_value roots theta_i4).
Proof.
move=> [h12 h34].
have hcenter := QC.chapman_five_mul_center_of_collisions hroots h12 h34.
have [q hq] := chapman_center_is_base five_neq0 hcenter hsum.
have hnotbase := irreducible_quintic_root_not_base
  p_size p_irr hroot1 (q := q).
exact: hnotbase hq.
Qed.

(** The exact arbitrary-base-field Chapman theorem.  Only the explicitly
    stated action of a five-cycle endomorphism is needed. *)
Theorem quintic_theta_value_injective_of_five_cycle_endomorphism_over_base
    (five_neq0 : (5%:R : K) != 0)
    (p_size : size p = 6%N) (p_irr : irreducible_poly p)
    (hroots : injective (tnth roots))
    (hroot1 : root (map_poly kF p) (tnth roots o1))
    (hsum : exists q : K,
      tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4 = kF q)
    (sigma : {rmorphism F -> F})
    (hsigma : forall k : 'I_5,
      sigma (tnth roots k) = tnth roots (five_cycle k)) :
  injective (TV.quintic_theta_value roots).
Proof.
move=> i j hij.
case hijb: (i == j).
- exact/eqP.
- exfalso.
  have hne : i != j by rewrite hijb.
  have hstep a b
      (hab : TV.quintic_theta_value roots a =
        TV.quintic_theta_value roots b) :
      TV.quintic_theta_value roots (chapman_cycle_index a) =
        TV.quintic_theta_value roots (chapman_cycle_index b).
    have hs := congr1 sigma hab.
    by rewrite !QC.quintic_theta_value_five_cycle_rmap in hs.
  have hcoll := five_cycle_collision_propagates hstep hne hij.
  exact: (chapman_collisions_impossible_for_irreducible_quintic_over_base
    five_neq0 p_size p_irr hroots hroot1 hsum hcoll).
Qed.

(** Pairwise distinct theta values give literal separability of the six
    linear-factor scalar resolvent. *)
Theorem quintic_scalar_resolvent_separable_of_five_cycle_endomorphism_over_base
    (five_neq0 : (5%:R : K) != 0)
    (p_size : size p = 6%N) (p_irr : irreducible_poly p)
    (hroots : injective (tnth roots))
    (hroot1 : root (map_poly kF p) (tnth roots o1))
    (hsum : exists q : K,
      tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4 = kF q)
    (sigma : {rmorphism F -> F})
    (hsigma : forall k : 'I_5,
      sigma (tnth roots k) = tnth roots (five_cycle k)) :
  separable_poly (TV.quintic_scalar_resolvent roots).
Proof.
rewrite /TV.quintic_scalar_resolvent separable_prod_XsubC.
apply/tuple_uniqP=> i j hij.
apply: (quintic_theta_value_injective_of_five_cycle_endomorphism_over_base
  five_neq0 p_size p_irr hroots hroot1 hsum sigma hsigma).
by move: hij; rewrite !TV.tnth_quintic_theta_values.
Qed.

Print Assumptions quintic_theta_value_injective_of_five_cycle_endomorphism_over_base.
Print Assumptions quintic_scalar_resolvent_separable_of_five_cycle_endomorphism_over_base.

End BaseFieldChapman.

(** * Canonical splitting-field specialization

    The preceding theorem asks for a root ordering and an endomorphism acting
    as the standard five-cycle.  Those data are not additional assumptions
    for an irreducible quintic.  In a splitting-field presentation the Galois
    action is transitive; Cauchy's theorem supplies an element of order five,
    and a noncanonical reindexing conjugates its action to [five_cycle].

    Neither the ordering nor the Galois element is uniquely determined.  The
    result below is therefore existential (and proof-relevant), not a
    computationally canonical choice.  The explicit [splittingFieldFor]
    premise records both splitting and generation/normality; separability is
    derived from irreducibility, degree five, and [5 != 0]. *)

Section QuinticSeparability.

Variable K : fieldType.
Variable p : {poly K}.

(** In any characteristic other than five, an irreducible quintic is
    separable: the degree-four coefficient of its derivative is five times
    its nonzero leading coefficient. *)
Lemma irreducible_quintic_separable_of_five_neq0
    (five_neq0 : (5%:R : K) != 0)
    (p_size : size p = 6%N) (p_irr : irreducible_poly p) :
  separable_poly p.
Proof.
have p_neq0 : p != 0 by rewrite -size_poly_eq0 p_size.
have p5E : p`_5 = lead_coef p by rewrite lead_coefE p_size.
have p5_neq0 : p`_5 != 0.
  by rewrite p5E lead_coef_eq0 p_neq0.
have p_deriv_neq0 : p^`() != 0.
  apply/eqP=> pder0.
  have hcoef := congr1 (fun q : {poly K} => q`_4) pder0.
  move/eqP: hcoef.
  by rewrite coef_deriv coef0 -mulr_natl mulf_eq0 five_neq0 p5_neq0.
rewrite separable_poly.unlock.
apply/coprimepP=> d; have [sp_gt1 eqp] := p_irr=> /eqp.
rewrite size_poly_eq1; have [//|dN1 /(_ isT)] := boolP (d %= 1).
move=> /eqp_dvdl-> hdiv.
have hle : size p <= size p^`() := dvdp_leq p_deriv_neq0 hdiv.
have hlt : size p^`() < size p := lt_size_deriv p_neq0.
by move: hlt; rewrite ltnNge hle.
Qed.

End QuinticSeparability.

(** Every transitive subgroup of [S5] contains a conjugate of the literal
    standard five-cycle.  This is the field-independent Cauchy/Sylow step. *)
Lemma transitive_S5_contains_conjugate_five_cycle_over
    (G : {group S5}) :
  [transitive G, on [set : 'I_5] | 'P] ->
  exists s : S5, (five_cycle ^ s)%g \in G.
Proof.
move=> htrans.
have h5G : (5 %| #|G|)%N.
  move: (atrans_dvd htrans).
  by rewrite cardsT card_ord.
have [c cG hcorder] := Cauchy (isT : prime 5) h5G.
have hcSylow : 5.-Sylow([set : S5]) <[c]>.
  rewrite pHallE subsetT -orderE hcorder cardsT /S5 card_Sn.
  rewrite andTb p_part (logn_fact 5) //.
  do 5! rewrite big_nat_recr //=.
  by rewrite big_geq //=.
have [s _ hcycle] := Sylow_trans standard_C5_sylow hcSylow.
exists s.
have hcsub : (<[c]>%G \subset G).
  apply/subsetP=> x /cycleP[i ->].
  exact: groupX cG.
apply: (subsetP hcsub).
rewrite hcycle -cycleJ.
exact: cycle_id (five_cycle ^ s).
Qed.

Section SplittingPresentation.

Variables (K : fieldType) (L : splittingFieldType K).
Variable p : {poly K}.
Hypothesis five_neq0 : (5%:R : K) != 0.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.
Variable root_seq : seq L.
Hypothesis p_factor :
  map_poly (in_alg L) p %=
    \prod_(x <- root_seq) ('X - x%:P).
Hypothesis root_seq_adjoins : <<1 & root_seq>>%VS = fullv.

Let p_neq0 : p != 0.
Proof. by rewrite -size_poly_eq0 p_size. Qed.

Let p_sep : separable_poly p :=
  irreducible_quintic_separable_of_five_neq0
    five_neq0 p_size p_irr.

Lemma size_splitting_quintic_root_seq : size root_seq = 5.
Proof.
have /eqp_size h := p_factor.
move: h; rewrite size_map_poly size_prod_XsubC p_size.
by move=> /succn_inj.
Qed.

Let eq_size_splitting_quintic_root_seq : size root_seq == 5.
Proof. exact/eqP/size_splitting_quintic_root_seq. Qed.

Definition splitting_quintic_root_tuple : 5.-tuple L :=
  Tuple eq_size_splitting_quintic_root_seq.

Lemma tnth_splitting_quintic_root_tuple i :
  tnth splitting_quintic_root_tuple i = nth 0 root_seq i.
Proof.
by rewrite /splitting_quintic_root_tuple (tnth_nth 0) /=.
Qed.

Lemma splitting_quintic_root_seq_uniq : uniq root_seq.
Proof.
rewrite -separable_prod_XsubC -(eqp_separable p_factor).
by rewrite separable_map p_sep.
Qed.

Lemma splitting_quintic_root_tuple_injective :
  injective (tnth splitting_quintic_root_tuple).
Proof.
move=> i j hij; apply: val_inj.
apply: (uniqP 0 splitting_quintic_root_seq_uniq);
  rewrite ?inE ?size_splitting_quintic_root_seq ?ltn_ord //.
by move: hij; rewrite /splitting_quintic_root_tuple
  !(@tnth_nth 5 L 0) /=.
Qed.

Lemma splitting_quintic_root_characterization :
  root (map_poly (in_alg L) p) =i root_seq.
Proof.
move=> x.
exact: eq_trans (eqp_root p_factor x)
  (root_prod_XsubC root_seq x).
Qed.

Lemma splitting_quintic_all_roots i :
  root (map_poly (in_alg L) p)
    (tnth splitting_quintic_root_tuple i).
Proof.
rewrite splitting_quintic_root_characterization
  tnth_splitting_quintic_root_tuple mem_nth
  ?size_splitting_quintic_root_seq ?ltn_ord //.
Qed.

Lemma splitting_quintic_gal_perm_eq (g : gal_of {:L}) :
  perm_eq [seq g x | x <- splitting_quintic_root_tuple]
    splitting_quintic_root_tuple.
Proof.
apply: prod_XsubC_eq; apply/eqP.
rewrite -eqp_monic ?monic_prod_XsubC //.
rewrite -(eqp_rtrans p_factor) big_map.
apply: (@eqp_trans _ (map_poly (g \o in_alg L) p)); last first.
  apply/eqpW/eq_map_poly=> x /=.
  have hxbase : in_alg L x \in (1%AS : {vspace L}).
    apply/vlineP; exists x.
    by rewrite in_algE.
  exact: fixed_gal (sub1v fullv) (gal1 g) hxbase.
rewrite map_poly_comp /=.
have := p_factor; rewrite -(eqp_map g) /=.
move=> /eqp_rtrans /= ->; apply/eqpW; rewrite rmorph_prod /=.
by apply: eq_bigr=> x; rewrite rmorphB /= map_polyX map_polyC /=.
Qed.

Definition splitting_quintic_gal_perm (g : gal_of {:L}) : S5 :=
  projT1 (sig_eqW (tuple_permP (splitting_quintic_gal_perm_eq g))).

Lemma splitting_quintic_gal_permP (g : gal_of {:L}) (i : 'I_5) :
  tnth splitting_quintic_root_tuple (splitting_quintic_gal_perm g i) =
    g (tnth splitting_quintic_root_tuple i).
Proof.
rewrite !tnth_splitting_quintic_root_tuple
  /splitting_quintic_gal_perm; case: sig_eqW=> /= s.
move=> /(congr1 (((@nth _ 0))^~ i)).
rewrite (nth_map 0) ?size_splitting_quintic_root_seq // => ->.
Unshelve.
by rewrite (nth_map i) ?size_enum_ord //
  nth_ord_enum tnth_splitting_quintic_root_tuple.
Qed.

Lemma splitting_quintic_gal_perm_is_morphism :
  {in ('Gal({:L} / 1%AS))%G &,
    {morph splitting_quintic_gal_perm :
      x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move=> u v _ _; apply/permP=> i; apply/val_inj.
apply: (uniqP 0 splitting_quintic_root_seq_uniq);
  rewrite ?inE ?size_splitting_quintic_root_seq ?ltn_ord //.
by rewrite -!tnth_splitting_quintic_root_tuple permM
  !splitting_quintic_gal_permP galM // ?memvf.
Qed.

Canonical splitting_quintic_gal_perm_morphism :=
  Morphism splitting_quintic_gal_perm_is_morphism.

Lemma splitting_quintic_minPoly_root x :
  x \in root_seq ->
  minPoly 1%VS x %= map_poly (in_alg L) p.
Proof.
move=> xroot.
have px0 : root (map_poly (in_alg L) p) x.
  by rewrite (eqp_root p_factor) root_prod_XsubC.
have hdiv : minPoly 1 x %| map_poly (in_alg L) p.
  rewrite minPoly_dvdp //.
  apply/polyOver1P; by exists p.
have hsize : size (minPoly 1 x) != 1%N by rewrite size_minPoly.
have /polyOver1P[q ->] := minPolyOver 1 x.
rewrite /eqp 2!(dvdp_map (fmorph_inj (in_alg L))).
by rewrite -/(_ %= _) size_map_poly; apply: p_irr.
Qed.

Lemma splitting_quintic_normal : normalField 1%AS fullv.
Proof.
apply/splitting_normalField; first exact: sub1v.
exists (map_poly (in_alg L) p).
- apply/polyOver1P; by exists p.
- exists root_seq; [exact p_factor | exact root_seq_adjoins].
Qed.

Definition splitting_quintic_galois_image : {group S5} :=
  splitting_quintic_gal_perm @* 'Gal({:L} / 1%AS).

Lemma splitting_quintic_galois_image_transitive :
  [transitive splitting_quintic_galois_image,
    on [set : 'I_5] | 'P].
Proof.
rewrite /atrans; apply/imsetP; exists ord0; first by rewrite inE.
apply/setP=> j; rewrite inE.
apply/idP/idP; last by [].
move=> _; apply/orbitP.
have root_mem i : tnth splitting_quintic_root_tuple i \in root_seq.
  by rewrite tnth_splitting_quintic_root_tuple mem_nth
    ?size_splitting_quintic_root_seq ?ltn_ord.
have mroot :
    root (minPoly 1%VS (tnth splitting_quintic_root_tuple ord0))
      (tnth splitting_quintic_root_tuple j).
  have hroot :
      root (minPoly 1%VS (tnth splitting_quintic_root_tuple ord0))
          (tnth splitting_quintic_root_tuple j) =
        (tnth splitting_quintic_root_tuple j \in root_seq) :=
    eq_trans
      (eqp_root (splitting_quintic_minPoly_root (root_mem ord0))
        (tnth splitting_quintic_root_tuple j))
      (splitting_quintic_root_characterization
        (tnth splitting_quintic_root_tuple j)).
  by move: (root_mem j); rewrite -hroot.
have [u gu hu] := normalField_root_minPoly (sub1v fullv)
  splitting_quintic_normal (memvf (tnth splitting_quintic_root_tuple ord0))
  mroot.
exists (splitting_quintic_gal_perm u).
- apply/morphimP; by exists u.
- apply: splitting_quintic_root_tuple_injective.
  by rewrite splitting_quintic_gal_permP hu.
Qed.

Lemma splitting_quintic_galois : galois 1%AS fullv.
Proof.
apply/splitting_galoisField.
exists (map_poly (in_alg L) p); split.
- apply/polyOver1P; by exists p.
- by rewrite separable_map p_sep.
- by exists root_seq.
Qed.

Lemma splitting_quintic_root_sum_base :
  exists q : K,
    \sum_(i : 'I_5) tnth splitting_quintic_root_tuple i = in_alg L q.
Proof.
set z := \sum_(i : 'I_5) tnth splitting_quintic_root_tuple i.
have zfixed : z \in fixedField 'Gal({:L} / 1%AS).
  apply/fixedFieldP; first exact: memvf.
  move=> g gg.
  rewrite /z rmorph_sum /=.
  under [LHS]eq_bigr=> i _ do
    rewrite -splitting_quintic_gal_permP.
  rewrite (reindex_inj
    (@perm_inj _ (splitting_quintic_gal_perm g)^-1)) /=.
  under [LHS]eq_bigr=> i _ do rewrite permKV.
  reflexivity.
have /galois_fixedField fixedE := splitting_quintic_galois.
have zbase : z \in (1%AS : {vspace L}) by rewrite -fixedE.
move/vlineP: zbase=> [q hq].
exists q.
by rewrite /z -in_algE.
Qed.

Lemma splitting_quintic_root_sumE (roots : 5.-tuple L) :
  \sum_(i : 'I_5) tnth roots i =
    tnth roots o0 + tnth roots o1 + tnth roots o2 +
      tnth roots o3 + tnth roots o4.
Proof.
rewrite !big_ord_recl !big_ord0.
have h0 : (@ord0 4) = o0 by apply: val_inj.
have h1 : lift (@ord0 4) (@ord0 3) = o1 by apply: val_inj.
have h2 : lift (@ord0 4) (lift (@ord0 3) (@ord0 2)) = o2
  by apply: val_inj.
have h3 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (@ord0 1))) = o3
  by apply: val_inj.
have h4 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (lift (@ord0 1) (@ord0 0)))) = o4
  by apply: val_inj.
by rewrite h4 h3 h2 h1 h0 addr0 !addrA.
Qed.

Lemma splitting_quintic_root_sum_permute
    (roots : 5.-tuple L) (s : S5) :
  \sum_(i : 'I_5) tnth (TV.permute_quintic_roots s roots) i =
    \sum_(i : 'I_5) tnth roots i.
Proof.
under [LHS]eq_bigr=> i _ do
  rewrite TV.tnth_permute_quintic_roots.
rewrite (reindex_inj (@perm_inj _ s^-1)) /=.
under [LHS]eq_bigr=> i _ do rewrite permKV.
reflexivity.
Qed.

Definition reindexed_splitting_quintic_roots (s : S5) : 5.-tuple L :=
  TV.permute_quintic_roots s splitting_quintic_root_tuple.

Lemma full_splitting_gal_rmorphism_bijective (u : gal_of (L:=L) fullv) :
  bijective (gal_repr u : {rmorphism L -> L}).
Proof.
apply: (@Bijective L L (gal_repr u) (gal_repr (u^-1)%g)).
- move=> x.
  have h := @galM K L fullv u (u^-1)%g x (memvf x).
  rewrite mulgV gal_id in h.
  exact: esym h.
- move=> x.
  have h := @galM K L fullv (u^-1)%g u x (memvf x).
  rewrite mulVg gal_id in h.
  exact: esym h.
Qed.

Theorem splitting_presentation_five_cycle_root_data :
  exists (roots : 5.-tuple L) (sigma : {rmorphism L -> L}),
    [/\
      injective (tnth roots),
      (forall k : 'I_5, root (map_poly (in_alg L) p) (tnth roots k)),
      (exists q : K,
        tnth roots o0 + tnth roots o1 + tnth roots o2 +
          tnth roots o3 + tnth roots o4 = in_alg L q) &
      forall k : 'I_5,
        sigma (tnth roots k) = tnth roots (five_cycle k)].
Proof.
have [s hs] := transitive_S5_contains_conjugate_five_cycle_over
  splitting_quintic_galois_image_transitive.
rewrite /splitting_quintic_galois_image in hs.
case/morphimP: hs=> u _ huGal huperm.
have huperm' : splitting_quintic_gal_perm u =
    (five_cycle ^ s)%g := esym huperm.
exists (reindexed_splitting_quintic_roots s),
  (gal_repr u : {rmorphism L -> L}); split.
- move=> i j.
  rewrite /reindexed_splitting_quintic_roots
    !TV.tnth_permute_quintic_roots=> hij.
  apply: (@perm_inj _ s).
  exact: splitting_quintic_root_tuple_injective hij.
- move=> k.
  rewrite /reindexed_splitting_quintic_roots
    TV.tnth_permute_quintic_roots.
  exact: splitting_quintic_all_roots.
- have [q hq] := splitting_quintic_root_sum_base.
  exists q.
  rewrite -splitting_quintic_root_sumE
    /reindexed_splitting_quintic_roots
    splitting_quintic_root_sum_permute.
  exact: hq.
- move=> k.
  rewrite /reindexed_splitting_quintic_roots
    !TV.tnth_permute_quintic_roots.
  change (u (tnth splitting_quintic_root_tuple (s k)) =
    tnth splitting_quintic_root_tuple (s (five_cycle k))).
  rewrite -splitting_quintic_gal_permP huperm' conjg_permE permK.
  by [].
Qed.

End SplittingPresentation.

Section CanonicalSplittingEndpoint.

Variables (K : fieldType) (L : splittingFieldType K).
Variable p : {poly K}.
Hypothesis five_neq0 : (5%:R : K) != 0.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.
Hypothesis p_splits :
  splittingFieldFor 1%AS (map_poly (in_alg L) p) fullv.

(** The arbitrary-field root-action hypotheses used by Chapman's argument are
    consequences of one explicit splitting-field presentation. *)
Theorem irreducible_quintic_splitting_field_root_data :
  exists (roots : 5.-tuple L) (sigma : {rmorphism L -> L}),
    [/\
      injective (tnth roots),
      (forall k : 'I_5, root (map_poly (in_alg L) p) (tnth roots k)),
      (exists q : K,
        tnth roots o0 + tnth roots o1 + tnth roots o2 +
          tnth roots o3 + tnth roots o4 = in_alg L q) &
      forall k : 'I_5,
        sigma (tnth roots k) = tnth roots (five_cycle k)].
Proof.
case: p_splits=> root_seq p_factor root_seq_adjoins.
exact: (@splitting_presentation_five_cycle_root_data
  K L p five_neq0 p_size p_irr root_seq p_factor root_seq_adjoins).
Qed.

(** Literal separability of the six-factor scalar resolvent, with no
    caller-supplied root ordering or five-cycle action. *)
Theorem irreducible_quintic_scalar_resolvent_separable_over_splitting_field :
  exists roots : 5.-tuple L,
    separable_poly (TV.quintic_scalar_resolvent roots).
Proof.
have [roots [sigma [hroots hall_roots hsum hsigma]]] :=
  irreducible_quintic_splitting_field_root_data.
exists roots.
exact: (@quintic_scalar_resolvent_separable_of_five_cycle_endomorphism_over_base
  K L (in_alg L) p roots five_neq0 p_size p_irr hroots
  (hall_roots o1) hsum sigma hsigma).
Qed.

Print Assumptions irreducible_quintic_splitting_field_root_data.
Print Assumptions irreducible_quintic_scalar_resolvent_separable_over_splitting_field.

End CanonicalSplittingEndpoint.

End PolynomialFormulasQuinticChapmanField.
