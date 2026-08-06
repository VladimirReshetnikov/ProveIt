From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import AbelRuffini.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Module PolynomialFormulasLowDegreeRadicals.

(** Small symmetric groups are solvable.  We prove the nontrivial [S_4]
    case structurally, without reducing the Boolean definition of
    [solvable] over the finite group. *)

Lemma sylow3_count_order6 (n : nat) :
    (n %| 6)%N -> (n %% 3 = 1)%N -> n = 1%N.
Proof.
move=> hn hmod.
have hn6 : (n <= 6)%N := @dvdn_leq n 6 isT hn.
move: hn6 hn hmod.
case: n => [|[|[|[|[|[|[|n]]]]]]] //=.
Qed.

Lemma card6_solvable (gT : finGroupType) (G : {group gT}) :
    #|G| = 6%N -> solvable G.
Proof.
move=> oG.
have hcardSyl : #|'Syl_3(G)| == 1%N.
  apply/eqP/sylow3_count_order6.
  - move: (@card_Syl_dvd 3 gT G).
    by rewrite oG.
  - exact: (@card_Syl_mod 3 gT G isT).
have [P sylP nP] :=
  elimT (@normal_sylowP gT 3 G) hcardSyl.
rewrite (series_sol nP).
apply/andP; split.
- exact: pgroup_sol (pHall_pgroup sylP).
- apply: abelian_sol; apply: cyclic_abelian; apply: cyclic_small.
  rewrite card_quotient ?normal_norm // -divgS ?(normal_sub nP) //.
  rewrite (card_Hall sylP) oG p_part.
  by [].
Qed.

Lemma card_le6_solvable (gT : finGroupType) (G : {group gT}) :
    (#|G| <= 6)%N -> solvable G.
Proof.
move=> hG.
case oG: #|G| hG => [|[|[|[|[|[|[|n]]]]]]] //= _.
- move: (cardG_gt0 G); by rewrite oG.
- have -> : G :=: 1 by exact: card1_trivg oG.
  exact: solvable1.
- apply: abelian_sol; apply: cyclic_abelian; apply: cyclic_small.
  by rewrite oG.
- apply: abelian_sol; apply: cyclic_abelian; apply: cyclic_small.
  by rewrite oG.
- apply: (@pgroup_sol _ 2).
  by rewrite /pgroup oG.
- apply: abelian_sol; apply: cyclic_abelian; apply: prime_cyclic.
  by rewrite oG.
- exact: card6_solvable oG.
Qed.

Lemma Alt_card4_solvable (T : finType) :
    #|T| = 4%N -> solvable 'Alt_T.
Proof.
move=> oT.
have oA : #|'Alt_T| = 12%N.
  apply: double_inj.
  by rewrite -mul2n card_Alt oT.
have ntA : 'Alt_T :!=: 1 by rewrite -cardG_gt1 oA.
have nsimp := not_simple_Alt_4 oT.
have exH : [exists H : {group {perm T}},
    [&& H <| 'Alt_T, H :!=: 1 & H :!=: 'Alt_T]].
  case hEx: [exists H : {group {perm T}},
      [&& H <| 'Alt_T, H :!=: 1 & H :!=: 'Alt_T]] => //.
  have noH : ~~ [exists H : {group {perm T}},
      [&& H <| 'Alt_T, H :!=: 1 & H :!=: 'Alt_T]] by rewrite hEx.
  move/existsPn: noH=> noH.
  case/negP: nsimp.
  apply/simpleP; split=> // H nHA.
  case hH1: (H :==: 1).
  - left; exact/eqP.
  - right; apply/eqP.
    move: (noH H).
    rewrite nHA hH1.
    by rewrite /= negbK.
have [H /and3P[nHA ntH neqHA]] := existsP exH.
have prHA : H \proper 'Alt_T.
  by rewrite properEneq neqHA (normal_sub nHA).
have idx_gt1 : (1 < #|'Alt_T : H|)%N.
  by rewrite indexg_gt1 (proper_subn prHA).
have H_gt1 : (1 < #|H|)%N by rewrite cardG_gt1.
have hlag := Lagrange (normal_sub nHA).
rewrite oA in hlag.
have hmul : (#|H| * 2 <= 12)%N.
  have hmul' : (#|H| * 2 <= #|H| * #|'Alt_T : H|)%N.
    rewrite leq_pmul2l ?cardG_gt0 //.
  by rewrite hlag in hmul'.
have hH6 : (#|H| <= 6)%N.
  move: hmul.
  by rewrite -[12%N]/(6 * 2)%N leq_pmul2r.
have himul : (2 * #|'Alt_T : H| <= 12)%N.
  have himul' : (2 * #|'Alt_T : H| <= #|H| * #|'Alt_T : H|)%N.
    rewrite leq_pmul2r ?indexg_gt0 //.
  by rewrite hlag in himul'.
have hi6 : (#|'Alt_T : H| <= 6)%N.
  move: himul.
  by rewrite -[12%N]/(2 * 6)%N leq_pmul2l.
rewrite (series_sol nHA).
apply/andP; split.
- exact: card_le6_solvable hH6.
- apply: card_le6_solvable.
  by rewrite card_quotient ?normal_norm // -divgS ?(normal_sub nHA).
Qed.

Lemma solvable_Sym_ord_le4 n :
  (n <= 4)%N -> solvable 'Sym_('I_n).
Proof.
case: n => [|[|[|[|[|n]]]]] //= _.
- apply: card_le6_solvable.
  by rewrite card_Sym card_ord.
- apply: card_le6_solvable.
  by rewrite card_Sym card_ord.
- apply: card_le6_solvable.
  by rewrite card_Sym card_ord.
- apply: card_le6_solvable.
  by rewrite card_Sym card_ord.
- rewrite (series_sol (Alt_normal 'I_4)).
  apply/andP; split.
  + exact: Alt_card4_solvable (card_ord 4).
  + apply: card_le6_solvable.
    rewrite card_quotient.
    2: exact: normal_norm (Alt_normal 'I_4).
    by rewrite Alt_index ?card_ord.
Qed.

(** For an arbitrary nonzero polynomial, the Galois group of its MathComp--
    Abel splitting field acts faithfully on the list of distinct roots.  We
    use [undup] because the polynomial itself need not be square-free. *)

Section LowDegreePolynomial.

Variable p : {poly rat}.
Hypothesis p_neq0 : p != 0.

Let L := numfield p.
Let charL : has_char0 L := char_numfield p.

Definition low_root_seq : seq L := numfield_roots p.
Definition low_distinct_root_seq : seq L := undup low_root_seq.

Lemma low_ratr_factorization :
  map_poly (@ratr L) p %=
    \prod_(x <- low_root_seq) ('X - x%:P).
Proof.
by have := poly_numfield_eqp p_neq0;
   rewrite (eq_map_poly (fmorph_eq_rat _)).
Qed.

Lemma size_low_root_seq : size low_root_seq = (size p).-1.
Proof.
have /eqp_size h := low_ratr_factorization.
move: h; rewrite -(@char0_ratrE L charL)
  size_map_poly size_prod_XsubC polySpred //.
by move=> /succn_inj.
Qed.

Let d := size low_distinct_root_seq.

Let eq_size_low_distinct_root_seq : size low_distinct_root_seq == d.
Proof. by rewrite /d eqxx. Qed.

Definition low_distinct_root_tuple : d.-tuple L :=
  Tuple eq_size_low_distinct_root_seq.

Lemma tnth_low_distinct_root_tuple i :
  tnth low_distinct_root_tuple i = nth 0 low_distinct_root_seq i.
Proof.
by rewrite /low_distinct_root_tuple (tnth_nth 0) /=.
Qed.

Lemma low_distinct_root_seq_uniq : uniq low_distinct_root_seq.
Proof. exact: undup_uniq _. Qed.

Lemma low_distinct_root_tuple_injective :
  injective (tnth low_distinct_root_tuple).
Proof.
move=> i j hij; apply: val_inj.
apply: (uniqP 0 low_distinct_root_seq_uniq);
  rewrite ?inE ?ltn_ord //.
by move: hij; rewrite !tnth_low_distinct_root_tuple.
Qed.

Lemma low_gal_root_perm_eq (g : gal_of {:L}) :
  perm_eq [seq g x | x <- low_root_seq] low_root_seq.
Proof.
apply: prod_XsubC_eq; apply/eqP.
rewrite -eqp_monic ?monic_prod_XsubC //.
rewrite -(eqp_rtrans low_ratr_factorization) big_map.
apply: (@eqp_trans _ (map_poly (g \o (@ratr L)) p)); last first.
  apply/eqpW/eq_map_poly=> x /=.
  rewrite (fixed_gal _ (gal1 g)) ?sub1v //.
  by rewrite -alg_num_field rpredZ ?mem1v.
rewrite map_poly_comp /=.
have := low_ratr_factorization; rewrite -(eqp_map g) /=.
move=> /eqp_rtrans /= ->; apply/eqpW; rewrite rmorph_prod /=.
by apply: eq_bigr=> x; rewrite rmorphB /= map_polyX map_polyC /=.
Qed.

Lemma low_gal_perm_eq (g : gal_of {:L}) :
  perm_eq [seq g x | x <- low_distinct_root_tuple]
    low_distinct_root_tuple.
Proof.
change (perm_eq [seq g x | x <- low_distinct_root_seq]
  low_distinct_root_seq).
rewrite -(@undup_map_inj _ _ g (fmorph_inj g) low_root_seq).
exact/perm_undup/perm_mem/low_gal_root_perm_eq.
Qed.

Definition low_gal_perm (g : gal_of {:L}) : 'S_d :=
  projT1 (sig_eqW (tuple_permP (low_gal_perm_eq g))).

Lemma low_gal_permP (g : gal_of {:L}) (i : 'I_d) :
  tnth low_distinct_root_tuple (low_gal_perm g i) =
    g (tnth low_distinct_root_tuple i).
Proof.
rewrite !tnth_low_distinct_root_tuple /low_gal_perm;
  case: sig_eqW=> /= s.
move=> /(congr1 (((@nth _ 0))^~ i)).
rewrite (nth_map 0) ?size_low_root_seq // => ->.
Unshelve.
by rewrite (nth_map i) ?size_enum_ord //
  nth_ord_enum tnth_low_distinct_root_tuple.
Qed.

Lemma low_gal_perm_is_morphism :
  {in ('Gal({:L} / 1%AS))%G &,
    {morph low_gal_perm :
      x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move=> u v _ _; apply/permP=> i.
apply: low_distinct_root_tuple_injective.
by rewrite permM !low_gal_permP galM // ?memvf.
Qed.

Canonical low_gal_perm_morphism :=
  Morphism low_gal_perm_is_morphism.

Lemma injm_low_gal_perm : ('injm low_gal_perm)%g.
Proof.
apply/subsetP=> u /mker /= gu1.
apply/set1gP/eqP/gal_eqP=> x x_full.
have fixdistinct :
    all (fun r => frel u r r) low_distinct_root_seq.
  apply/allP=> r /= /(nthP 0)[i].
  rewrite /d=> ltd <-.
  have hfix : low_gal_perm u (Ordinal ltd) = Ordinal ltd.
    by rewrite gu1 perm1.
  have hroot := low_gal_permP u (Ordinal ltd).
  rewrite hfix in hroot.
  rewrite !tnth_low_distinct_root_tuple in hroot.
  apply/eqP.
  exact: esym hroot.
have fixroots : all (fun r => frel u r r) low_root_seq.
  apply/allP=> r rroot.
  apply: (allP fixdistinct).
  by rewrite /low_distinct_root_seq mem_undup.
have x_adjoin : x \in <<1 & low_root_seq>>%VS.
  by rewrite /low_root_seq adjoin_numfield_roots.
clear x_full fixdistinct.
elim/last_ind: low_root_seq x x_adjoin fixroots=> [|s r IHs] x.
  rewrite adjoin_nil subfield_closed=> x1 _.
  by rewrite (fixed_gal _ (gal1 u)) ?sub1v ?gal_id.
rewrite adjoin_rcons=> /Fadjoin_poly_eq <-.
rewrite all_rcons=> /andP[/eqP ur /IHs us].
rewrite gal_id -horner_map /= ur map_poly_id //.
move=> a /(nthP 0)[i i_lt <-]; rewrite us ?gal_id //.
exact/polyOverP/Fadjoin_polyOver.
Qed.

Definition low_galois_image : {group 'S_d} :=
  low_gal_perm @* 'Gal({:L} / 1%AS).

Lemma low_galois_image_solvableE :
  solvable low_galois_image = solvable 'Gal({:L} / 1%AS).
Proof.
exact: injm_sol injm_low_gal_perm (subxx _).
Qed.

Lemma size_low_distinct_root_seq_le4 :
  (size p <= 5)%N -> (d <= 4)%N.
Proof.
move=> p_size_le5.
have hdu : (d <= size low_root_seq)%N.
  rewrite /d /low_distinct_root_seq.
  exact: size_undup _.
have hrs4 : (size low_root_seq <= 4)%N.
  rewrite size_low_root_seq.
  move: (leq_sub2r 1 p_size_le5).
  by rewrite !subn1.
exact: leq_trans hdu hrs4.
Qed.

Lemma low_degree_galois_solvable :
  (size p <= 5)%N -> solvable 'Gal({:L} / 1%AS).
Proof.
move=> p_size_le5.
rewrite -low_galois_image_solvableE.
have hsub : low_galois_image \subset 'Sym_('I_d) := subsetT _.
exact: solvableS hsub (solvable_Sym_ord_le4
  (size_low_distinct_root_seq_le4 p_size_le5)).
Qed.

Theorem low_degree_radical_formula :
  (size p <= 5)%N ->
  LeanProofs.PolynomialFormulasAbelRuffini.radical_formula_solves p.
Proof.
move=> p_size_le5.
apply: (LeanProofs.PolynomialFormulasAbelRuffini.radical_formula_solvesP
  p_neq0).1.
exact: elimT (AbelGaloisPolyRat p)
  (low_degree_galois_solvable p_size_le5).
Qed.

End LowDegreePolynomial.

End PolynomialFormulasLowDegreeRadicals.
