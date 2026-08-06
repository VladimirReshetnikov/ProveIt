From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import QuinticF20Data.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

(** The Galois group of the MathComp--Abel splitting field of an
    irreducible rational quintic acts faithfully and transitively on its
    five canonical roots.  This realizes it as a concrete subgroup of
    [S_5], in the same coordinates as the Frobenius subgroup used by the
    Dummit resolvent. *)
Module PolynomialFormulasQuinticGaloisAction.

Import PolynomialFormulasQuinticF20Data.

Section IrreducibleQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.
Let charL : has_char0 L := char_numfield p.

Definition quintic_root_seq : seq L := numfield_roots p.

Let p_neq0 : p != 0.
Proof. by rewrite -size_poly_eq0 p_size. Qed.

Lemma quintic_ratr_factorization :
  map_poly (@ratr L) p %=
    \prod_(x <- quintic_root_seq) ('X - x%:P).
Proof.
by have := poly_numfield_eqp p_neq0;
   rewrite (eq_map_poly (fmorph_eq_rat _)).
Qed.

Lemma size_quintic_root_seq : size quintic_root_seq = 5.
Proof.
have /eqp_size h := quintic_ratr_factorization.
move: h; rewrite -(@char0_ratrE L charL)
  size_map_poly size_prod_XsubC p_size.
by move=> /succn_inj.
Qed.

Let eq_size_quintic_root_seq : size quintic_root_seq == 5.
Proof. exact/eqP/size_quintic_root_seq. Qed.

Definition quintic_root_tuple : 5.-tuple L :=
  Tuple eq_size_quintic_root_seq.

Lemma tnth_quintic_root_tuple i :
  tnth quintic_root_tuple i = nth 0 quintic_root_seq i.
Proof.
by rewrite /quintic_root_tuple (tnth_nth 0) /=.
Qed.

Lemma quintic_root_seq_uniq : uniq quintic_root_seq.
Proof.
rewrite -separable_prod_XsubC
  -(eqp_separable quintic_ratr_factorization).
rewrite -(@char0_ratrE L charL) separable_map separable_poly.unlock.
apply/coprimepP=> d; have [sp_gt1 eqp] := p_irr=> /eqp.
rewrite size_poly_eq1; have [//|dN1 /(_ isT)] := boolP (d %= 1).
move=> /eqp_dvdl-> /dvdp_leq.
rewrite -size_poly_eq0 polyorder.size_deriv.
by case: (size p) sp_gt1=> [|[|n]] //= _; rewrite ltnn; apply.
Qed.

Lemma quintic_root_tuple_injective : injective (tnth quintic_root_tuple).
Proof.
move=> i j hij; apply: val_inj.
apply: (uniqP 0 quintic_root_seq_uniq);
  rewrite ?inE ?size_quintic_root_seq ?ltn_ord //.
by move: hij; rewrite /quintic_root_tuple !(@tnth_nth 5 L 0) /=.
Qed.

Lemma quintic_gal_perm_eq (g : gal_of {:L}) :
  perm_eq [seq g x | x <- quintic_root_tuple] quintic_root_tuple.
Proof.
apply: prod_XsubC_eq; apply/eqP.
rewrite -eqp_monic ?monic_prod_XsubC //.
rewrite -(eqp_rtrans quintic_ratr_factorization) big_map.
apply: (@eqp_trans _ (map_poly (g \o (@ratr L)) p)); last first.
  apply/eqpW/eq_map_poly=> x /=.
  rewrite (fixed_gal _ (gal1 g)) ?sub1v //.
  by rewrite -alg_num_field rpredZ ?mem1v.
rewrite map_poly_comp /=.
have := quintic_ratr_factorization; rewrite -(eqp_map g) /=.
move=> /eqp_rtrans /= ->; apply/eqpW; rewrite rmorph_prod /=.
by apply: eq_bigr=> x; rewrite rmorphB /= map_polyX map_polyC /=.
Qed.

Definition quintic_gal_perm (g : gal_of {:L}) : S5 :=
  projT1 (sig_eqW (tuple_permP (quintic_gal_perm_eq g))).

Lemma quintic_gal_permP (g : gal_of {:L}) (i : 'I_5) :
  tnth quintic_root_tuple (quintic_gal_perm g i) =
    g (tnth quintic_root_tuple i).
Proof.
rewrite !tnth_quintic_root_tuple /quintic_gal_perm;
  case: sig_eqW=> /= s.
move=> /(congr1 (((@nth _ 0))^~ i)).
rewrite (nth_map 0) ?size_quintic_root_seq // => ->.
Unshelve.
by rewrite (nth_map i) ?size_enum_ord //
  nth_ord_enum tnth_quintic_root_tuple.
Qed.

Lemma quintic_gal_perm_is_morphism :
  {in ('Gal({:L} / 1%AS))%G &,
    {morph quintic_gal_perm :
      x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move=> u v _ _; apply/permP=> i; apply/val_inj.
apply: (uniqP 0 quintic_root_seq_uniq);
  rewrite ?inE ?size_quintic_root_seq ?ltn_ord //.
by rewrite -!tnth_quintic_root_tuple permM
  !quintic_gal_permP galM // ?memvf.
Qed.

Canonical quintic_gal_perm_morphism :=
  Morphism quintic_gal_perm_is_morphism.

Lemma injm_quintic_gal_perm : ('injm quintic_gal_perm)%g.
Proof.
apply/subsetP=> u /mker /= gu1.
apply/set1gP/eqP/gal_eqP=> x x_full.
have fixroots : all (fun r => frel u r r) quintic_root_seq.
  apply/allP=> r /= /(nthP 0)[i].
  rewrite size_quintic_root_seq=> lti5 <-.
  have hfix :
      quintic_gal_perm u (Ordinal lti5) = Ordinal lti5.
    by rewrite gu1 perm1.
  have hroot := quintic_gal_permP u (Ordinal lti5).
  rewrite hfix in hroot.
  rewrite !tnth_quintic_root_tuple in hroot.
  apply/eqP.
  exact: esym hroot.
have x_adjoin : x \in <<1 & quintic_root_seq>>%VS.
  by rewrite /quintic_root_seq adjoin_numfield_roots.
clear x_full.
elim/last_ind: quintic_root_seq x x_adjoin fixroots=> [|s r IHs] x.
  rewrite adjoin_nil subfield_closed=> x1 _.
  by rewrite (fixed_gal _ (gal1 u)) ?sub1v ?gal_id.
rewrite adjoin_rcons=> /Fadjoin_poly_eq <-.
rewrite all_rcons=> /andP[/eqP ur /IHs us].
rewrite gal_id -horner_map /= ur map_poly_id //.
move=> a /(nthP 0)[i i_lt <-]; rewrite us ?gal_id //.
exact/polyOverP/Fadjoin_polyOver.
Qed.

Lemma quintic_minPoly_root x :
  x \in quintic_root_seq ->
  minPoly 1%VS x %= map_poly (@ratr L) p.
Proof.
move=> xroot.
have px0 : root (map_poly (@ratr L) p) x.
  by rewrite (eqp_root quintic_ratr_factorization) root_prod_XsubC.
have : minPoly 1 x %| map_poly (@ratr L) p.
  rewrite minPoly_dvdp //.
  apply/polyOver1P; exists p; apply: eq_map_poly.
  by move=> q; rewrite in_algE alg_num_field.
have : size (minPoly 1 x) != 1%N by rewrite size_minPoly.
have /polyOver1P[q ->] := minPolyOver 1 x.
have /eq_map_poly -> : in_alg L =1 (@ratr L).
  by move=> r; rewrite in_algE alg_num_field.
rewrite -(@char0_ratrE L charL) /eqp.
rewrite 2!(dvdp_map (char0_ratr charL)).
by rewrite -/(_ %= _) size_map_poly; apply: p_irr.
Qed.

Lemma quintic_root_characterization :
  root (map_poly (@ratr L) p) =i quintic_root_seq.
Proof.
move=> x.
exact: eq_trans (eqp_root quintic_ratr_factorization x)
  (root_prod_XsubC quintic_root_seq x).
Qed.

Definition quintic_galois_image : {group S5} :=
  quintic_gal_perm @* 'Gal({:L} / 1%AS).

Lemma quintic_galois_image_transitive :
  [transitive quintic_galois_image, on [set: 'I_5] | 'P].
Proof.
rewrite /atrans; apply/imsetP; exists ord0; first by rewrite inE.
apply/setP=> j; rewrite inE.
apply/idP/idP; last by [].
move=> _; apply/orbitP.
have root_mem i : tnth quintic_root_tuple i \in quintic_root_seq.
  by rewrite tnth_quintic_root_tuple mem_nth ?size_quintic_root_seq ?ltn_ord.
have mroot :
    root (minPoly 1%VS (tnth quintic_root_tuple ord0))
      (tnth quintic_root_tuple j).
  have hroot :
      root (minPoly 1%VS (tnth quintic_root_tuple ord0))
          (tnth quintic_root_tuple j) =
        (tnth quintic_root_tuple j \in quintic_root_seq) :=
    eq_trans
      (eqp_root (quintic_minPoly_root (root_mem ord0))
        (tnth quintic_root_tuple j))
      (quintic_root_characterization (tnth quintic_root_tuple j)).
  by move: (root_mem j); rewrite -hroot.
have [u gu hu] := normalField_root_minPoly (sub1v fullv)
  (normal_numfield p) (memvf (tnth quintic_root_tuple ord0)) mroot.
exists (quintic_gal_perm u).
  apply/morphimP; by exists u.
apply: quintic_root_tuple_injective.
by rewrite quintic_gal_permP hu.
Qed.

Lemma quintic_galois_image_solvableE :
  solvable quintic_galois_image =
    solvable 'Gal({:L} / 1%AS).
Proof.
exact: injm_sol injm_quintic_gal_perm (subxx _).
Qed.

End IrreducibleQuintic.

End PolynomialFormulasQuinticGaloisAction.
