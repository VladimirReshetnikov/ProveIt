From mathcomp Require Import all_ssreflect all_fingroup all_solvable.
From PolynomialFormulas Require Import QuinticF20Data.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The group-theoretic classification behind the Frobenius--Dummit
    quintic criterion.  A transitive solvable subgroup of [S_5] has a
    nontrivial elementary-abelian normal subgroup.  Prime degree forces that
    subgroup to be transitive, hence to be a Sylow 5-subgroup; normality then
    puts the whole group in its normalizer. *)
Module PolynomialFormulasQuinticSolvableCriterion.

Import PolynomialFormulasQuinticF20Data.

Local Open Scope group_scope.
Local Open Scope action_scope.

Definition quintic_block_action : {action S5 &-> {set 'I_5}} :=
  (('P^*) : {action S5 &-> {set 'I_5}}).

Lemma invariant_partition_uniform (G : {group S5})
    (Q : {set {set 'I_5}}) :
  [transitive G, on [set: 'I_5] | 'P] ->
  partition Q [set: 'I_5] ->
  [acts G, on Q | quintic_block_action] ->
  {in Q &, forall A B : {set 'I_5}, #|A| = #|B|}.
Proof.
move=> trG partQ actQ A B QA QB.
have tiQ := partition_trivIset partQ.
have nzA := partition_neq0 partQ QA.
have nzB := partition_neq0 partQ QB.
case/set0Pn: nzA => x Ax.
case/set0Pn: nzB => y By.
have Sx : x \in [set: 'I_5] by rewrite inE.
have Sy : y \in [set: 'I_5] by rewrite inE.
have [g Gg hxy] := atransP2 trG Sx Sy.
have actAQ : quintic_block_action A g \in Q by rewrite (actsP actQ).
have yact : y \in quintic_block_action A g.
  by apply/imsetP; exists x.
have eqAB : quintic_block_action A g = B.
  by rewrite -(def_pblock tiQ actAQ yact) -(def_pblock tiQ QB By).
  by rewrite -(card_setact 'P A g) eqAB.
Qed.

Lemma transitive_S5_primitive (G : {group S5}) :
  [transitive G, on [set: 'I_5] | 'P] ->
  [primitive G, on [set: 'I_5] | 'P].
Proof.
move=> trG.
rewrite /primitive trG /=.
apply/negP=> /existsP[Q /and3P[partQ actQ ntQ]].
move/andP: ntQ=> [cardQ_gt1 cardQ_lt5].
rewrite cardsT card_ord in cardQ_lt5.
have Qnz : Q != set0.
  apply/eqP=> Q0.
  by move: cardQ_gt1; rewrite Q0 cards0.
case/set0Pn: Qnz=> A QA.
have uniQ := invariant_partition_uniform trG partQ actQ.
have card_partition5 : 5 = (#|Q| * #|A|)%N.
  have hcard : #|[set: 'I_5]| = (#|Q| * #|A|)%N.
    apply: card_uniform_partition partQ=> B QB.
    exact: uniQ B A QB QA.
  by move: hcard; rewrite cardsT card_ord.
have cardQ_dvd5 : #|Q| %| 5.
  apply/dvdnP; exists #|A|.
  by rewrite mulnC.
have cardQ_ne1 : #|Q| != 1%N.
  apply/eqP=> cardQ1.
  by move: cardQ_gt1; rewrite cardQ1 ltnn.
have cardQ_eq5 : #|Q| = 5%N.
  exact: (elimT (prime_nt_dvdP (isT : prime 5) cardQ_ne1) cardQ_dvd5).
by move: cardQ_lt5; rewrite cardQ_eq5 ltnn.
Qed.

Lemma transitive_S5_nontrivial (G : {group S5}) :
  [transitive G, on [set: 'I_5] | 'P] -> G :!=: 1.
Proof.
move=> trG; apply/eqP=> G1.
have d5G : 5 %| #|G|.
  by move: (atrans_dvd trG); rewrite cardsT card_ord.
by move: d5G; rewrite G1 cards1.
Qed.

Lemma perm_S5_astab_setT_sub1 :
  'C([set: 'I_5] | 'P) \subset [1 S5].
Proof.
apply/subsetP=> s cs; rewrite inE; apply/eqP/permP=> i; rewrite perm1.
apply: (@astab_act S5 [set: S5]%G 'I_5 'P [set: 'I_5] s i cs).
by rewrite inE.
Qed.

Lemma natural_S5_action_kernel_trivial (G : {group S5}) :
  'C_G([set: 'I_5] | 'P) \subset [1 S5].
Proof.
exact: subset_trans (subsetIr _ _) perm_S5_astab_setT_sub1.
Qed.

Lemma solvable_conjugate (G : {group S5}) x :
  solvable G -> solvable (G :^ x).
Proof.
move/derivedP=> [n derGn].
apply/derivedP; exists n.
by rewrite derJ derGn conjs1g.
Qed.

Lemma solvable_transitive_normal_sylow5 (G : {group S5}) :
  solvable G ->
  [transitive G, on [set: 'I_5] | 'P] ->
  exists H : {group S5},
    5.-Sylow([set: S5]) H /\ H <| G.
Proof.
move=> solG trG.
have ntG := transitive_S5_nontrivial trG.
have primG := transitive_S5_primitive trG.
case: (solvable_norm_abelem solG (normal_refl G) ntG) =>
  H [sHG nHG ntH abH].
have trH : [transitive H, on [set: 'I_5] | 'P].
  case: (prim_trans_norm primG nHG)=> [sHker | trH]; last exact: trH.
  have sH1 := subset_trans sHker (natural_S5_action_kernel_trivial G).
  have H1 : H :==: 1 by rewrite eqEsubset sH1 sub1G.
  by move: ntH; rewrite H1.
have d5H : 5 %| #|H|.
  by move: (atrans_dvd trH); rewrite cardsT card_ord.
case/is_abelemP: abH=> q qprime /abelem_pgroup qH.
have q5 : 5 = q.
  apply/eqP.
  exact: (pgroupP qH 5 (isT : prime 5) d5H).
have pH : 5.-group H.
  apply/pgroupP=> r rprime rdH.
  have rq := pgroupP qH r rprime rdH.
  by move: rq; rewrite -q5.
have [P sylP sHP] :=
  @Sylow_superset 5 S5 [set: S5] H (subsetT H) pH.
have [x _ hPx] := Sylow_trans standard_C5_sylow sylP.
have cardP : #|P| = 5%N.
  by rewrite hPx cardJg card_standard_C5.
have cardH_le5 : #|H| <= 5.
  have hle := dvdn_leq (cardG_gt0 P) (cardSg sHP).
  by move: hle; rewrite cardP.
have cardH_ge5 : 5 <= #|H| :=
  dvdn_leq (cardG_gt0 H) d5H.
have cardH : #|H| = 5%N.
  by apply/eqP; rewrite eqn_leq cardH_le5 cardH_ge5.
have HP : H = P.
  apply: val_inj; apply/eqP.
  by rewrite eqEcard sHP cardH cardP.
exists H; split=> //.
by rewrite HP.
Qed.

Definition contained_in_conjugate_F20b (G : {group S5}) : bool :=
  [exists x : S5, G \subset (standard_F20 :^ x)].

Theorem solvable_transitive_S5_criterion (G : {group S5}) :
  [transitive G, on [set: 'I_5] | 'P] ->
  solvable G = contained_in_conjugate_F20b G.
Proof.
move=> trG; apply/idP/idP.
- move=> solG; apply/existsP.
  have [H [sylH nHG]] := solvable_transitive_normal_sylow5 solG trG.
  have [x _ hHx] := Sylow_trans standard_C5_sylow sylH.
  exists x.
  move: (normal_norm nHG).
  by rewrite hHx normJ /standard_F20.
- move/existsP=> [x subG].
  have solFx : solvable (standard_F20 :^ x) :=
    @solvable_conjugate standard_F20 x standard_F20_solvable.
  exact: solvableS subG solFx.
Qed.

Corollary solvable_transitive_S5_iff (G : {group S5}) :
  [transitive G, on [set: 'I_5] | 'P] ->
  (solvable G <->
    exists x : S5, G \subset (standard_F20 :^ x)).
Proof.
move=> trG; split.
- move=> solG.
  have h : contained_in_conjugate_F20b G.
    by move: solG; rewrite solvable_transitive_S5_criterion.
  exact: (elimT existsP h).
- move=> [x subG].
  have h : contained_in_conjugate_F20b G.
    apply/existsP; exists x.
    exact: subG.
  by move: h; rewrite -solvable_transitive_S5_criterion.
Qed.

End PolynomialFormulasQuinticSolvableCriterion.
