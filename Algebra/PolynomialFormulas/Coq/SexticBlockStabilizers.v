From mathcomp Require Import all_ssreflect all_fingroup all_solvable.
From PolynomialFormulas Require Import SexticSparseResolvents
  SexticResolventSymmetry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasSexticBlockStabilizers.

Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticResolventSymmetry.

Local Open Scope group_scope.
Local Open Scope action_scope.

Lemma val_subtype_setT (T : finType) (S : {set T}) :
  val @: [set: {x | x \in S}] = S.
Proof.
apply/setP=> x; apply/imsetP/idP=> [[u _ ->]|Sx].
  exact: valP.
by exists (Sub x Sx); rewrite // inE.
Qed.

Lemma card_subtype_set (T : finType) (S : {set T}) :
  #|[set: {x | x \in S}]| = #|S|.
Proof.
rewrite cardsT card_sig -(@cardsE T (mem S)).
by apply: eq_card=> x; rewrite inE.
Qed.

Lemma card_subtype_fin (T : finType) (S : {set T}) :
  #|{: {x | x \in S}}| = #|S|.
Proof.
rewrite card_sig -(@cardsE T (mem S)).
by apply: eq_card=> x; rewrite inE.
Qed.

Section SolvableActionStep.

Variables (aT : finGroupType) (rT : finType).
Variable to : {action aT &-> rT}.
Variables (H : {group aT}) (S : {set rT}).
Hypothesis hHS : H \subset 'N(S | to).

Let sto := @subaction aT [set: aT]%G rT (fun x => x \in S)
  {x | x \in S} to.
Let hHdom : H \subset subact_dom (fun x => x \in S) to.
Proof.
rewrite /subact_dom.
have -> : [set x | x \in S] = S by apply/setP=> x; rewrite inE.
exact hHS.
Qed.
Let rsto := sto \ hHdom.
Let f := actperm rsto.

Lemma restricted_subaction_kernel :
  'ker f = H :&: 'C(S | to).
Proof.
rewrite /f ker_actperm /rsto astab_ract /sto astab_subact.
rewrite val_subtype_setT setIA.
by rewrite (setIidPl hHdom).
Qed.

Lemma solvable_invariant_subset
    (solFix : solvable (H :&: 'C(S | to)))
    (solPerm : solvable 'Sym_({x | x \in S})) :
  solvable H.
Proof.
rewrite (series_sol (ker_normal f)).
apply/andP; split.
  apply: solvableS solFix.
  apply/subsetP=> x.
  change (x \in 'ker f -> x \in H :&: 'C(S | to)).
  by rewrite restricted_subaction_kernel.
have isoQ : (H / 'ker f) \isog (f @* H) := first_isog f.
rewrite (isog_sol isoQ).
exact: solvableS (subsetT (f @* H)) solPerm.
Qed.

End SolvableActionStep.

Lemma solvable_Sym_card_le3 (T : finType) :
  #|T| <= 3 -> solvable 'Sym_T.
Proof.
move=> leT3.
rewrite (series_sol (Alt_normal T)).
apply/andP; split.
- apply: abelian_sol; apply: cyclic_abelian; apply: cyclic_small.
  case: (leqP #|T| 2) => [leT2|lt2T].
    have hAS : #|'Alt_T| <= #|'Sym_T| :=
      subset_leq_card (Alt_subset T).
    apply: leq_trans hAS _.
    rewrite card_Sym.
    by case: #|T| leT2 => [|[|[|n]]].
  have T3 : #|T| = 3 by apply/eqP; rewrite eqn_leq leT3 lt2T.
  have alt3 : #|'Alt_T| = 3.
    by apply: double_inj; rewrite -mul2n card_Alt ?T3.
  by rewrite alt3.
- have isoQ : ('Sym_T / 'Alt_T) \isog (@odd_perm T @* 'Sym_T).
    exact: first_isog.
  rewrite (isog_sol isoQ).
  have solBool : solvable [set: bool]%G.
    apply: abelian_sol; apply: cyclic_abelian; apply: cyclic_small.
    by rewrite cardsT card_bool.
  exact: solvableS (subsetT (@odd_perm T @* 'Sym_T)) solBool.
Qed.

Definition S6 := {perm 'I_6}.
Definition block_action : {action S6 &-> {set 'I_6}} :=
  (('P^*) : {action S6 &-> {set 'I_6}}).
Definition ord6 (n : nat) : 'I_6 := inord n.

Definition o0 : 'I_6 := @Ordinal 6 0 isT.
Definition o1 : 'I_6 := @Ordinal 6 1 isT.
Definition o2 : 'I_6 := @Ordinal 6 2 isT.
Definition o3 : 'I_6 := @Ordinal 6 3 isT.
Definition o4 : 'I_6 := @Ordinal 6 4 isT.
Definition o5 : 'I_6 := @Ordinal 6 5 isT.

Definition pair_b0 : {set 'I_6} := [set o0; o1].
Definition pair_b1 : {set 'I_6} := [set o2; o3].
Definition pair_b2 : {set 'I_6} := [set o4; o5].
Definition pair0_blocks : {set {set 'I_6}} :=
  [set pair_b0; pair_b1; pair_b2].

Definition triple_b0 : {set 'I_6} := [set o0; o1; o2].
Definition triple_b1 : {set 'I_6} := [set o3; o4; o5].
Definition triple0_blocks : {set {set 'I_6}} :=
  [set triple_b0; triple_b1].

Lemma pair_block_card_le3 (B : {x | x \in pair0_blocks}) :
  #|{: {x | x \in val B}}| <= 3.
Proof.
case: B => B hB /=.
rewrite /pair0_blocks !inE in hB.
move/orP: hB => [hB | /eqP->]; last
  by rewrite card_subtype_fin /pair_b2 cards2; case: (_ != _).
move/orP: hB => [/eqP-> | /eqP->];
  by rewrite card_subtype_fin /pair_b0 /pair_b1 cards2; case: (_ != _).
Qed.

Lemma triple_block_card_le3 (B : {x | x \in triple0_blocks}) :
  #|{: {x | x \in val B}}| <= 3.
Proof.
case: B => B hB /=.
rewrite /triple0_blocks !inE in hB.
move/orP: hB => [/eqP-> | /eqP->];
rewrite card_subtype_fin /triple_b0 /triple_b1 -setUA cardsU1 cards2;
  by case: (_ \notin _); case: (_ != _).
Qed.

Lemma pair_blocks_card_le3 : #|{: {x | x \in pair0_blocks}}| <= 3.
Proof.
rewrite card_subtype_fin /pair0_blocks -setUA cardsU1 cards2.
by case: (_ \notin _); case: (_ != _).
Qed.

Lemma triple_blocks_card_le3 : #|{: {x | x \in triple0_blocks}}| <= 3.
Proof.
rewrite card_subtype_fin /triple0_blocks cards2.
by case: (_ != _).
Qed.

Lemma partition_centralizer_normalizes_block
    (Q : {set {set 'I_6}}) (B : {set 'I_6}) :
  B \in Q -> 'C(Q | block_action) \subset 'N(B | 'P).
Proof.
move=> BQ; apply/subsetP=> s cQs.
rewrite -astab1_set.
apply/astabP=> X /set1P->.
exact: astab_act cQs BQ.
Qed.

Definition pair_k0 : {group S6} := 'C(pair0_blocks | block_action).
Definition pair_k1 : {group S6} := pair_k0 :&: 'C(pair_b0 | 'P).
Definition pair_k2 : {group S6} := pair_k1 :&: 'C(pair_b1 | 'P).
Definition pair_k3 : {group S6} := pair_k2 :&: 'C(pair_b2 | 'P).
Definition pair_g0 : {group S6} := 'N(pair0_blocks | block_action).

Definition triple_k0 : {group S6} := 'C(triple0_blocks | block_action).
Definition triple_k1 : {group S6} := triple_k0 :&: 'C(triple_b0 | 'P).
Definition triple_k2 : {group S6} := triple_k1 :&: 'C(triple_b1 | 'P).
Definition triple_g0 : {group S6} := 'N(triple0_blocks | block_action).

Lemma pair_b0_mem : pair_b0 \in pair0_blocks.
Proof. by rewrite /pair0_blocks !inE eqxx. Qed.
Lemma pair_b1_mem : pair_b1 \in pair0_blocks.
Proof. by rewrite /pair0_blocks !inE eqxx orbT. Qed.
Lemma pair_b2_mem : pair_b2 \in pair0_blocks.
Proof. by rewrite /pair0_blocks !inE eqxx orbT. Qed.
Lemma triple_b0_mem : triple_b0 \in triple0_blocks.
Proof. by rewrite /triple0_blocks !inE eqxx. Qed.
Lemma triple_b1_mem : triple_b1 \in triple0_blocks.
Proof. by rewrite /triple0_blocks !inE eqxx orbT. Qed.

Lemma pair_k0_norm_b0 : pair_k0 \subset 'N(pair_b0 | 'P).
Proof. exact: partition_centralizer_normalizes_block pair_b0_mem. Qed.
Lemma pair_k0_norm_b1 : pair_k0 \subset 'N(pair_b1 | 'P).
Proof. exact: partition_centralizer_normalizes_block pair_b1_mem. Qed.
Lemma pair_k0_norm_b2 : pair_k0 \subset 'N(pair_b2 | 'P).
Proof. exact: partition_centralizer_normalizes_block pair_b2_mem. Qed.
Lemma triple_k0_norm_b0 : triple_k0 \subset 'N(triple_b0 | 'P).
Proof. exact: partition_centralizer_normalizes_block triple_b0_mem. Qed.
Lemma triple_k0_norm_b1 : triple_k0 \subset 'N(triple_b1 | 'P).
Proof. exact: partition_centralizer_normalizes_block triple_b1_mem. Qed.

Lemma enum_ord6E : enum 'I_6 =
  [:: o0; o1; o2; o3; o4; o5].
Proof.
apply: (inj_map val_inj).
by rewrite val_enum_ord /o0 /o1 /o2 /o3 /o4 /o5.
Qed.

Lemma pair_blocks_cover :
  pair_b0 :|: pair_b1 :|: pair_b2 = [set: 'I_6].
Proof.
apply/setP=> i.
rewrite in_setT; apply/idP.
have mi : i \in enum 'I_6 by rewrite mem_enum.
rewrite enum_ord6E in mi.
move: mi; rewrite /pair_b0 /pair_b1 /pair_b2 !inE.
by rewrite !orbA.
Qed.

Lemma triple_blocks_cover :
  triple_b0 :|: triple_b1 = [set: 'I_6].
Proof.
apply/setP=> i.
rewrite in_setT; apply/idP.
have mi : i \in enum 'I_6 by rewrite mem_enum.
rewrite enum_ord6E in mi.
move: mi; rewrite /triple_b0 /triple_b1 !inE.
by rewrite !orbA.
Qed.

Lemma perm_astab_setT_sub1 : 'C([set: 'I_6] | 'P) \subset [1 S6].
Proof.
apply/subsetP=> s cs; rewrite inE; apply/eqP/permP=> i; rewrite perm1.
apply: (@astab_act S6 [set: S6]%G 'I_6 'P [set: 'I_6] s i cs).
by rewrite inE.
Qed.

Lemma pair_k3_sub1 : pair_k3 \subset [1 S6].
Proof.
apply: subset_trans perm_astab_setT_sub1.
apply/subsetP=> s hs.
case/setIP: hs=> hk2 cB2; case/setIP: hk2=> hk1 cB1.
case/setIP: hk1=> _ cB0.
rewrite -pair_blocks_cover.
apply/astabP=> i hi.
case/setUP: hi=> [hi01 | hi2]; last exact: astab_act cB2 hi2.
case/setUP: hi01=> [hi0 | hi1].
  exact: astab_act cB0 hi0.
exact: astab_act cB1 hi1.
Qed.

Lemma triple_k2_sub1 : triple_k2 \subset [1 S6].
Proof.
apply: subset_trans perm_astab_setT_sub1.
apply/subsetP=> s hs.
case/setIP: hs=> hk1 cB1; case/setIP: hk1=> _ cB0.
rewrite -triple_blocks_cover.
apply/astabP=> i hi.
case/setUP: hi=> [hi0 | hi1].
  exact: astab_act cB0 hi0.
exact: astab_act cB1 hi1.
Qed.

Lemma pair_k3_solvable : solvable pair_k3.
Proof. exact: solvableS pair_k3_sub1 (solvable1 S6). Qed.

Lemma triple_k2_solvable : solvable triple_k2.
Proof. exact: solvableS triple_k2_sub1 (solvable1 S6). Qed.

Lemma pair_b0_card_le3 : #|{: {x | x \in pair_b0}}| <= 3.
Proof. by rewrite card_subtype_fin /pair_b0 cards2; case: (_ != _). Qed.
Lemma pair_b1_card_le3 : #|{: {x | x \in pair_b1}}| <= 3.
Proof. by rewrite card_subtype_fin /pair_b1 cards2; case: (_ != _). Qed.
Lemma pair_b2_card_le3 : #|{: {x | x \in pair_b2}}| <= 3.
Proof. by rewrite card_subtype_fin /pair_b2 cards2; case: (_ != _). Qed.
Lemma triple_b0_card_le3 : #|{: {x | x \in triple_b0}}| <= 3.
Proof.
rewrite card_subtype_fin /triple_b0 -setUA cardsU1 cards2.
by case: (_ \notin _); case: (_ != _).
Qed.
Lemma triple_b1_card_le3 : #|{: {x | x \in triple_b1}}| <= 3.
Proof.
rewrite card_subtype_fin /triple_b1 -setUA cardsU1 cards2.
by case: (_ \notin _); case: (_ != _).
Qed.

Lemma pair_k2_solvable : solvable pair_k2.
Proof.
apply: (solvable_invariant_subset
  (to := 'P) (H := pair_k2) (S := pair_b2)).
- exact: subset_trans (subset_trans (subsetIl _ _) (subsetIl _ _))
    pair_k0_norm_b2.
- exact: pair_k3_solvable.
- apply: solvable_Sym_card_le3.
  exact: pair_b2_card_le3.
Qed.

Lemma pair_k1_solvable : solvable pair_k1.
Proof.
apply: (solvable_invariant_subset
  (to := 'P) (H := pair_k1) (S := pair_b1)).
- exact: subset_trans (subsetIl _ _) pair_k0_norm_b1.
- exact: pair_k2_solvable.
- apply: solvable_Sym_card_le3.
  exact: pair_b1_card_le3.
Qed.

Lemma pair_k0_solvable : solvable pair_k0.
Proof.
apply: (solvable_invariant_subset
  (to := 'P) (H := pair_k0) (S := pair_b0)).
- exact: pair_k0_norm_b0.
- exact: pair_k1_solvable.
- apply: solvable_Sym_card_le3.
  exact: pair_b0_card_le3.
Qed.

Lemma triple_k1_solvable : solvable triple_k1.
Proof.
apply: (solvable_invariant_subset
  (to := 'P) (H := triple_k1) (S := triple_b1)).
- exact: subset_trans (subsetIl _ _) triple_k0_norm_b1.
- exact: triple_k2_solvable.
- apply: solvable_Sym_card_le3.
  exact: triple_b1_card_le3.
Qed.

Lemma triple_k0_solvable : solvable triple_k0.
Proof.
apply: (solvable_invariant_subset
  (to := 'P) (H := triple_k0) (S := triple_b0)).
- exact: triple_k0_norm_b0.
- exact: triple_k1_solvable.
- apply: solvable_Sym_card_le3.
  exact: triple_b0_card_le3.
Qed.

Lemma pair_g0_solvable : solvable pair_g0.
Proof.
apply: (solvable_invariant_subset
  (to := block_action) (H := pair_g0) (S := pair0_blocks)).
- by rewrite /pair_g0.
- exact: solvableS (subsetIr _ _) pair_k0_solvable.
- apply: solvable_Sym_card_le3.
  exact: pair_blocks_card_le3.
Qed.

Lemma triple_g0_solvable : solvable triple_g0.
Proof.
apply: (solvable_invariant_subset
  (to := block_action) (H := triple_g0) (S := triple0_blocks)).
- by rewrite /triple_g0.
- exact: solvableS (subsetIr _ _) triple_k0_solvable.
- apply: solvable_Sym_card_le3.
  exact: triple_blocks_card_le3.
Qed.

Definition pair_table_block (p : pair_partition) (b : 'I_3) :
    {set 'I_6} :=
  pair_member p b @: [set: 'I_2].

Definition pair_table_blocks (p : pair_partition) : {set {set 'I_6}} :=
  pair_table_block p @: [set: 'I_3].

Definition triple_table_block (p : triple_partition) (b : 'I_2) :
    {set 'I_6} :=
  triple_member p b @: [set: 'I_3].

Definition triple_table_blocks (p : triple_partition) : {set {set 'I_6}} :=
  triple_table_block p @: [set: 'I_2].

Definition pair_flat (p : pair_partition) : seq 'I_6 :=
  [seq inord n | n <- flatten (pair_member_blocks p)].

Definition pair_conj_fun (p : pair_partition) (i : 'I_6) : 'I_6 :=
  nth ord0 (pair_flat p) i.

Definition triple_flat (p : triple_partition) : seq 'I_6 :=
  [seq inord n | n <- flatten (triple_member_blocks p)].

Definition triple_conj_fun (p : triple_partition) (i : 'I_6) : 'I_6 :=
  nth ord0 (triple_flat p) i.

Lemma pair_blocks_table_size :
  all (fun bs => size (flatten bs) == 6) pair_blocks_table.
Proof. vm_compute; reflexivity. Qed.

Lemma pair_blocks_table_uniq :
  all (fun bs => uniq (flatten bs)) pair_blocks_table.
Proof. vm_compute; reflexivity. Qed.

Lemma pair_blocks_table_bound :
  all (fun bs => all (ltn^~ 6) (flatten bs)) pair_blocks_table.
Proof. vm_compute; reflexivity. Qed.

Lemma triple_blocks_table_size :
  all (fun bs => size (flatten bs) == 6) triple_blocks_table.
Proof. vm_compute; reflexivity. Qed.

Lemma triple_blocks_table_uniq :
  all (fun bs => uniq (flatten bs)) triple_blocks_table.
Proof. vm_compute; reflexivity. Qed.

Lemma triple_blocks_table_bound :
  all (fun bs => all (ltn^~ 6) (flatten bs)) triple_blocks_table.
Proof. vm_compute; reflexivity. Qed.

Lemma pair_flat_size p : size (pair_flat p) = 6.
Proof.
rewrite /pair_flat size_map.
rewrite pair_member_blocks_correct.
have hp : p < size pair_blocks_table by rewrite /pair_blocks_table.
have hm := mem_nth [::] hp.
have /eqP hsize := allP pair_blocks_table_size _ hm.
exact hsize.
Qed.

Lemma pair_flat_uniq p : uniq (pair_flat p).
Proof.
rewrite /pair_flat.
rewrite pair_member_blocks_correct.
have hp : p < size pair_blocks_table by rewrite /pair_blocks_table.
have hm := mem_nth [::] hp.
have uxs := allP pair_blocks_table_uniq _ hm.
have bxs := allP pair_blocks_table_bound _ hm.
have hinj : {in flatten (nth [::] pair_blocks_table p) &,
    injective (@inord 5)}.
  move=> x y hx hy hxy.
  have ltx := allP bxs x hx; have lty := allP bxs y hy.
  have hv : val (@inord 5 x) = val (@inord 5 y) := congr1 val hxy.
  have kx : val (@inord 5 x) = x := inordK ltx.
  have ky : val (@inord 5 y) = y := inordK lty.
  by rewrite kx ky in hv.
by rewrite (map_inj_in_uniq hinj) uxs.
Qed.

Lemma triple_flat_size p : size (triple_flat p) = 6.
Proof.
rewrite /triple_flat size_map.
rewrite triple_member_blocks_correct.
have hp : p < size triple_blocks_table by rewrite /triple_blocks_table.
have hm := mem_nth [::] hp.
have /eqP hsize := allP triple_blocks_table_size _ hm.
exact hsize.
Qed.

Lemma triple_flat_uniq p : uniq (triple_flat p).
Proof.
rewrite /triple_flat.
rewrite triple_member_blocks_correct.
have hp : p < size triple_blocks_table by rewrite /triple_blocks_table.
have hm := mem_nth [::] hp.
have uxs := allP triple_blocks_table_uniq _ hm.
have bxs := allP triple_blocks_table_bound _ hm.
have hinj : {in flatten (nth [::] triple_blocks_table p) &,
    injective (@inord 5)}.
  move=> x y hx hy hxy.
  have ltx := allP bxs x hx; have lty := allP bxs y hy.
  have hv : val (@inord 5 x) = val (@inord 5 y) := congr1 val hxy.
  have kx : val (@inord 5 x) = x := inordK ltx.
  have ky : val (@inord 5 y) = y := inordK lty.
  by rewrite kx ky in hv.
by rewrite (map_inj_in_uniq hinj) uxs.
Qed.

Lemma pair_conj_fun_injective p : injective (pair_conj_fun p).
Proof.
move=> i j hij; apply: val_inj.
apply/eqP.
have hi : i < size (pair_flat p) by rewrite pair_flat_size.
have hj : j < size (pair_flat p) by rewrite pair_flat_size.
rewrite -(nth_uniq ord0 hi hj (pair_flat_uniq p)).
apply/eqP; exact hij.
Qed.

Lemma triple_conj_fun_injective p : injective (triple_conj_fun p).
Proof.
move=> i j hij; apply: val_inj.
apply/eqP.
have hi : i < size (triple_flat p) by rewrite triple_flat_size.
have hj : j < size (triple_flat p) by rewrite triple_flat_size.
rewrite -(nth_uniq ord0 hi hj (triple_flat_uniq p)).
apply/eqP; exact hij.
Qed.

Definition pair_conj (p : pair_partition) : S6 :=
  @perm 'I_6 (pair_conj_fun p) (@pair_conj_fun_injective p).

Definition triple_conj (p : triple_partition) : S6 :=
  @perm 'I_6 (triple_conj_fun p) (@triple_conj_fun_injective p).

Lemma pair_flat_nth p (b : 'I_3) (s : 'I_2) :
  nth ord0 (pair_flat p) (2 * b + s) = pair_member p b s.
Proof.
rewrite /pair_flat /pair_member_blocks
  PolynomialFormulasSexticResolventSymmetry.enum_ord2E
  PolynomialFormulasSexticResolventSymmetry.enum_ord3E /=.
case: (unliftP ord0 b)=> [b1 ->|->].
  case: (unliftP ord0 b1)=> [b2 ->|->].
    rewrite (ord1 b2); case: (unliftP ord0 s)=> [s1 ->|->].
      by rewrite (ord1 s1) /= inord_val.
    by rewrite /= inord_val.
  case: (unliftP ord0 s)=> [s1 ->|->].
    by rewrite (ord1 s1) /= inord_val.
  by rewrite /= inord_val.
case: (unliftP ord0 s)=> [s1 ->|->].
  by rewrite (ord1 s1) /= inord_val.
by rewrite /= inord_val.
Qed.

Lemma pair_index_bound (b : 'I_3) (s : 'I_2) : 2 * b + s < 6.
Proof.
case: (unliftP ord0 b)=> [b1 ->|->].
  case: (unliftP ord0 b1)=> [b2 ->|->].
    rewrite (ord1 b2); case: (unliftP ord0 s)=> [s1 ->|->].
      by rewrite (ord1 s1).
    by [].
  case: (unliftP ord0 s)=> [s1 ->|->].
    by rewrite (ord1 s1).
  by [].
case: (unliftP ord0 s)=> [s1 ->|->].
  by rewrite (ord1 s1).
by [].
Qed.

Definition pair_position (b : 'I_3) (s : 'I_2) : 'I_6 :=
  @Ordinal 6 (2 * b + s) (pair_index_bound b s).

Lemma pair_conj_position p b s :
  pair_conj p (pair_position b s) = pair_member p b s.
Proof.
rewrite /pair_conj permE /pair_conj_fun /pair_position /=.
exact: pair_flat_nth.
Qed.

Lemma triple_flat_nth p (b : 'I_2) (s : 'I_3) :
  nth ord0 (triple_flat p) (3 * b + s) = triple_member p b s.
Proof.
rewrite /triple_flat /triple_member_blocks
  PolynomialFormulasSexticResolventSymmetry.enum_ord2E
  PolynomialFormulasSexticResolventSymmetry.enum_ord3E /=.
case: (unliftP ord0 b)=> [b1 ->|->].
  rewrite (ord1 b1); case: (unliftP ord0 s)=> [s1 ->|->].
    case: (unliftP ord0 s1)=> [s2 ->|->].
      by rewrite (ord1 s2) /= inord_val.
    by rewrite /= inord_val.
  by rewrite /= inord_val.
case: (unliftP ord0 s)=> [s1 ->|->].
  case: (unliftP ord0 s1)=> [s2 ->|->].
    by rewrite (ord1 s2) /= inord_val.
  by rewrite /= inord_val.
by rewrite /= inord_val.
Qed.

Lemma triple_index_bound (b : 'I_2) (s : 'I_3) : 3 * b + s < 6.
Proof.
case: (unliftP ord0 b)=> [b1 ->|->].
  rewrite (ord1 b1); case: (unliftP ord0 s)=> [s1 ->|->].
    case: (unliftP ord0 s1)=> [s2 ->|->].
      by rewrite (ord1 s2).
    by [].
  by [].
case: (unliftP ord0 s)=> [s1 ->|->].
  case: (unliftP ord0 s1)=> [s2 ->|->].
    by rewrite (ord1 s2).
  by [].
by [].
Qed.

Definition triple_position (b : 'I_2) (s : 'I_3) : 'I_6 :=
  @Ordinal 6 (3 * b + s) (triple_index_bound b s).

Lemma triple_conj_position p b s :
  triple_conj p (triple_position b s) = triple_member p b s.
Proof.
rewrite /triple_conj permE /triple_conj_fun /triple_position /=.
exact: triple_flat_nth.
Qed.

Definition pair_position_block (b : 'I_3) : {set 'I_6} :=
  pair_position b @: [set: 'I_2].

Definition pair_position_blocks : {set {set 'I_6}} :=
  pair_position_block @: [set: 'I_3].

Definition triple_position_block (b : 'I_2) : {set 'I_6} :=
  triple_position b @: [set: 'I_3].

Definition triple_position_blocks : {set {set 'I_6}} :=
  triple_position_block @: [set: 'I_2].

Definition i3_0 : 'I_3 := @Ordinal 3 0 isT.
Definition i3_1 : 'I_3 := @Ordinal 3 1 isT.
Definition i3_2 : 'I_3 := @Ordinal 3 2 isT.
Definition i2_0 : 'I_2 := @Ordinal 2 0 isT.
Definition i2_1 : 'I_2 := @Ordinal 2 1 isT.

Lemma imset_ord2 (T : finType) (f : 'I_2 -> T) :
  f @: [set: 'I_2] = [set f i2_0; f i2_1].
Proof.
apply/setP=> x; apply/imsetP/idP.
- move=> [s _ ->].
  case: (unliftP ord0 s)=> [s1 ->|->].
    rewrite (ord1 s1).
    have -> : lift ord0 ord0 = i2_1 by apply: val_inj.
    by rewrite !inE eqxx orbT.
  have -> : ord0 = i2_0 by apply: val_inj.
  by rewrite !inE eqxx.
- rewrite !inE; case/orP=> /eqP->.
    by exists i2_0; rewrite ?inE.
  by exists i2_1; rewrite ?inE.
Qed.

Lemma imset_ord3 (T : finType) (f : 'I_3 -> T) :
  f @: [set: 'I_3] = [set f i3_0; f i3_1; f i3_2].
Proof.
apply/setP=> x; apply/imsetP/idP.
- move=> [s _ ->].
  case: (unliftP ord0 s)=> [s1 ->|->].
    case: (unliftP ord0 s1)=> [s2 ->|->].
      rewrite (ord1 s2).
      have -> : lift ord0 (lift ord0 ord0) = i3_2 by apply: val_inj.
      by rewrite !inE eqxx orbT.
    have -> : lift ord0 ord0 = i3_1 by apply: val_inj.
    by rewrite !inE eqxx orbT.
  have -> : ord0 = i3_0 by apply: val_inj.
  by rewrite !inE eqxx.
- rewrite !inE; case/orP=> [h | /eqP->].
    case/orP: h=> /eqP->.
      by exists i3_0; rewrite ?inE.
    by exists i3_1; rewrite ?inE.
  by exists i3_2; rewrite ?inE.
Qed.

Lemma pair_position_block0 : pair_position_block i3_0 = pair_b0.
Proof.
rewrite /pair_position_block imset_ord2 /pair_b0.
have -> : pair_position i3_0 i2_0 = o0 by apply: val_inj.
have -> : pair_position i3_0 i2_1 = o1 by apply: val_inj.
reflexivity.
Qed.

Lemma pair_position_block1 : pair_position_block i3_1 = pair_b1.
Proof.
rewrite /pair_position_block imset_ord2 /pair_b1.
have -> : pair_position i3_1 i2_0 = o2 by apply: val_inj.
have -> : pair_position i3_1 i2_1 = o3 by apply: val_inj.
reflexivity.
Qed.

Lemma pair_position_block2 : pair_position_block i3_2 = pair_b2.
Proof.
rewrite /pair_position_block imset_ord2 /pair_b2.
have -> : pair_position i3_2 i2_0 = o4 by apply: val_inj.
have -> : pair_position i3_2 i2_1 = o5 by apply: val_inj.
reflexivity.
Qed.

Lemma triple_position_block0 : triple_position_block i2_0 = triple_b0.
Proof.
rewrite /triple_position_block imset_ord3 /triple_b0.
have -> : triple_position i2_0 i3_0 = o0 by apply: val_inj.
have -> : triple_position i2_0 i3_1 = o1 by apply: val_inj.
have -> : triple_position i2_0 i3_2 = o2 by apply: val_inj.
reflexivity.
Qed.

Lemma triple_position_block1 : triple_position_block i2_1 = triple_b1.
Proof.
rewrite /triple_position_block imset_ord3 /triple_b1.
have -> : triple_position i2_1 i3_0 = o3 by apply: val_inj.
have -> : triple_position i2_1 i3_1 = o4 by apply: val_inj.
have -> : triple_position i2_1 i3_2 = o5 by apply: val_inj.
reflexivity.
Qed.

Lemma pair_position_blocksE : pair_position_blocks = pair0_blocks.
Proof.
rewrite /pair_position_blocks imset_ord3 pair_position_block0
  pair_position_block1 pair_position_block2.
reflexivity.
Qed.

Lemma triple_position_blocksE : triple_position_blocks = triple0_blocks.
Proof.
rewrite /triple_position_blocks imset_ord2 triple_position_block0
  triple_position_block1.
reflexivity.
Qed.

Lemma pair_conj_block p b :
  block_action (pair_position_block b) (pair_conj p) = pair_table_block p b.
Proof.
change ([set pair_conj p x | x in pair_position_block b] =
  pair_table_block p b).
rewrite /pair_position_block /pair_table_block.
apply/setP=> x; apply/imsetP/imsetP.
- move=> [y /imsetP[s _ ->] ->].
  by exists s; rewrite ?inE // pair_conj_position.
- move=> [s _ ->].
  exists (pair_position b s); last by rewrite pair_conj_position.
  by apply/imsetP; exists s; rewrite ?inE.
Qed.

Lemma triple_conj_block p b :
  block_action (triple_position_block b) (triple_conj p) =
    triple_table_block p b.
Proof.
change ([set triple_conj p x | x in triple_position_block b] =
  triple_table_block p b).
rewrite /triple_position_block /triple_table_block.
apply/setP=> x; apply/imsetP/imsetP.
- move=> [y /imsetP[s _ ->] ->].
  by exists s; rewrite ?inE // triple_conj_position.
- move=> [s _ ->].
  exists (triple_position b s); last by rewrite triple_conj_position.
  by apply/imsetP; exists s; rewrite ?inE.
Qed.

Lemma pair_conj_blocks p :
  (block_action^*) pair0_blocks (pair_conj p) = pair_table_blocks p.
Proof.
rewrite -pair_position_blocksE.
change ([set block_action C (pair_conj p) |
    C in pair_position_blocks] = pair_table_blocks p).
rewrite /pair_position_blocks /pair_table_blocks.
apply/setP=> B; apply/imsetP/imsetP.
- move=> [C /imsetP[b _ ->] ->].
  by exists b; rewrite ?inE // pair_conj_block.
- move=> [b _ ->].
  exists (pair_position_block b); last by rewrite pair_conj_block.
  by apply/imsetP; exists b; rewrite ?inE.
Qed.

Lemma triple_conj_blocks p :
  (block_action^*) triple0_blocks (triple_conj p) = triple_table_blocks p.
Proof.
rewrite -triple_position_blocksE.
change ([set block_action C (triple_conj p) |
    C in triple_position_blocks] = triple_table_blocks p).
rewrite /triple_position_blocks /triple_table_blocks.
apply/setP=> B; apply/imsetP/imsetP.
- move=> [C /imsetP[b _ ->] ->].
  by exists b; rewrite ?inE // triple_conj_block.
- move=> [b _ ->].
  exists (triple_position_block b); last by rewrite triple_conj_block.
  by apply/imsetP; exists b; rewrite ?inE.
Qed.

Section StabilizerConjugacy.

Variables (aT : finGroupType) (rT : finType).
Variable to : {action aT &-> rT}.

Lemma astabs_setact_conj (S : {set rT}) (a : aT) :
  'N(((to^*) : {action aT &-> {set rT}}) S a | to) =
    'N(S | to) :^ a.
Proof.
rewrite -!astab1_set.
exact: astab1_act.
Qed.

End StabilizerConjugacy.

Definition pair_table_group (p : pair_partition) : {group S6} :=
  'N(pair_table_blocks p | block_action).

Definition triple_table_group (p : triple_partition) : {group S6} :=
  'N(triple_table_blocks p | block_action).

Lemma pair_table_group_conj p :
  pair_table_group p = pair_g0 :^ pair_conj p.
Proof.
rewrite /pair_table_group /pair_g0 -pair_conj_blocks.
apply: group_inj.
exact (@astabs_setact_conj S6 {set 'I_6}
  block_action pair0_blocks (pair_conj p)).
Qed.

Lemma triple_table_group_conj p :
  triple_table_group p = triple_g0 :^ triple_conj p.
Proof.
rewrite /triple_table_group /triple_g0 -triple_conj_blocks.
apply: group_inj.
exact (@astabs_setact_conj S6 {set 'I_6}
  block_action triple0_blocks (triple_conj p)).
Qed.

Lemma pair_table_group_solvable p : solvable (pair_table_group p).
Proof.
rewrite pair_table_group_conj.
rewrite -(isog_sol (@conj_isog S6 pair_g0 (pair_conj p))).
exact: pair_g0_solvable.
Qed.

Lemma triple_table_group_solvable p : solvable (triple_table_group p).
Proof.
rewrite triple_table_group_conj.
rewrite -(isog_sol (@conj_isog S6 triple_g0 (triple_conj p))).
exact: triple_g0_solvable.
Qed.

End PolynomialFormulasSexticBlockStabilizers.
