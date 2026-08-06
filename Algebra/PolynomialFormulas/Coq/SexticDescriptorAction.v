From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import SexticSparseResolvents
  SexticNewtonPowerSums SexticResolventSymmetry SexticSeparatingExistence
  SexticBlockStabilizers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

(** The finite pair and triple descriptor tables carry the natural action of
    [S_6].  This file extends the transposition-level symmetry lemmas used to
    prove coefficient invariance to arbitrary permutations.  The only finite
    search below is over the explicit tables (15 and 10 entries); its
    completeness and its agreement with the block stabilizers are closed
    Boolean certificates. *)
Module PolynomialFormulasSexticDescriptorAction.

Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticResolventSymmetry.
Import PolynomialFormulasSexticSeparatingExistence.
Import PolynomialFormulasSexticBlockStabilizers.

Definition permute_code (s : S6) (code : seq nat) : seq nat :=
  [seq val (s (inord n)) | n <- code].

Definition permute_codes (s : S6) (codes : seq (seq nat)) : seq (seq nat) :=
  [seq sort leq (permute_code s code) | code <- codes].

Definition pair_partition_actionb
    (s : S6) (p q : pair_partition) : bool :=
  perm_eq (permute_codes s (pair_member_blocks p))
    (pair_member_blocks q).

Definition triple_partition_actionb
    (s : S6) (p q : triple_partition) : bool :=
  perm_eq (permute_codes s (triple_member_blocks p))
    (triple_member_blocks q).

Definition pair_partition_action (s : S6) (p : pair_partition) :
    pair_partition :=
  odflt ord0 [pick q | pair_partition_actionb s p q].

Definition triple_partition_action (s : S6) (p : triple_partition) :
    triple_partition :=
  odflt ord0 [pick q | triple_partition_actionb s p q].

Lemma permute_codeM (s t : S6) code :
  permute_code (s * t)%g code = permute_code t (permute_code s code).
Proof.
rewrite /permute_code -map_comp.
apply: eq_map=> n.
by rewrite /= permM inord_val.
Qed.

Lemma permute_codesM (s t : S6) codes :
  permute_codes (s * t)%g codes =
    permute_codes t (permute_codes s codes).
Proof.
rewrite /permute_codes -map_comp.
apply: eq_map=> code.
apply/perm_sortP; first exact: leq_total.
- exact: leq_trans.
- exact: anti_leq.
rewrite permute_codeM.
rewrite /permute_code.
apply: perm_map.
rewrite perm_sym.
exact: permEl (perm_sort leq (permute_code s code)).
Qed.

Lemma permute_codes_perm (s : S6) codes1 codes2 :
  perm_eq codes1 codes2 ->
  perm_eq (permute_codes s codes1) (permute_codes s codes2).
Proof. exact: perm_map. Qed.

Lemma permute_code1 code :
  all (fun n => n < 6)%N code -> permute_code 1%g code = code.
Proof.
move=> hcode; rewrite /permute_code.
rewrite -[RHS]map_id.
apply/eq_in_map=> n hn.
rewrite perm1.
exact: inordK (allP hcode n hn).
Qed.

Lemma permute_codes1 codes :
  all code_wfb codes -> permute_codes 1%g codes = codes.
Proof.
elim: codes=> [|code codes ih] //= /andP[hcode hcodes].
rewrite ih // permute_code1.
- have /and3P[hsorted _ _] := hcode.
  by rewrite (sorted_sort leq_trans hsorted).
- by have /and3P[_ _] := hcode.
Qed.

Lemma permute_code_tperm_zero (j : 'I_6) code :
  all (fun n => n < 6)%N code ->
  permute_code (tperm ord0 j) code = map (swap_zero j) code.
Proof.
move=> hcode; rewrite /permute_code.
apply/eq_in_map=> n hn.
rewrite val_tperm_zero.
have hn6 : (n < 6)%N := allP hcode n hn.
have hinord : val (inord n : 'I_6) = n := inordK hn6.
by rewrite hinord.
Qed.

Lemma pair_permute_codes_tperm_zero j p :
  permute_codes (tperm ord0 j) (pair_member_blocks p) =
    pair_partition_codes j p.
Proof.
rewrite pair_partition_codesE /permute_codes.
rewrite -map_comp.
apply/eq_in_map=> code hcode.
congr (sort leq _).
apply: permute_code_tperm_zero.
have /and3P[_ _] := allP (pair_codes_wfb p) code hcode.
exact.
Qed.

Lemma triple_permute_codes_tperm_zero j p :
  permute_codes (tperm ord0 j) (triple_member_blocks p) =
    triple_partition_codes j p.
Proof.
rewrite triple_partition_codesE /permute_codes.
rewrite -map_comp.
apply/eq_in_map=> code hcode.
congr (sort leq _).
apply: permute_code_tperm_zero.
have /and3P[_ _] := allP (triple_codes_wfb p) code hcode.
exact.
Qed.

Definition pair_action_totalb (s : S6) : bool :=
  [forall p : pair_partition,
    [exists q : pair_partition, pair_partition_actionb s p q]].

Definition triple_action_totalb (s : S6) : bool :=
  [forall p : triple_partition,
    [exists q : triple_partition, triple_partition_actionb s p q]].

Definition pair_action_total_set : {set S6} :=
  [set s | pair_action_totalb s].

Definition triple_action_total_set : {set S6} :=
  [set s | triple_action_totalb s].

Lemma pair_action_total_group_set : group_set pair_action_total_set.
Proof.
apply/group_setP; split.
- rewrite inE /pair_action_totalb.
  apply/forallP=> p; apply/existsP; exists p.
  by rewrite /pair_partition_actionb permute_codes1 ?pair_codes_wfb.
- move=> s t; rewrite !inE /pair_action_totalb.
  move=> /forallP hs /forallP ht; apply/forallP=> p.
  move/existsP: (hs p)=> [q hsq].
  move/existsP: (ht q)=> [r htr].
  apply/existsP; exists r.
  rewrite /pair_partition_actionb permute_codesM.
  exact: perm_trans (permute_codes_perm t hsq) htr.
Qed.

Lemma triple_action_total_group_set : group_set triple_action_total_set.
Proof.
apply/group_setP; split.
- rewrite inE /triple_action_totalb.
  apply/forallP=> p; apply/existsP; exists p.
  by rewrite /triple_partition_actionb permute_codes1 ?triple_codes_wfb.
- move=> s t; rewrite !inE /triple_action_totalb.
  move=> /forallP hs /forallP ht; apply/forallP=> p.
  move/existsP: (hs p)=> [q hsq].
  move/existsP: (ht q)=> [r htr].
  apply/existsP; exists r.
  rewrite /triple_partition_actionb permute_codesM.
  exact: perm_trans (permute_codes_perm t hsq) htr.
Qed.

Canonical pair_action_total_group : {group S6} :=
  Group pair_action_total_group_set.

Canonical triple_action_total_group : {group S6} :=
  Group triple_action_total_group_set.

Lemma pair_action_total_tperm (j : 'I_6) :
  tperm ord0 j \in pair_action_total_group.
Proof.
rewrite inE /pair_action_totalb.
apply/forallP=> p; apply/existsP.
exists (pair_partition_map j p).
rewrite /pair_partition_actionb pair_permute_codes_tperm_zero.
rewrite -(pair_partition_codes_zero (pair_partition_map j p)).
exact: pair_partition_map_action.
Qed.

Lemma triple_action_total_tperm (j : 'I_6) :
  tperm ord0 j \in triple_action_total_group.
Proof.
rewrite inE /triple_action_totalb.
apply/forallP=> p; apply/existsP.
exists (triple_partition_map j p).
rewrite /triple_partition_actionb triple_permute_codes_tperm_zero.
rewrite -(triple_partition_codes_zero (triple_partition_map j p)).
exact: triple_partition_map_action.
Qed.

Lemma pair_action_total (s : S6) : pair_action_totalb s.
Proof.
have sfull : s \in [set: S6] by rewrite inE.
rewrite -(gen_tperm ord0) in sfull.
have ssub : <<[set tperm ord0 j | j in 'I_6]>>%g
    \subset pair_action_total_group.
  rewrite gen_subG; apply/subsetP=> u /imsetP[j _ ->].
  exact: pair_action_total_tperm.
have := subsetP ssub s sfull.
by rewrite inE.
Qed.

Lemma triple_action_total (s : S6) : triple_action_totalb s.
Proof.
have sfull : s \in [set: S6] by rewrite inE.
rewrite -(gen_tperm ord0) in sfull.
have ssub : <<[set tperm ord0 j | j in 'I_6]>>%g
    \subset triple_action_total_group.
  rewrite gen_subG; apply/subsetP=> u /imsetP[j _ ->].
  exact: triple_action_total_tperm.
have := subsetP ssub s sfull.
by rewrite inE.
Qed.

Lemma pair_partition_action_exists_certificate :
  [forall s : S6, [forall p : pair_partition,
    [exists q : pair_partition, pair_partition_actionb s p q]]].
Proof. by apply/forallP=> s; exact: pair_action_total s. Qed.

Lemma triple_partition_action_exists_certificate :
  [forall s : S6, [forall p : triple_partition,
    [exists q : triple_partition, triple_partition_actionb s p q]]].
Proof. by apply/forallP=> s; exact: triple_action_total s. Qed.

Lemma pair_partition_actionP s p :
  pair_partition_actionb s p (pair_partition_action s p).
Proof.
have hex : [exists q, pair_partition_actionb s p q] :=
  (elimT forallP (elimT forallP
    pair_partition_action_exists_certificate s) p).
rewrite /pair_partition_action.
case: pickP => [q hq|hnone] //.
move/existsP: hex=> [q hq].
by move: (hnone q); rewrite hq.
Qed.

Lemma triple_partition_actionP s p :
  triple_partition_actionb s p (triple_partition_action s p).
Proof.
have hex : [exists q, triple_partition_actionb s p q] :=
  (elimT forallP (elimT forallP
    triple_partition_action_exists_certificate s) p).
rewrite /triple_partition_action.
case: pickP => [q hq|hnone] //.
move/existsP: hex=> [q hq].
by move: (hnone q); rewrite hq.
Qed.

Section Evaluation.

Variable R : comNzRingType.

Lemma root_at_nat_assignment_perm (roots : 6.-tuple R) (s : S6) n :
  (n < 6)%N ->
  root_at_nat (assignment_values roots (finfun s)) n =
    root_at_nat roots (val (s (inord n))).
Proof.
move=> hn.
rewrite /root_at_nat -(inordK hn).
rewrite -!(@tnth_nth 6 R 0) /assignment_values !tnth_mktuple ffunE.
by rewrite inordK.
Qed.

Lemma block_code_value_assignment_perm
    (roots : 6.-tuple R) (s : S6) c code :
  all (fun n => n < 6)%N code ->
  block_code_value (assignment_values roots (finfun s)) c code =
    block_code_value roots c (permute_code s code).
Proof.
move=> hcode.
rewrite /block_code_value /permute_code big_map.
apply: eq_big_seq=> n hn.
by rewrite root_at_nat_assignment_perm ?(allP hcode n hn).
Qed.

Lemma descriptor_codes_value_assignment_perm
    (roots : 6.-tuple R) (s : S6) x codes :
  all code_wfb codes ->
  descriptor_codes_value (assignment_values roots (finfun s)) x codes =
    descriptor_codes_value roots x (permute_codes s codes).
Proof.
move=> hcodes.
rewrite /descriptor_codes_value /permute_codes big_map.
apply: eq_big_seq=> code hcode.
rewrite block_code_value_sort.
congr ((tnth x ord0)%:R - _).
apply: block_code_value_assignment_perm.
have /and3P[_ _] := allP hcodes code hcode.
exact.
Qed.

Theorem pair_descriptor_perm (roots : 6.-tuple R) x (s : S6) p :
  sparse_eval_ring (assignment_values roots (finfun s))
      (pair_sparse_descriptor_value x p) =
    sparse_eval_ring roots
      (pair_sparse_descriptor_value x (pair_partition_action s p)).
Proof.
rewrite !pair_descriptor_member_codes.
rewrite descriptor_codes_value_assignment_perm ?pair_codes_wfb //.
apply: descriptor_codes_value_perm.
exact: pair_partition_actionP.
Qed.

Theorem triple_descriptor_perm (roots : 6.-tuple R) x (s : S6) p :
  sparse_eval_ring (assignment_values roots (finfun s))
      (triple_sparse_descriptor_value x p) =
    sparse_eval_ring roots
      (triple_sparse_descriptor_value x (triple_partition_action s p)).
Proof.
rewrite !triple_descriptor_member_codes.
rewrite descriptor_codes_value_assignment_perm ?triple_codes_wfb //.
apply: descriptor_codes_value_perm.
exact: triple_partition_actionP.
Qed.

End Evaluation.

(** Converting the canonical sorted natural-number block codes to finite sets
    makes their relationship with MathComp's set action literal. *)
Definition code_set (code : seq nat) : {set 'I_6} :=
  [set i | val i \in code].

Definition codes_set (codes : seq (seq nat)) : {set {set 'I_6}} :=
  [set C | C \in [seq code_set code | code <- codes]].

Lemma code_set_sort code : code_set (sort leq code) = code_set code.
Proof.
apply/setP=> i; rewrite /code_set !inE.
exact: perm_mem (permEl (perm_sort leq code)) (val i).
Qed.

Lemma codes_set_perm codes1 codes2 :
  perm_eq codes1 codes2 -> codes_set codes1 = codes_set codes2.
Proof.
move=> hperm; apply/setP=> C; rewrite /codes_set !inE.
apply/mapP/mapP=> [[code hcode ->]|[code hcode ->]].
- exists code=> //.
  by rewrite -(perm_mem hperm code).
- exists code=> //.
  by rewrite (perm_mem hperm code).
Qed.

Lemma code_set_permute (s : S6) code :
  all (fun n => n < 6)%N code ->
  code_set (permute_code s code) = block_action (code_set code) s.
Proof.
move=> hcode; apply/setP=> i.
rewrite /code_set !inE /block_action.
apply/mapP/imsetP.
- move=> [n hn hni].
  have hn6 : (n < 6)%N := allP hcode n hn.
  exists (inord n : 'I_6).
  + rewrite inE.
    have hinord : val (inord n : 'I_6) = n := inordK hn6.
    by rewrite hinord.
  + apply: val_inj; exact: hni.
- move=> [j].
  rewrite /code_set inE=> hj ->.
  exists (val j)=> //.
  by rewrite /permute_code inord_val.
Qed.

Lemma codes_set_permute (s : S6) codes :
  all code_wfb codes ->
  codes_set (permute_codes s codes) =
    (block_action^*) (codes_set codes) s.
Proof.
move=> hcodes; apply/setP=> C.
rewrite /codes_set !inE /block_action.
apply/mapP/imsetP.
- move=> [scode].
  rewrite /permute_codes=> /mapP[code hcode ->] ->.
  exists (code_set code).
  + rewrite /codes_set inE.
    by apply/mapP; exists code.
  + rewrite code_set_sort.
    apply: code_set_permute.
    have /and3P[_ _] := allP hcodes code hcode.
    exact.
- move=> [B].
  rewrite /codes_set inE=> /mapP[code hcode ->] ->.
  exists (sort leq (permute_code s code)).
  + rewrite /permute_codes.
    by apply/mapP; exists code.
  + rewrite code_set_sort.
    symmetry.
    apply: code_set_permute.
    have /and3P[_ _] := allP hcodes code hcode.
    exact.
Qed.

(** The sequence encoding and the set encoding agree definitionally up to
    the standard sequence/set image views. *)
Lemma pair_code_set_block p b :
  code_set [seq val (pair_member p b u) | u <- enum 'I_2] =
    pair_table_block p b.
Proof.
apply/setP=> i; rewrite /code_set /pair_table_block inE.
apply/mapP/imsetP.
- move=> [u hu hui].
  exists u; first by rewrite inE.
  apply: val_inj; exact: hui.
- move=> [u _ ->].
  apply: (@ex_intro2 _ _ _ u).
  + exact: mem_enum u.
  + reflexivity.
Qed.

Lemma triple_code_set_block p b :
  code_set [seq val (triple_member p b u) | u <- enum 'I_3] =
    triple_table_block p b.
Proof.
apply/setP=> i; rewrite /code_set /triple_table_block inE.
apply/mapP/imsetP.
- move=> [u hu hui].
  exists u; first by rewrite inE.
  apply: val_inj; exact: hui.
- move=> [u _ ->].
  apply: (@ex_intro2 _ _ _ u).
  + exact: mem_enum u.
  + reflexivity.
Qed.

Lemma pair_codes_setE p :
  codes_set (pair_member_blocks p) = pair_table_blocks p.
Proof.
apply/setP=> B.
rewrite /codes_set /pair_member_blocks /pair_table_blocks inE.
apply/mapP/imsetP.
- move=> [code /mapP[b hb ->] ->].
  exists b; first by rewrite inE.
  exact: pair_code_set_block.
- move=> [b _ ->].
  exists [seq val (pair_member p b u) | u <- enum 'I_2].
  + apply/mapP; exists b; first by rewrite mem_enum.
    reflexivity.
  + exact: esym (pair_code_set_block p b).
Qed.

Lemma triple_codes_setE p :
  codes_set (triple_member_blocks p) = triple_table_blocks p.
Proof.
apply/setP=> B.
rewrite /codes_set /triple_member_blocks /triple_table_blocks inE.
apply/mapP/imsetP.
- move=> [code /mapP[b hb ->] ->].
  exists b; first by rewrite inE.
  exact: triple_code_set_block.
- move=> [b _ ->].
  exists [seq val (triple_member p b u) | u <- enum 'I_3].
  + apply/mapP; exists b; first by rewrite mem_enum.
    reflexivity.
  + exact: esym (triple_code_set_block p b).
Qed.

Lemma code_set_injective_wfb c d :
  code_wfb c -> code_wfb d -> code_set c = code_set d -> c = d.
Proof.
move=> /and3P[sc uc bc] /and3P[sd ud bd] hset.
apply: (sorted_eq leq_trans anti_leq sc sd).
apply: (uniq_perm uc ud)=> n.
case hn6: (n < 6)%N.
- have hm := congr1 (fun S : {set 'I_6} => (inord n : 'I_6) \in S) hset.
  rewrite /code_set !inE in hm.
  have hinord : val (inord n : 'I_6) = n := inordK hn6.
  by rewrite hinord in hm.
- apply/idP/idP=> hn.
  + have := allP bc n hn.
    by rewrite hn6.
  + have := allP bd n hn.
    by rewrite hn6.
Qed.

Lemma codes_set_perm_injective codes1 codes2 :
  all code_wfb codes1 -> all code_wfb codes2 ->
  uniq codes1 -> uniq codes2 ->
  codes_set codes1 = codes_set codes2 -> perm_eq codes1 codes2.
Proof.
move=> wf1 wf2 u1 u2 hset.
apply: (uniq_perm u1 u2)=> code.
apply/idP/idP=> hcode.
- have hcset : code_set code \in codes_set codes2.
    rewrite -hset /codes_set inE.
    by apply/mapP; exists code.
  rewrite /codes_set inE in hcset.
  move/mapP: hcset=> [d hd hdc].
  have hcd : code = d.
    apply: code_set_injective_wfb.
    + exact: allP wf1 code hcode.
    + exact: allP wf2 d hd.
    + exact: hdc.
  by rewrite hcd.
- have hcset : code_set code \in codes_set codes1.
    rewrite hset /codes_set inE.
    by apply/mapP; exists code.
  rewrite /codes_set inE in hcset.
  move/mapP: hcset=> [d hd hdc].
  have hcd : code = d.
    apply: code_set_injective_wfb.
    + exact: allP wf2 code hcode.
    + exact: allP wf1 d hd.
    + exact: hdc.
  by rewrite hcd.
Qed.

Lemma pair_table_blocks_injective : injective pair_table_blocks.
Proof.
move=> p q hpq; apply: pair_codes_perm_injective.
apply: codes_set_perm_injective.
- exact: pair_codes_wfb.
- exact: pair_codes_wfb.
- exact: pair_codes_uniq.
- exact: pair_codes_uniq.
- by rewrite pair_codes_setE hpq pair_codes_setE.
Qed.

Lemma triple_table_blocks_injective : injective triple_table_blocks.
Proof.
move=> p q hpq; apply: triple_codes_perm_injective.
apply: codes_set_perm_injective.
- exact: triple_codes_wfb.
- exact: triple_codes_wfb.
- exact: triple_codes_uniq.
- exact: triple_codes_uniq.
- by rewrite triple_codes_setE hpq triple_codes_setE.
Qed.

Lemma pair_partition_action_blocks s p :
  (block_action^*) (pair_table_blocks p) s =
    pair_table_blocks (pair_partition_action s p).
Proof.
rewrite -!pair_codes_setE -codes_set_permute ?pair_codes_wfb //.
apply: codes_set_perm.
exact: pair_partition_actionP.
Qed.

Lemma triple_partition_action_blocks s p :
  (block_action^*) (triple_table_blocks p) s =
    triple_table_blocks (triple_partition_action s p).
Proof.
rewrite -!triple_codes_setE -codes_set_permute ?triple_codes_wfb //.
apply: codes_set_perm.
exact: triple_partition_actionP.
Qed.

(** Membership in the table stabilizer is exactly the statement that the
    induced finite-table action fixes its index. *)

Lemma pair_partition_action_fixedP s p :
  reflect (pair_partition_action s p = p) (s \in pair_table_group p).
Proof.
apply: (iffP idP).
- move=> hs; apply: pair_table_blocks_injective.
  rewrite -pair_partition_action_blocks.
  exact: astabs_setact hs.
- move=> hp; rewrite /pair_table_group.
  have hsfix : s \in 'C[pair_table_blocks p | (block_action^*)].
    apply/astab1P.
    by rewrite pair_partition_action_blocks hp.
  by move: hsfix; rewrite astab1_set.
Qed.

Lemma triple_partition_action_fixedP s p :
  reflect (triple_partition_action s p = p) (s \in triple_table_group p).
Proof.
apply: (iffP idP).
- move=> hs; apply: triple_table_blocks_injective.
  rewrite -triple_partition_action_blocks.
  exact: astabs_setact hs.
- move=> hp; rewrite /triple_table_group.
  have hsfix : s \in 'C[triple_table_blocks p | (block_action^*)].
    apply/astab1P.
    by rewrite triple_partition_action_blocks hp.
  by move: hsfix; rewrite astab1_set.
Qed.

End PolynomialFormulasSexticDescriptorAction.
