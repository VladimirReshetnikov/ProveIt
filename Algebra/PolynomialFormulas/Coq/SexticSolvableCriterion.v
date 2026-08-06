From mathcomp Require Import all_ssreflect all_fingroup all_solvable.
From Stdlib Require Import Lia.
From PolynomialFormulas Require Import SexticSparseResolvents
  SexticBlockStabilizers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasSexticSolvableCriterion.

Import PolynomialFormulasSexticBlockStabilizers.
Import PolynomialFormulasSexticSparseResolvents.

Local Open Scope group_scope.
Local Open Scope action_scope.

Lemma transitive_group_nontrivial (G : {group S6}) :
  [transitive G, on [set: 'I_6] | 'P] -> G :!=: 1.
Proof.
move=> trG; apply/eqP=> G1.
have d6G : 6 %| #|G|.
  by move: (atrans_dvd trG); rewrite cardsT card_ord.
by move: d6G; rewrite G1 cards1.
Qed.

Lemma natural_action_pointwise_kernel_trivial (G : {group S6}) :
  'C_G([set: 'I_6] | 'P) \subset [1 S6].
Proof.
exact: subset_trans (subsetIr _ _) perm_astab_setT_sub1.
Qed.

Lemma solvable_transitive_not_primitive (G : {group S6}) :
  solvable G -> [transitive G, on [set: 'I_6] | 'P] ->
  ~~ [primitive G, on [set: 'I_6] | 'P].
Proof.
move=> solG trG; apply/negP=> primG.
have ntG := transitive_group_nontrivial trG.
case: (solvable_norm_abelem solG (normal_refl G) ntG) =>
  H [sHG nHG ntH abH].
have trH : [transitive H, on [set: 'I_6] | 'P].
  case: (prim_trans_norm primG nHG) => [sHC | //].
  have sH1 := subset_trans sHC (natural_action_pointwise_kernel_trivial G).
  have H1 : H :==: 1 by rewrite eqEsubset sH1 sub1G.
  by move: ntH; rewrite H1.
have d6H : 6 %| #|H|.
  by move: (atrans_dvd trH); rewrite cardsT card_ord.
case/is_abelemP: abH => q qprime /abelem_pgroup qH.
have d2H : 2 %| #|H| := dvdn_trans (isT : 2 %| 6) d6H.
have d3H : 3 %| #|H| := dvdn_trans (isT : 3 %| 6) d6H.
have q2 : 2 = q.
  apply/eqP.
  exact: (pgroupP qH 2 (isT : prime 2) d2H).
have q3 : 3 = q.
  apply/eqP.
  exact: (pgroupP qH 3 (isT : prime 3) d3H).
by rewrite -q2 in q3.
Qed.

Local Open Scope nat_scope.

Definition index_pairs6 : seq (nat * nat) :=
  flatten [seq [seq (i, j) | j <- iota 0 6] | i <- iota 0 6].

Definition same_relation_seq (xs ys : seq nat) : bool :=
  all (fun ij =>
    (nth 0 xs ij.1 == nth 0 xs ij.2) ==
      (nth 0 ys ij.1 == nth 0 ys ij.2)) index_pairs6.

Definition uniform_seq (k : nat) (xs : seq nat) : bool :=
  all (fun x => count (pred1 x) xs == k) xs.

Definition raw_pair_tables : seq (seq nat) := [::
  [::0;0;1;1;2;2]; [::0;0;1;2;1;2]; [::0;0;1;2;2;1];
  [::0;1;0;1;2;2]; [::0;1;0;2;1;2]; [::0;1;0;2;2;1];
  [::0;1;1;0;2;2]; [::0;1;2;0;1;2]; [::0;1;2;0;2;1];
  [::0;1;1;2;0;2]; [::0;1;2;1;0;2]; [::0;1;2;2;0;1];
  [::0;1;1;2;2;0]; [::0;1;2;1;2;0]; [::0;1;2;2;1;0]
].

Definition raw_triple_tables : seq (seq nat) := [::
  [::0;0;0;1;1;1]; [::0;0;1;0;1;1]; [::0;0;1;1;0;1];
  [::0;0;1;1;1;0]; [::0;1;0;0;1;1]; [::0;1;0;1;0;1];
  [::0;1;0;1;1;0]; [::0;1;1;0;0;1]; [::0;1;1;0;1;0];
  [::0;1;1;1;0;0]
].

Definition raw_pair_matches xs :=
  has (same_relation_seq xs) raw_pair_tables.

Definition raw_triple_matches xs :=
  has (same_relation_seq xs) raw_triple_tables.

Lemma raw_pair_tables_correct :
  raw_pair_tables = [seq val t | t <- pair_label_table].
Proof. by []. Qed.

Lemma raw_triple_tables_correct :
  raw_triple_tables = [seq val t | t <- triple_label_table].
Proof. by []. Qed.

Lemma pair_label_table_complete :
  [forall a0 : 'I_3, [forall a1 : 'I_3, [forall a2 : 'I_3,
  [forall a3 : 'I_3, [forall a4 : 'I_3, [forall a5 : 'I_3,
    uniform_seq 2 [:: val a0; val a1; val a2; val a3; val a4; val a5] ==>
      raw_pair_matches
        [:: val a0; val a1; val a2; val a3; val a4; val a5]]]]]]].
Proof.
apply/forallP=> a0; case: a0 => [[|[|[|a0]]] ha0] //.
all: apply/forallP=> a1; case: a1 => [[|[|[|a1]]] ha1] //.
all: apply/forallP=> a2; case: a2 => [[|[|[|a2]]] ha2] //.
all: apply/forallP=> a3; case: a3 => [[|[|[|a3]]] ha3] //.
all: apply/forallP=> a4; case: a4 => [[|[|[|a4]]] ha4] //.
all: apply/forallP=> a5; case: a5 => [[|[|[|a5]]] ha5] //.
all: vm_compute.
Qed.

Lemma triple_label_table_complete :
  [forall a0 : 'I_2, [forall a1 : 'I_2, [forall a2 : 'I_2,
  [forall a3 : 'I_2, [forall a4 : 'I_2, [forall a5 : 'I_2,
    uniform_seq 3 [:: val a0; val a1; val a2; val a3; val a4; val a5] ==>
      raw_triple_matches
        [:: val a0; val a1; val a2; val a3; val a4; val a5]]]]]]].
Proof.
apply/forallP=> a0; case: a0 => [[|[|a0]] ha0] //.
all: apply/forallP=> a1; case: a1 => [[|[|a1]] ha1] //.
all: apply/forallP=> a2; case: a2 => [[|[|a2]] ha2] //.
all: apply/forallP=> a3; case: a3 => [[|[|a3]] ha3] //.
all: apply/forallP=> a4; case: a4 => [[|[|a4]] ha4] //.
all: apply/forallP=> a5; case: a5 => [[|[|a5]] ha5] //.
all: vm_compute.
Qed.

Lemma nth_ord_imset (T : finType) (x0 : T) (s : seq T) n :
  size s = n ->
  (fun i : 'I_n => nth x0 s i) @: [set: 'I_n] = [set:: s].
Proof.
move=> size_s; apply/setP=> x; apply/imsetP/idP.
  move=> [i _ ->]; rewrite inE mem_nth // size_s; exact: ltn_ord.
rewrite inE => sx.
have ix_s : index x s < size s by rewrite index_mem.
pose i : 'I_n := Ordinal (eq_ind _ (fun m => index x s < m) ix_s _ size_s).
exists i; first by rewrite inE.
by rewrite /= nth_index.
Qed.

Lemma pair_label_fiber_size p (b : 'I_3) :
  size (label_fiber (pair_label p) (val b)) = 2.
Proof.
case: p => [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp] //;
case: b => [[|[|[|b]]] hb] //;
rewrite /label_fiber
  PolynomialFormulasSexticBlockStabilizers.enum_ord6E;
vm_compute; reflexivity.
Qed.

Lemma triple_label_fiber_size p (b : 'I_2) :
  size (label_fiber (triple_label p) (val b)) = 3.
Proof.
case: p => [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp] //;
case: b => [[|[|b]] hb] //;
rewrite /label_fiber
  PolynomialFormulasSexticBlockStabilizers.enum_ord6E;
vm_compute; reflexivity.
Qed.

Lemma pair_table_blockE p (b : 'I_3) :
  pair_table_block p b = [set i | tnth (pair_label p) i == val b].
Proof.
rewrite /pair_table_block /pair_member.
rewrite (@nth_ord_imset _ ord0 _ 2
  (pair_label_fiber_size p b)).
apply/setP=> i.
rewrite inE /label_fiber.
rewrite (@mem_filter _ (fun i0 : 'I_6 =>
  tnth (pair_label p) i0 == val b) i (enum 'I_6)).
have hi : i \in enum 'I_6 by exact: fintype.mem_enum _ _.
rewrite hi andbT.
by rewrite inE.
Qed.

Lemma triple_table_blockE p (b : 'I_2) :
  triple_table_block p b = [set i | tnth (triple_label p) i == val b].
Proof.
rewrite /triple_table_block /triple_member.
rewrite (@nth_ord_imset _ ord0 _ 3
  (triple_label_fiber_size p b)).
apply/setP=> i.
rewrite inE /label_fiber.
rewrite (@mem_filter _ (fun i0 : 'I_6 =>
  tnth (triple_label p) i0 == val b) i (enum 'I_6)).
have hi : i \in enum 'I_6 by exact: fintype.mem_enum _ _.
rewrite hi andbT.
by rewrite inE.
Qed.

Lemma pair_label_bound p (i : 'I_6) : tnth (pair_label p) i < 3.
Proof.
case: p => [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp] //;
case: i => [[|[|[|[|[|[|i]]]]]] hi] //; vm_compute.
Qed.

Lemma triple_label_bound p (i : 'I_6) : tnth (triple_label p) i < 2.
Proof.
case: p => [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp] //;
case: i => [[|[|[|[|[|[|i]]]]]] hi] //; vm_compute.
Qed.

Lemma pair_label_onto p (b : 'I_3) :
  exists i : 'I_6, tnth (pair_label p) i = val b.
Proof.
have mb : val b \in pair_label p.
  case: p => [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|q]]]]]]]]]]]]]]] hq] //;
  case: b => [[|[|[|c]]] hc] //; vm_compute.
case/tnthP: mb => i hi; exists i.
exact: esym hi.
Qed.

Lemma triple_label_onto p (b : 'I_2) :
  exists i : 'I_6, tnth (triple_label p) i = val b.
Proof.
have mb : val b \in triple_label p.
  case: p => [[|[|[|[|[|[|[|[|[|[|q]]]]]]]]]] hq] //;
  case: b => [[|[|c]] hc] //; vm_compute.
case/tnthP: mb => i hi; exists i.
exact: esym hi.
Qed.

Lemma pair_table_blocks_preim p :
  pair_table_blocks p =
    preim_partition (fun i => tnth (pair_label p) i) [set: 'I_6].
Proof.
rewrite /pair_table_blocks /preim_partition /equivalence_partition.
apply/setP=> B; apply/imsetP/imsetP.
- move=> [b _ ->].
  case: (pair_label_onto p b) => i hi.
  exists i; first by rewrite inE.
  rewrite pair_table_blockE.
  apply/setP=> j.
  by rewrite !inE hi eq_sym.
- move=> [i _ ->].
  pose b : 'I_3 := Ordinal (pair_label_bound p i).
  exists b; first by rewrite inE.
  rewrite pair_table_blockE.
  apply/setP=> j.
  by rewrite !inE /b /= eq_sym.
Qed.

Lemma triple_table_blocks_preim p :
  triple_table_blocks p =
    preim_partition (fun i => tnth (triple_label p) i) [set: 'I_6].
Proof.
rewrite /triple_table_blocks /preim_partition /equivalence_partition.
apply/setP=> B; apply/imsetP/imsetP.
- move=> [b _ ->].
  case: (triple_label_onto p b) => i hi.
  exists i; first by rewrite inE.
  rewrite triple_table_blockE.
  apply/setP=> j.
  by rewrite !inE hi eq_sym.
- move=> [i _ ->].
  pose b : 'I_2 := Ordinal (triple_label_bound p i).
  exists b; first by rewrite inE.
  rewrite triple_table_blockE.
  apply/setP=> j.
  by rewrite !inE /b /= eq_sym.
Qed.

Lemma solvable_transitive_imprimitive (G : {group S6}) :
  solvable G -> [transitive G, on [set: 'I_6] | 'P] ->
  exists Q, imprimitivity_system G [set: 'I_6] 'P Q.
Proof.
move=> solG trG.
move: (solvable_transitive_not_primitive solG trG).
by rewrite /primitive trG /= negbK => /existsP.
Qed.

Lemma invariant_partition_uniform (G : {group S6})
    (Q : {set {set 'I_6}}) :
  [transitive G, on [set: 'I_6] | 'P] ->
  partition Q [set: 'I_6] ->
  [acts G, on Q | block_action] ->
  {in Q &, forall A B : {set 'I_6}, #|A| = #|B|}.
Proof.
move=> trG partQ actQ A B QA QB.
have tiQ := partition_trivIset partQ.
have nzA := partition_neq0 partQ QA.
have nzB := partition_neq0 partQ QB.
case/set0Pn: nzA => x Ax.
case/set0Pn: nzB => y By.
have Sx : x \in [set: 'I_6] by rewrite inE.
have Sy : y \in [set: 'I_6] by rewrite inE.
have [g Gg hxy] := atransP2 trG Sx Sy.
have actAQ : block_action A g \in Q by rewrite (actsP actQ).
have yact : y \in block_action A g.
  by apply/imsetP; exists x.
have eqAB : block_action A g = B.
  by rewrite -(def_pblock tiQ actAQ yact) -(def_pblock tiQ QB By).
by rewrite -(card_setact 'P A g) eqAB.
Qed.

Lemma count_map_enum (T R : finType) (f : T -> R) (y : R) :
  count (pred1 y) [seq f x | x <- enum T] =
    #|[pred x | f x == y]|.
Proof.
rewrite count_map enumT cardE size_filter.
apply: eq_count => x.
rewrite /preim /pred1 /=.
by rewrite inE.
Qed.

Lemma count_enum_pred (T : finType) (P : pred T) :
  count P (enum T) = #|P|.
Proof. by rewrite enumT cardE size_filter. Qed.

Lemma same_relation_seq_nth xs ys i j :
  same_relation_seq xs ys -> i < 6 -> j < 6 ->
  (nth 0 xs i == nth 0 xs j) = (nth 0 ys i == nth 0 ys j).
Proof.
rewrite /same_relation_seq => /allP h li lj.
have memij : (i, j) \in index_pairs6.
  rewrite /index_pairs6.
  apply/flatten_mapP; exists i.
    by rewrite mem_iota add0n li.
  apply/mapP; exists j.
    by rewrite mem_iota add0n lj.
  by [].
exact: (elimT eqP (h (i, j) memij)).
Qed.

Lemma preim_partition_ext (T R S : finType) (D : {set T})
    (f : T -> R) (g : T -> S) :
  (forall x y, x \in D -> y \in D ->
    (f x == f y) = (g x == g y)) ->
  preim_partition f D = preim_partition g D.
Proof.
move=> fg; rewrite /preim_partition /equivalence_partition.
apply/setP=> B; apply/imsetP/imsetP=> [[x Dx ->] | [x Dx ->]];
exists x => //; apply/setP=> y; rewrite !inE.
  by case Dy: (y \in D) => //; rewrite fg.
by case Dy: (y \in D) => //; rewrite fg.
Qed.

Lemma pair_label_table_complete_fun (lab : 'I_6 -> 'I_3) :
  uniform_seq 2 [seq val (lab i) | i <- enum 'I_6] ->
  raw_pair_matches [seq val (lab i) | i <- enum 'I_6].
Proof.
rewrite PolynomialFormulasSexticBlockStabilizers.enum_ord6E /=.
move=> unif.
move/forallP: pair_label_table_complete => h0.
move/forallP: (h0 (lab o0)) => h1.
move/forallP: (h1 (lab o1)) => h2.
move/forallP: (h2 (lab o2)) => h3.
move/forallP: (h3 (lab o3)) => h4.
move/forallP: (h4 (lab o4)) => h5.
move/implyP: (h5 (lab o5)) => h.
exact: h unif.
Qed.

Lemma triple_label_table_complete_fun (lab : 'I_6 -> 'I_2) :
  uniform_seq 3 [seq val (lab i) | i <- enum 'I_6] ->
  raw_triple_matches [seq val (lab i) | i <- enum 'I_6].
Proof.
rewrite PolynomialFormulasSexticBlockStabilizers.enum_ord6E /=.
move=> unif.
move/forallP: triple_label_table_complete => h0.
move/forallP: (h0 (lab o0)) => h1.
move/forallP: (h1 (lab o1)) => h2.
move/forallP: (h2 (lab o2)) => h3.
move/forallP: (h3 (lab o3)) => h4.
move/forallP: (h4 (lab o4)) => h5.
move/implyP: (h5 (lab o5)) => h.
exact: h unif.
Qed.

Lemma nth_map_enum_ord6 n (lab : 'I_6 -> 'I_n) (i : 'I_6) :
  nth 0 [seq val (lab x) | x <- enum 'I_6] i = val (lab i).
Proof.
by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum.
Qed.

Lemma nth_tuple_nat (t : 6.-tuple nat) (i : 'I_6) :
  nth 0 t i = tnth t i.
Proof. exact: esym (tnth_nth 0 t i). Qed.

Lemma raw_pair_match_partition (lab : 'I_6 -> 'I_3) :
  raw_pair_matches [seq val (lab i) | i <- enum 'I_6] ->
  exists p, preim_partition lab [set: 'I_6] = pair_table_blocks p.
Proof.
rewrite /raw_pair_matches raw_pair_tables_correct.
case/hasP=> ys /mapP[t mt ->] rel.
have it : index t pair_label_table < 15.
  by rewrite -size_pair_label_table index_mem.
pose p : pair_partition := Ordinal it.
have pt : pair_label p = t.
  by rewrite /pair_label /p /= nth_index.
exists p; rewrite pair_table_blocks_preim.
have labrel i j :
    (lab i == lab j) =
      (tnth (pair_label p) i == tnth (pair_label p) j).
  have relij := same_relation_seq_nth rel (ltn_ord i) (ltn_ord j).
  rewrite !nth_map_enum_ord6 !nth_tuple_nat -pt in relij.
  by rewrite -val_eqE.
rewrite /preim_partition /equivalence_partition.
apply/setP=> B; apply/imsetP/imsetP=> [[i _ ->] | [i _ ->]];
exists i => //; apply/setP=> j; rewrite !inE.
  by rewrite labrel.
by rewrite labrel.
Qed.

Lemma raw_triple_match_partition (lab : 'I_6 -> 'I_2) :
  raw_triple_matches [seq val (lab i) | i <- enum 'I_6] ->
  exists p, preim_partition lab [set: 'I_6] = triple_table_blocks p.
Proof.
rewrite /raw_triple_matches raw_triple_tables_correct.
case/hasP=> ys /mapP[t mt ->] rel.
have it : index t triple_label_table < 10.
  by rewrite -size_triple_label_table index_mem.
pose p : triple_partition := Ordinal it.
have pt : triple_label p = t.
  by rewrite /triple_label /p /= nth_index.
exists p; rewrite triple_table_blocks_preim.
have labrel i j :
    (lab i == lab j) =
      (tnth (triple_label p) i == tnth (triple_label p) j).
  have relij := same_relation_seq_nth rel (ltn_ord i) (ltn_ord j).
  rewrite !nth_map_enum_ord6 !nth_tuple_nat -pt in relij.
  by rewrite -val_eqE.
rewrite /preim_partition /equivalence_partition.
apply/setP=> B; apply/imsetP/imsetP=> [[i _ ->] | [i _ ->]];
exists i => //; apply/setP=> j; rewrite !inE.
  by rewrite labrel.
by rewrite labrel.
Qed.

Lemma nat_between_one_six n :
  1 < n -> n < 6 -> n = 2 \/ n = 3 \/ n = 4 \/ n = 5.
Proof.
move=> /ltP h1 /ltP h6.
lia.
Qed.

Lemma invariant_partition_is_table (G : {group S6})
    (Q : {set {set 'I_6}}) :
  [transitive G, on [set: 'I_6] | 'P] ->
  partition Q [set: 'I_6] ->
  [acts G, on Q | block_action] ->
  1 < #|Q| < 6 ->
  (exists p, Q = pair_table_blocks p) \/
    (exists p, Q = triple_table_blocks p).
Proof.
move=> trG partQ actQ ntQ.
have nzQ : Q != set0.
  apply/eqP=> Q0; move: ntQ.
  by rewrite Q0 cards0.
case/set0Pn: nzQ => B QB.
pose k := #|B|.
have uniAB := invariant_partition_uniform trG partQ actQ.
have uniK A : A \in Q -> #|A| = k.
  by move=> QA; exact: uniAB A B QA QB.
have card6 : 6 = #|Q| * k.
  have := card_uniform_partition uniK partQ.
  by rewrite cardsT card_ord.
have [q1 q6] := andP ntQ.
have qgt1 := elimT ltP q1.
have qlt6 := elimT ltP q6.
have card_cases :
    (#|Q| = 3 /\ k = 2) \/ (#|Q| = 2 /\ k = 3).
  have qcases := nat_between_one_six q1 q6.
  case: qcases => [q2 | [q3 | [q4 | q5]]].
  - right; split=> //; rewrite q2 mulnE in card6; nia.
  - left; split=> //; rewrite q3 mulnE in card6; nia.
  - rewrite q4 mulnE in card6; nia.
  - rewrite q5 mulnE in card6; nia.
have tiQ := partition_trivIset partQ.
have covQ : cover Q = [set: 'I_6] := cover_partition partQ.
have pxQ x : pblock Q x \in Q.
  apply: pblock_mem.
  by rewrite covQ inE.
case: card_cases => [[q3 k2] | [q2 k3]].
- left.
  pose lab x : 'I_3 :=
    cast_ord q3 (enum_rank_in QB (pblock Q x)).
  have lab_eq x y :
      (lab x == lab y) = (pblock Q x == pblock Q y).
    apply/eqP/eqP=> hxy.
      change (cast_ord q3 (enum_rank_in QB (pblock Q x)) =
        cast_ord q3 (enum_rank_in QB (pblock Q y))) in hxy.
      have rankeq :
          enum_rank_in QB (pblock Q x) = enum_rank_in QB (pblock Q y).
        exact: (@cast_ord_inj #|Q| 3 q3 _ _ hxy).
      exact: (@enum_rank_in_inj _ B B Q QB QB _ _
        (pxQ x) (pxQ y) rankeq).
    by rewrite /lab hxy.
  have unif : uniform_seq 2 [seq val (lab i) | i <- enum 'I_6].
    apply/allP=> z /mapP[x _ ->].
    rewrite count_map count_enum_pred.
    have -> :
        #|preim (fun i : 'I_6 => val (lab i))
            (pred1 (val (lab x)))| = #|pblock Q x|.
      apply: eq_card => i.
      rewrite /preim /pred1.
      rewrite !inE val_eqE (lab_eq i x) eq_sym.
      have covx : x \in cover Q by rewrite covQ inE.
      exact: eq_pblock tiQ covx.
    by rewrite (uniK _ (pxQ x)) k2.
  have table_match := pair_label_table_complete_fun unif.
  case: (raw_pair_match_partition table_match) => p hp.
  exists p.
  have preim_lab :
      preim_partition lab [set: 'I_6] =
        preim_partition (pblock Q) [set: 'I_6].
    apply: preim_partition_ext => x y _ _.
    exact: lab_eq x y.
  rewrite -(preim_partition_pblock partQ) -preim_lab.
  exact: hp.
- right.
  pose lab x : 'I_2 :=
    cast_ord q2 (enum_rank_in QB (pblock Q x)).
  have lab_eq x y :
      (lab x == lab y) = (pblock Q x == pblock Q y).
    apply/eqP/eqP=> hxy.
      change (cast_ord q2 (enum_rank_in QB (pblock Q x)) =
        cast_ord q2 (enum_rank_in QB (pblock Q y))) in hxy.
      have rankeq :
          enum_rank_in QB (pblock Q x) = enum_rank_in QB (pblock Q y).
        exact: (@cast_ord_inj #|Q| 2 q2 _ _ hxy).
      exact: (@enum_rank_in_inj _ B B Q QB QB _ _
        (pxQ x) (pxQ y) rankeq).
    by rewrite /lab hxy.
  have unif : uniform_seq 3 [seq val (lab i) | i <- enum 'I_6].
    apply/allP=> z /mapP[x _ ->].
    rewrite count_map count_enum_pred.
    have -> :
        #|preim (fun i : 'I_6 => val (lab i))
            (pred1 (val (lab x)))| = #|pblock Q x|.
      apply: eq_card => i.
      rewrite /preim /pred1.
      rewrite !inE val_eqE (lab_eq i x) eq_sym.
      have covx : x \in cover Q by rewrite covQ inE.
      exact: eq_pblock tiQ covx.
    by rewrite (uniK _ (pxQ x)) k3.
  have table_match := triple_label_table_complete_fun unif.
  case: (raw_triple_match_partition table_match) => p hp.
  exists p.
  have preim_lab :
      preim_partition lab [set: 'I_6] =
        preim_partition (pblock Q) [set: 'I_6].
    apply: preim_partition_ext => x y _ _.
    exact: lab_eq x y.
  rewrite -(preim_partition_pblock partQ) -preim_lab.
  exact: hp.
Qed.

Theorem solvable_transitive_S6_criterion (G : {group S6}) :
  [transitive G, on [set: 'I_6] | 'P] ->
  solvable G <->
    (exists p, G \subset pair_table_group p) \/
    (exists p, G \subset triple_table_group p).
Proof.
move=> trG; split.
- move=> solG.
  case: (solvable_transitive_imprimitive solG trG) => Q impQ.
  move/and3P: impQ => [partQ actQ ntQ].
  rewrite cardsT card_ord in ntQ.
  case: (invariant_partition_is_table trG partQ actQ ntQ) =>
      [[p Qp] | [p Qp]].
  - left; exists p; rewrite /pair_table_group -Qp.
    apply/subsetP=> g Gg; apply/astabsP=> A.
    exact: actsP actQ g Gg A.
  - right; exists p; rewrite /triple_table_group -Qp.
    apply/subsetP=> g Gg; apply/astabsP=> A.
    exact: actsP actQ g Gg A.
- case=> [[p subG] | [p subG]].
  - exact: solvableS subG (pair_table_group_solvable p).
  - exact: solvableS subG (triple_table_group_solvable p).
Qed.

End PolynomialFormulasSexticSolvableCriterion.
