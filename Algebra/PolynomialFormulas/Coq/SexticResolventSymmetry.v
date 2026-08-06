From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import SexticSparsePolynomials
  SexticSparseResolvents SexticNewtonPowerSums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Permuting the six roots permutes the finite pair and triple descriptor
    tables.  The only table-specific part of the argument is discharged by
    the two closed Boolean certificates below.  Everything after them is a
    generic proof about finite products and polynomial coefficients. *)
Module PolynomialFormulasSexticResolventSymmetry.

Import PolynomialFormulasSexticSparsePolynomials.
Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.

Definition pair_blocks_table : seq (seq (seq nat)) := [::
  [:: [:: 0; 1]; [:: 2; 3]; [:: 4; 5]];
  [:: [:: 0; 1]; [:: 2; 4]; [:: 3; 5]];
  [:: [:: 0; 1]; [:: 2; 5]; [:: 3; 4]];
  [:: [:: 0; 2]; [:: 1; 3]; [:: 4; 5]];
  [:: [:: 0; 2]; [:: 1; 4]; [:: 3; 5]];
  [:: [:: 0; 2]; [:: 1; 5]; [:: 3; 4]];
  [:: [:: 0; 3]; [:: 1; 2]; [:: 4; 5]];
  [:: [:: 0; 3]; [:: 1; 4]; [:: 2; 5]];
  [:: [:: 0; 3]; [:: 1; 5]; [:: 2; 4]];
  [:: [:: 0; 4]; [:: 1; 2]; [:: 3; 5]];
  [:: [:: 0; 4]; [:: 1; 3]; [:: 2; 5]];
  [:: [:: 0; 4]; [:: 1; 5]; [:: 2; 3]];
  [:: [:: 0; 5]; [:: 1; 2]; [:: 3; 4]];
  [:: [:: 0; 5]; [:: 1; 3]; [:: 2; 4]];
  [:: [:: 0; 5]; [:: 1; 4]; [:: 2; 3]]
].

Definition triple_blocks_table : seq (seq (seq nat)) := [::
  [:: [:: 0; 1; 2]; [:: 3; 4; 5]];
  [:: [:: 0; 1; 3]; [:: 2; 4; 5]];
  [:: [:: 0; 1; 4]; [:: 2; 3; 5]];
  [:: [:: 0; 1; 5]; [:: 2; 3; 4]];
  [:: [:: 0; 2; 3]; [:: 1; 4; 5]];
  [:: [:: 0; 2; 4]; [:: 1; 3; 5]];
  [:: [:: 0; 2; 5]; [:: 1; 3; 4]];
  [:: [:: 0; 3; 4]; [:: 1; 2; 5]];
  [:: [:: 0; 3; 5]; [:: 1; 2; 4]];
  [:: [:: 0; 4; 5]; [:: 1; 2; 3]]
].

Definition pair_member_blocks (p : pair_partition) : seq (seq nat) :=
  [seq [seq val (pair_member p b s) | s <- enum 'I_2] |
    b <- enum 'I_3].

Definition triple_member_blocks (p : triple_partition) : seq (seq nat) :=
  [seq [seq val (triple_member p b s) | s <- enum 'I_3] |
    b <- enum 'I_2].

Lemma enum_ord2E : enum 'I_2 =
    [:: @Ordinal 2 0 isT; @Ordinal 2 1 isT].
Proof.
apply: (inj_map val_inj).
by rewrite val_enum_ord.
Qed.

Lemma enum_ord3E : enum 'I_3 =
    [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT].
Proof.
apply: (inj_map val_inj).
by rewrite val_enum_ord.
Qed.

Lemma enum_ord6E : enum 'I_6 =
    [:: @Ordinal 6 0 isT; @Ordinal 6 1 isT; @Ordinal 6 2 isT;
        @Ordinal 6 3 isT; @Ordinal 6 4 isT; @Ordinal 6 5 isT].
Proof.
apply: (inj_map val_inj).
by rewrite val_enum_ord.
Qed.

Lemma pair_member_blocks_correct (p : pair_partition) :
  pair_member_blocks p = nth [::] pair_blocks_table p.
Proof.
case: p => [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp] //;
rewrite /pair_member_blocks /pair_member /label_fiber
  enum_ord2E enum_ord3E enum_ord6E;
vm_compute; reflexivity.
Qed.

Lemma triple_member_blocks_correct (p : triple_partition) :
  triple_member_blocks p = nth [::] triple_blocks_table p.
Proof.
case: p => [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp] //;
rewrite /triple_member_blocks /triple_member /label_fiber
  enum_ord2E enum_ord3E enum_ord6E;
vm_compute; reflexivity.
Qed.

Definition swap_zero (j n : nat) : nat :=
  if n == 0 then j else if n == j then 0 else n.

Definition pair_partition_codes_nat (j p : nat) :=
  [seq sort leq (map (swap_zero j) block) |
    block <- nth [::] pair_blocks_table p].

Definition triple_partition_codes_nat (j p : nat) :=
  [seq sort leq (map (swap_zero j) block) |
    block <- nth [::] triple_blocks_table p].

Definition pair_partition_codes (j : nat) (p : pair_partition) :=
  pair_partition_codes_nat j p.

Definition triple_partition_codes (j : nat) (p : triple_partition) :=
  triple_partition_codes_nat j p.

Definition pair_actionb j p q :=
  perm_eq (pair_partition_codes j p) (pair_partition_codes_nat 0 q).

Definition triple_actionb j p q :=
  perm_eq (triple_partition_codes j p) (triple_partition_codes_nat 0 q).

Definition pair_partition_map_table : seq (seq nat) := [::
  [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14];
  [:: 0; 1; 2; 6; 9; 12; 3; 10; 13; 4; 7; 14; 5; 8; 11];
  [:: 6; 9; 12; 3; 4; 5; 0; 14; 11; 1; 13; 8; 2; 10; 7];
  [:: 3; 13; 10; 0; 14; 11; 6; 7; 8; 12; 2; 5; 9; 1; 4];
  [:: 14; 4; 7; 13; 1; 8; 12; 2; 5; 9; 10; 11; 6; 3; 0];
  [:: 11; 8; 5; 10; 7; 2; 9; 4; 1; 6; 3; 0; 12; 13; 14]
].

Definition triple_partition_map_table : seq (seq nat) := [::
  [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9];
  [:: 0; 1; 2; 3; 9; 8; 7; 6; 5; 4];
  [:: 0; 9; 8; 7; 4; 5; 6; 3; 2; 1];
  [:: 9; 1; 6; 5; 4; 3; 2; 7; 8; 0];
  [:: 8; 6; 2; 4; 3; 5; 1; 7; 0; 9];
  [:: 7; 5; 4; 3; 2; 1; 6; 0; 8; 9]
].

Definition pair_partition_map_nat (j : 'I_6) (p : pair_partition) : nat :=
  nth 0 (nth [::] pair_partition_map_table j) p.

Definition triple_partition_map_nat (j : 'I_6) (p : triple_partition) : nat :=
  nth 0 (nth [::] triple_partition_map_table j) p.

Lemma pair_partition_map_nat_bound j p :
  (pair_partition_map_nat j p < 15)%N.
Proof.
case: j => [[|[|[|[|[|[|j]]]]]] hj] //;
case: p => [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp] //.
Qed.

Lemma triple_partition_map_nat_bound j p :
  (triple_partition_map_nat j p < 10)%N.
Proof.
case: j => [[|[|[|[|[|[|j]]]]]] hj] //;
case: p => [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp] //.
Qed.

Definition pair_partition_map (j : 'I_6) (p : pair_partition) :
    pair_partition :=
  inord (pair_partition_map_nat j p).

Definition triple_partition_map (j : 'I_6) (p : triple_partition) :
    triple_partition :=
  inord (triple_partition_map_nat j p).

Lemma pair_action_complete_certificate :
  [forall j : 'I_6, [forall p : pair_partition,
    perm_eq (pair_partition_codes j p)
      (pair_partition_codes_nat 0 (pair_partition_map_nat j p))]].
Proof.
apply/forallP=> j; apply/forallP=> p.
case: j => [[|[|[|[|[|[|j]]]]]] hj].
all: try by [].
all: case: p => [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp].
all: try by [].
all: vm_compute; exact I.
Qed.

Lemma triple_action_complete_certificate :
  [forall j : 'I_6, [forall p : triple_partition,
    perm_eq (triple_partition_codes j p)
      (triple_partition_codes_nat 0 (triple_partition_map_nat j p))]].
Proof.
apply/forallP=> j; apply/forallP=> p.
case: j => [[|[|[|[|[|[|j]]]]]] hj].
all: try by [].
all: case: p => [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp].
all: try by [].
all: vm_compute; exact I.
Qed.

Lemma pair_partition_map_row_size (j : 'I_6) :
  size (nth [::] pair_partition_map_table j) = 15%N.
Proof.
case: (unliftP ord0 j)=> [j1 ->|->] /=; last by [].
case: (unliftP ord0 j1)=> [j2 ->|->] /=; last by [].
case: (unliftP ord0 j2)=> [j3 ->|->] /=; last by [].
case: (unliftP ord0 j3)=> [j4 ->|->] /=; last by [].
case: (unliftP ord0 j4)=> [j5 ->|->] /=; last by [].
by rewrite (ord1 j5).
Qed.

Lemma pair_partition_map_row_uniq (j : 'I_6) :
  uniq (nth [::] pair_partition_map_table j).
Proof.
case: (unliftP ord0 j)=> [j1 ->|->] /=; last by [].
case: (unliftP ord0 j1)=> [j2 ->|->] /=; last by [].
case: (unliftP ord0 j2)=> [j3 ->|->] /=; last by [].
case: (unliftP ord0 j3)=> [j4 ->|->] /=; last by [].
case: (unliftP ord0 j4)=> [j5 ->|->] /=; last by [].
by rewrite (ord1 j5).
Qed.

Lemma triple_partition_map_row_size (j : 'I_6) :
  size (nth [::] triple_partition_map_table j) = 10%N.
Proof.
case: (unliftP ord0 j)=> [j1 ->|->] /=; last by [].
case: (unliftP ord0 j1)=> [j2 ->|->] /=; last by [].
case: (unliftP ord0 j2)=> [j3 ->|->] /=; last by [].
case: (unliftP ord0 j3)=> [j4 ->|->] /=; last by [].
case: (unliftP ord0 j4)=> [j5 ->|->] /=; last by [].
by rewrite (ord1 j5).
Qed.

Lemma triple_partition_map_row_uniq (j : 'I_6) :
  uniq (nth [::] triple_partition_map_table j).
Proof.
case: (unliftP ord0 j)=> [j1 ->|->] /=; last by [].
case: (unliftP ord0 j1)=> [j2 ->|->] /=; last by [].
case: (unliftP ord0 j2)=> [j3 ->|->] /=; last by [].
case: (unliftP ord0 j3)=> [j4 ->|->] /=; last by [].
case: (unliftP ord0 j4)=> [j5 ->|->] /=; last by [].
by rewrite (ord1 j5).
Qed.

Lemma pair_partition_map_action (j : 'I_6) (p : pair_partition) :
  pair_actionb j p (pair_partition_map j p).
Proof.
rewrite /pair_actionb /pair_partition_map /pair_partition_codes.
rewrite inordK ?pair_partition_map_nat_bound //.
exact: (elimT forallP (elimT forallP pair_action_complete_certificate j) p).
Qed.

Lemma triple_partition_map_action (j : 'I_6) (p : triple_partition) :
  triple_actionb j p (triple_partition_map j p).
Proof.
rewrite /triple_actionb /triple_partition_map /triple_partition_codes.
rewrite inordK ?triple_partition_map_nat_bound //.
exact: (elimT forallP (elimT forallP triple_action_complete_certificate j) p).
Qed.

Lemma val_pair_partition_map j p :
  val (pair_partition_map j p) = pair_partition_map_nat j p.
Proof. exact: inordK (pair_partition_map_nat_bound j p). Qed.

Lemma val_triple_partition_map j p :
  val (triple_partition_map j p) = triple_partition_map_nat j p.
Proof. exact: inordK (triple_partition_map_nat_bound j p). Qed.

Lemma pair_partition_map_injective (j : 'I_6) :
  injective (pair_partition_map j).
Proof.
move=> p1 p2 h.
have hnat : pair_partition_map_nat j p1 = pair_partition_map_nat j p2.
  rewrite -(val_pair_partition_map j p1) -(val_pair_partition_map j p2).
  by rewrite h.
apply: val_inj; apply/eqP.
have hp1 : (p1 < size (nth [::] pair_partition_map_table j))%N
  by rewrite pair_partition_map_row_size.
have hp2 : (p2 < size (nth [::] pair_partition_map_table j))%N
  by rewrite pair_partition_map_row_size.
rewrite -(nth_uniq 0 hp1 hp2 (pair_partition_map_row_uniq j)).
apply/eqP; exact hnat.
Qed.

Lemma triple_partition_map_injective (j : 'I_6) :
  injective (triple_partition_map j).
Proof.
move=> p1 p2 h.
have hnat : triple_partition_map_nat j p1 = triple_partition_map_nat j p2.
  rewrite -(val_triple_partition_map j p1)
    -(val_triple_partition_map j p2).
  by rewrite h.
apply: val_inj; apply/eqP.
have hp1 : (p1 < size (nth [::] triple_partition_map_table j))%N
  by rewrite triple_partition_map_row_size.
have hp2 : (p2 < size (nth [::] triple_partition_map_table j))%N
  by rewrite triple_partition_map_row_size.
rewrite -(nth_uniq 0 hp1 hp2 (triple_partition_map_row_uniq j)).
apply/eqP; exact hnat.
Qed.

Lemma val_tperm_zero (j i : 'I_6) :
  val (tperm ord0 j i) = swap_zero j (val i).
Proof.
case hi0: (i == ord0).
- move/eqP: hi0=> ->.
  by rewrite tpermL /swap_zero eqxx.
case hij: (i == j).
- have hijE : i = j := eqP hij.
  have hj0 : val j != 0.
    apply/eqP=> h.
    have hiord : i = ord0.
      rewrite hijE; apply: val_inj; exact h.
    by move: hi0; rewrite hiord eqxx.
  rewrite hijE tpermR /swap_zero.
  case: ifP=> [h|h].
  - by move/eqP: h=> ->.
  - by rewrite eqxx.
have h0i : ord0 != i by rewrite eq_sym hi0.
have hji : j != i by rewrite eq_sym hij.
rewrite tpermD // /swap_zero.
have hvi0 : val i != 0.
  apply/eqP=> h; move/eqP: hi0; apply.
  apply: val_inj; exact h.
have hvij : val i != val j.
  apply/eqP=> h; move/eqP: hij; apply.
  apply: val_inj; exact h.
case: ifP=> [h|_].
- by move/eqP: h; move/eqP: hvi0.
case: ifP=> [h|_].
- by move/eqP: h; move/eqP: hvij.
reflexivity.
Qed.

Lemma pair_partition_codesE j p :
  pair_partition_codes j p =
    [seq sort leq code |
      code <- [seq map (swap_zero j) block |
        block <- pair_member_blocks p]].
Proof.
rewrite /pair_partition_codes /pair_partition_codes_nat
  pair_member_blocks_correct.
by rewrite -map_comp.
Qed.

Lemma triple_partition_codesE j p :
  triple_partition_codes j p =
    [seq sort leq code |
      code <- [seq map (swap_zero j) block |
        block <- triple_member_blocks p]].
Proof.
rewrite /triple_partition_codes /triple_partition_codes_nat
  triple_member_blocks_correct.
by rewrite -map_comp.
Qed.

Lemma pair_partition_codes_zero p :
  pair_partition_codes 0 p = pair_member_blocks p.
Proof.
rewrite pair_partition_codesE pair_member_blocks_correct.
case: p => [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp] //;
vm_compute; reflexivity.
Qed.

Lemma triple_partition_codes_zero p :
  triple_partition_codes 0 p = triple_member_blocks p.
Proof.
rewrite triple_partition_codesE triple_member_blocks_correct.
case: p => [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp] //;
vm_compute; reflexivity.
Qed.

(** Ring-valued evaluation of the sparse descriptor programs. *)
Section DescriptorEvaluation.

Variable R : comPzRingType.

Lemma sparse_eval_ring_nat_const (values : 6.-tuple R) n :
  sparse_eval_ring values (nat_sparse_const n) = n%:R.
Proof. by rewrite /nat_sparse_const sparse_eval_ring_const. Qed.

Lemma sparse_eval_ring_pair_block_value (values : 6.-tuple R) x p b :
  sparse_eval_ring values (pair_sparse_block_value x p b) =
    \prod_(s : 'I_2)
      ((tnth x ord_max)%:R - tnth values (pair_member p b s)).
Proof.
rewrite /pair_sparse_block_value sparse_eval_ring_product big_map big_enum.
apply: eq_bigr=> s _.
by rewrite sparse_eval_ring_sub sparse_eval_ring_nat_const
  sparse_eval_ring_var.
Qed.

Lemma sparse_eval_ring_triple_block_value (values : 6.-tuple R) x p b :
  sparse_eval_ring values (triple_sparse_block_value x p b) =
    \prod_(s : 'I_3)
      ((tnth x ord_max)%:R - tnth values (triple_member p b s)).
Proof.
rewrite /triple_sparse_block_value sparse_eval_ring_product big_map big_enum.
apply: eq_bigr=> s _.
by rewrite sparse_eval_ring_sub sparse_eval_ring_nat_const
  sparse_eval_ring_var.
Qed.

Lemma sparse_eval_ring_pair_descriptor_value (values : 6.-tuple R) x p :
  sparse_eval_ring values (pair_sparse_descriptor_value x p) =
    \prod_(b : 'I_3)
      ((tnth x ord0)%:R -
        \prod_(s : 'I_2)
          ((tnth x ord_max)%:R - tnth values (pair_member p b s))).
Proof.
rewrite /pair_sparse_descriptor_value sparse_eval_ring_product
  big_map big_enum.
apply: eq_bigr=> b _.
by rewrite sparse_eval_ring_sub sparse_eval_ring_nat_const
  sparse_eval_ring_pair_block_value.
Qed.

Lemma sparse_eval_ring_triple_descriptor_value (values : 6.-tuple R) x p :
  sparse_eval_ring values (triple_sparse_descriptor_value x p) =
    \prod_(b : 'I_2)
      ((tnth x ord0)%:R -
        \prod_(s : 'I_3)
          ((tnth x ord_max)%:R - tnth values (triple_member p b s))).
Proof.
rewrite /triple_sparse_descriptor_value sparse_eval_ring_product
  big_map big_enum.
apply: eq_bigr=> b _.
by rewrite sparse_eval_ring_sub sparse_eval_ring_nat_const
  sparse_eval_ring_triple_block_value.
Qed.

Definition root_at_nat (roots : 6.-tuple R) (n : nat) : R :=
  nth 0 roots n.

Definition block_code_value (roots : 6.-tuple R) (c : R)
    (code : seq nat) : R :=
  \prod_(n <- code) (c - root_at_nat roots n).

Definition descriptor_codes_value (roots : 6.-tuple R) (x : parameter)
    (codes : seq (seq nat)) : R :=
  \prod_(code <- codes)
    ((tnth x ord0)%:R -
      block_code_value roots (tnth x ord_max)%:R code).

Lemma block_code_value_perm roots c code1 code2 :
  perm_eq code1 code2 ->
  block_code_value roots c code1 = block_code_value roots c code2.
Proof. exact: perm_big. Qed.

Lemma descriptor_codes_value_perm roots x codes1 codes2 :
  perm_eq codes1 codes2 ->
  descriptor_codes_value roots x codes1 =
    descriptor_codes_value roots x codes2.
Proof. exact: perm_big. Qed.

Lemma block_code_value_sort roots c code :
  block_code_value roots c (sort leq code) =
    block_code_value roots c code.
Proof.
apply: block_code_value_perm.
exact: permEl (perm_sort leq code).
Qed.

Lemma descriptor_codes_value_map_sort roots x codes :
  descriptor_codes_value roots x
      [seq sort leq code | code <- codes] =
    descriptor_codes_value roots x codes.
Proof.
rewrite /descriptor_codes_value big_map.
apply: eq_bigr=> code _.
by rewrite block_code_value_sort.
Qed.

Lemma pair_descriptor_member_codes (roots : 6.-tuple R) x p :
  sparse_eval_ring roots (pair_sparse_descriptor_value x p) =
    descriptor_codes_value roots x (pair_member_blocks p).
Proof.
rewrite sparse_eval_ring_pair_descriptor_value
  /descriptor_codes_value /pair_member_blocks big_map big_enum.
apply: eq_bigr=> b _.
congr ((tnth x ord0)%:R - _).
rewrite /block_code_value big_map big_enum.
apply: eq_bigr=> s _.
by rewrite /root_at_nat -(@tnth_nth 6 R 0 roots (pair_member p b s)).
Qed.

Lemma triple_descriptor_member_codes (roots : 6.-tuple R) x p :
  sparse_eval_ring roots (triple_sparse_descriptor_value x p) =
    descriptor_codes_value roots x (triple_member_blocks p).
Proof.
rewrite sparse_eval_ring_triple_descriptor_value
  /descriptor_codes_value /triple_member_blocks big_map big_enum.
apply: eq_bigr=> b _.
congr ((tnth x ord0)%:R - _).
rewrite /block_code_value big_map big_enum.
apply: eq_bigr=> s _.
by rewrite /root_at_nat -(@tnth_nth 6 R 0 roots (triple_member p b s)).
Qed.

Lemma root_at_nat_tperm_zero (roots : 6.-tuple R) (j i : 'I_6) :
  root_at_nat
      (assignment_values roots (finfun (tperm ord0 j))) (val i) =
    root_at_nat roots (swap_zero j (val i)).
Proof.
rewrite -[LHS]tnth_nth /assignment_values tnth_mktuple ffunE.
rewrite -val_tperm_zero /root_at_nat.
exact: tnth_nth.
Qed.

Lemma pair_descriptor_tperm_codes (roots : 6.-tuple R) x j p :
  sparse_eval_ring
      (assignment_values roots (finfun (tperm ord0 j)))
      (pair_sparse_descriptor_value x p) =
    descriptor_codes_value roots x
      [seq map (swap_zero j) code | code <- pair_member_blocks p].
Proof.
rewrite pair_descriptor_member_codes /descriptor_codes_value
  /pair_member_blocks !big_map.
apply: eq_bigr=> b _.
congr ((tnth x ord0)%:R - _).
rewrite /block_code_value !big_map.
apply: eq_bigr=> s _.
by rewrite root_at_nat_tperm_zero.
Qed.

Lemma triple_descriptor_tperm_codes (roots : 6.-tuple R) x j p :
  sparse_eval_ring
      (assignment_values roots (finfun (tperm ord0 j)))
      (triple_sparse_descriptor_value x p) =
    descriptor_codes_value roots x
      [seq map (swap_zero j) code | code <- triple_member_blocks p].
Proof.
rewrite triple_descriptor_member_codes /descriptor_codes_value
  /triple_member_blocks !big_map.
apply: eq_bigr=> b _.
congr ((tnth x ord0)%:R - _).
rewrite /block_code_value !big_map.
apply: eq_bigr=> s _.
by rewrite root_at_nat_tperm_zero.
Qed.

Lemma pair_descriptor_tperm (roots : 6.-tuple R) x j p :
  sparse_eval_ring
      (assignment_values roots (finfun (tperm ord0 j)))
      (pair_sparse_descriptor_value x p) =
    sparse_eval_ring roots
      (pair_sparse_descriptor_value x (pair_partition_map j p)).
Proof.
rewrite pair_descriptor_tperm_codes.
rewrite pair_descriptor_member_codes.
rewrite -(pair_partition_codes_zero (pair_partition_map j p)).
rewrite -(descriptor_codes_value_map_sort roots x
  [seq map (swap_zero j) code | code <- pair_member_blocks p]).
rewrite -(pair_partition_codesE j p).
apply: descriptor_codes_value_perm.
move: (pair_partition_map_action j p).
by rewrite /pair_actionb /pair_partition_codes.
Qed.

Lemma triple_descriptor_tperm (roots : 6.-tuple R) x j p :
  sparse_eval_ring
      (assignment_values roots (finfun (tperm ord0 j)))
      (triple_sparse_descriptor_value x p) =
    sparse_eval_ring roots
      (triple_sparse_descriptor_value x (triple_partition_map j p)).
Proof.
rewrite triple_descriptor_tperm_codes.
rewrite triple_descriptor_member_codes.
rewrite -(triple_partition_codes_zero (triple_partition_map j p)).
rewrite -(descriptor_codes_value_map_sort roots x
  [seq map (swap_zero j) code | code <- triple_member_blocks p]).
rewrite -(triple_partition_codesE j p).
apply: descriptor_codes_value_perm.
move: (triple_partition_map_action j p).
by rewrite /triple_actionb /triple_partition_codes.
Qed.

End DescriptorEvaluation.

(** Interpreting an ascending sparse coefficient list as a polynomial lets
    us transport descriptor symmetry to every individual coefficient. *)
Section ResolventPolynomial.

Variable R : comNzRingType.

Fixpoint coefficient_list_poly (values : 6.-tuple R)
    (p : coefficient_list) : {poly R} :=
  if p is a :: p' then
    (sparse_eval_ring values a)%:P +
      'X * coefficient_list_poly values p'
  else 0.

Lemma coefficient_list_poly_add values p q :
  coefficient_list_poly values (coefficient_add p q) =
    coefficient_list_poly values p + coefficient_list_poly values q.
Proof.
elim: p q=> [|a p ih] [|b q] //=.
all: try by rewrite add0r.
all: try by rewrite addr0.
by rewrite sparse_eval_ring_add polyCD ih mulrDr addrACA.
Qed.

Lemma coefficient_list_poly_scale values a p :
  coefficient_list_poly values (coefficient_scale a p) =
    (sparse_eval_ring values a)%:P * coefficient_list_poly values p.
Proof.
elim: p=> [|b p ih] /=.
- by rewrite mulr0.
- rewrite sparse_eval_ring_mul polyCM ih mulrDr.
  by rewrite mulrCA.
Qed.

Lemma coefficient_list_poly_shift values p :
  coefficient_list_poly values (coefficient_shift p) =
    'X * coefficient_list_poly values p.
Proof.
by rewrite /coefficient_shift /= sparse_eval_ring_zero polyC0 add0r.
Qed.

Lemma coefficient_list_poly_linear_product values roots :
  coefficient_list_poly values (linear_product roots) =
    \prod_(r <- roots)
      ('X - (sparse_eval_ring values r)%:P).
Proof.
elim: roots=> [|r roots ih] /=.
- rewrite sparse_eval_ring_const big_nil.
  by rewrite mulr0 addr0.
- rewrite coefficient_list_poly_add coefficient_list_poly_scale
    coefficient_list_poly_shift sparse_eval_ring_neg polyCN ih big_cons.
  by rewrite mulrBl mulNr addrC.
Qed.

Lemma coefficient_list_poly_pair_resolvent values x :
  coefficient_list_poly values (pair_sparse_resolvent x) =
    \prod_(p : pair_partition)
      ('X -
        (sparse_eval_ring values
          (pair_sparse_descriptor_value x p))%:P).
Proof.
rewrite /pair_sparse_resolvent coefficient_list_poly_linear_product
  big_map big_enum.
by apply: eq_bigr=> p _.
Qed.

Lemma coefficient_list_poly_triple_resolvent values x :
  coefficient_list_poly values (triple_sparse_resolvent x) =
    \prod_(p : triple_partition)
      ('X -
        (sparse_eval_ring values
          (triple_sparse_descriptor_value x p))%:P).
Proof.
rewrite /triple_sparse_resolvent coefficient_list_poly_linear_product
  big_map big_enum.
by apply: eq_bigr=> p _.
Qed.

Lemma coefficient_list_poly_coef values p i :
  (coefficient_list_poly values p)`_i =
    sparse_eval_ring values (nth sparse_zero p i).
Proof.
elim: p i=> [|a p ih] [|i] /=.
- by rewrite coef0 sparse_eval_ring_zero.
- by rewrite coef0 sparse_eval_ring_zero.
- by rewrite coefD coefC coefXM eqxx addr0.
- by rewrite coefD coefC coefXM /= add0r ih.
Qed.

Lemma coefficient_list_poly_pair_tperm (roots : 6.-tuple R) x j :
  coefficient_list_poly
      (assignment_values roots (finfun (tperm ord0 j)))
      (pair_sparse_resolvent x) =
    coefficient_list_poly roots (pair_sparse_resolvent x).
Proof.
rewrite !coefficient_list_poly_pair_resolvent.
under [LHS]eq_bigr=> p _ do rewrite pair_descriptor_tperm.
symmetry.
by rewrite (reindex_inj (@pair_partition_map_injective j)).
Qed.

Lemma coefficient_list_poly_triple_tperm (roots : 6.-tuple R) x j :
  coefficient_list_poly
      (assignment_values roots (finfun (tperm ord0 j)))
      (triple_sparse_resolvent x) =
    coefficient_list_poly roots (triple_sparse_resolvent x).
Proof.
rewrite !coefficient_list_poly_triple_resolvent.
under [LHS]eq_bigr=> p _ do rewrite triple_descriptor_tperm.
symmetry.
by rewrite (reindex_inj (@triple_partition_map_injective j)).
Qed.

Lemma pair_sparse_resolvent_coefficient_tperm
    (roots : 6.-tuple R) x i j :
  sparse_eval_ring
      (assignment_values roots (finfun (tperm ord0 j)))
      (pair_sparse_resolvent_coefficient x i) =
    sparse_eval_ring roots (pair_sparse_resolvent_coefficient x i).
Proof.
rewrite /pair_sparse_resolvent_coefficient.
rewrite -(coefficient_list_poly_coef
  (assignment_values roots (finfun (tperm ord0 j)))
  (pair_sparse_resolvent x) i).
rewrite -(coefficient_list_poly_coef roots (pair_sparse_resolvent x) i).
by rewrite coefficient_list_poly_pair_tperm.
Qed.

Lemma triple_sparse_resolvent_coefficient_tperm
    (roots : 6.-tuple R) x i j :
  sparse_eval_ring
      (assignment_values roots (finfun (tperm ord0 j)))
      (triple_sparse_resolvent_coefficient x i) =
    sparse_eval_ring roots (triple_sparse_resolvent_coefficient x i).
Proof.
rewrite /triple_sparse_resolvent_coefficient.
rewrite -(coefficient_list_poly_coef
  (assignment_values roots (finfun (tperm ord0 j)))
  (triple_sparse_resolvent x) i).
rewrite -(coefficient_list_poly_coef roots (triple_sparse_resolvent x) i).
by rewrite coefficient_list_poly_triple_tperm.
Qed.

Definition sparse_permutation_invariant
    (p : sparse_polynomial) (g : {perm 'I_6}) : Prop :=
  forall roots : 6.-tuple R,
    sparse_eval_ring (assignment_values roots (finfun g)) p =
      sparse_eval_ring roots p.

Lemma assignment_values_permM (roots : 6.-tuple R)
    (g h : {perm 'I_6}) :
  assignment_values roots (finfun (g * h)%g) =
    assignment_values
      (assignment_values roots (finfun h)) (finfun g).
Proof.
apply: eq_from_tnth=> i.
by rewrite /assignment_values !tnth_mktuple !ffunE permM.
Qed.

Lemma sparse_permutation_invariant_one p :
  sparse_permutation_invariant p 1%g.
Proof.
move=> roots.
suff -> : assignment_values roots (finfun (1%g : {perm 'I_6})) = roots
  by [].
apply: eq_from_tnth=> i.
by rewrite /assignment_values tnth_mktuple ffunE perm1.
Qed.

Lemma sparse_permutation_invariant_mul p g h :
  sparse_permutation_invariant p g ->
  sparse_permutation_invariant p h ->
  sparse_permutation_invariant p (g * h)%g.
Proof.
move=> hg hh roots.
rewrite assignment_values_permM.
rewrite hg.
exact: hh.
Qed.

Lemma tperm_star_product (x y : 'I_6) :
  x != ord0 -> y != ord0 -> x != y ->
  tperm x y =
    (tperm ord0 x * tperm ord0 y * tperm ord0 x)%g.
Proof.
move=> hx0 hy0 hxy.
have h := tpermJ ord0 y (tperm ord0 x).
rewrite tpermL in h.
rewrite tpermD in h.
- rewrite /conjg tpermV mulgA in h.
  exact: esym h.
- by rewrite eq_sym hy0.
- exact hxy.
Qed.

Lemma sparse_permutation_invariant_tperm p
    (hstar : forall j : 'I_6,
      sparse_permutation_invariant p (tperm ord0 j))
    (x y : 'I_6) :
  sparse_permutation_invariant p (tperm x y).
Proof.
case hx0: (x == ord0).
- move/eqP: hx0=> ->.
  exact: hstar.
case hy0: (y == ord0).
- move/eqP: hy0=> ->.
  rewrite tpermC.
  exact: hstar.
case hxy: (x == y).
- move/eqP: hxy=> ->.
  rewrite tperm1.
  exact: sparse_permutation_invariant_one.
have hx0' : x != ord0 by rewrite hx0.
have hy0' : y != ord0 by rewrite hy0.
have hxy' : x != y by rewrite hxy.
rewrite (tperm_star_product hx0' hy0' hxy').
apply: sparse_permutation_invariant_mul.
- apply: sparse_permutation_invariant_mul; exact: hstar.
- exact: hstar.
Qed.

Lemma sparse_permutation_invariant_all p
    (hstar : forall j : 'I_6,
      sparse_permutation_invariant p (tperm ord0 j))
    (g : {perm 'I_6}) :
  sparse_permutation_invariant p g.
Proof.
have [ts -> _] := prod_tpermP g.
elim: ts=> [|[x y] ts ih] /=.
- rewrite big_nil.
  exact: sparse_permutation_invariant_one.
- rewrite big_cons.
  apply: sparse_permutation_invariant_mul.
  - exact: sparse_permutation_invariant_tperm hstar x y.
  - exact: ih.
Qed.

Lemma pair_sparse_resolvent_coefficient_perm x i g :
  sparse_permutation_invariant
    (pair_sparse_resolvent_coefficient x i) g.
Proof.
apply: sparse_permutation_invariant_all=> j roots.
exact: pair_sparse_resolvent_coefficient_tperm.
Qed.

Lemma triple_sparse_resolvent_coefficient_perm x i g :
  sparse_permutation_invariant
    (triple_sparse_resolvent_coefficient x i) g.
Proof.
apply: sparse_permutation_invariant_all=> j roots.
exact: triple_sparse_resolvent_coefficient_tperm.
Qed.

Theorem pair_sparse_resolvent_coefficient_invariant
    (roots : 6.-tuple R) x i :
  permutation_invariant_at roots
    (pair_sparse_resolvent_coefficient x i).
Proof.
move=> a ha.
rewrite assignment_code_injectiveb in ha.
have hainj : injective a := elimT (@injectiveP _ _ a) ha.
pose g : {perm 'I_6} := perm hainj.
have havals : assignment_values roots a =
    assignment_values roots (finfun g).
  apply: eq_from_tnth=> j.
  by rewrite /assignment_values !tnth_mktuple !ffunE /g permE.
rewrite havals.
exact: pair_sparse_resolvent_coefficient_perm.
Qed.

Theorem triple_sparse_resolvent_coefficient_invariant
    (roots : 6.-tuple R) x i :
  permutation_invariant_at roots
    (triple_sparse_resolvent_coefficient x i).
Proof.
move=> a ha.
rewrite assignment_code_injectiveb in ha.
have hainj : injective a := elimT (@injectiveP _ _ a) ha.
pose g : {perm 'I_6} := perm hainj.
have havals : assignment_values roots a =
    assignment_values roots (finfun g).
  apply: eq_from_tnth=> j.
  by rewrite /assignment_values !tnth_mktuple !ffunE /g permE.
rewrite havals.
exact: triple_sparse_resolvent_coefficient_perm.
Qed.

End ResolventPolynomial.

End PolynomialFormulasSexticResolventSymmetry.
