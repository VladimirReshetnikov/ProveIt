From Stdlib Require Import Arith Bool Lia List Vector ZArith.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.
From Undecidability.MuRec.Util Require Import recomp.

From PolynomialFormulas Require Import
  SexticMuRecComputability SexticMuRecFactorDecision
  SexticMuRecSparseEvaluator SexticMuRecCollisionEvaluator
  SexticMuRecCollisionSemantics SexticMuRecResolventRootEvaluator
  SexticMuRecMixedRadixSemantics SexticRecursiveCore
  SexticSparsePolynomials SexticSparseResolvents
  SexticPowerSumSymmetric SexticNewtonPowerSums
  SexticComputedResolvents SexticResolventSymmetry SexticSeparatingSearch
  SexticMuRecSeparatingInstance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecDescriptorSemantics.

Module SP := PolynomialFormulasSexticSparsePolynomials.
Module SR := PolynomialFormulasSexticSparseResolvents.
Module SRS := PolynomialFormulasSexticResolventSymmetry.
Module SE := PolynomialFormulasSexticMuRecSparseEvaluator.
Module CE := PolynomialFormulasSexticMuRecCollisionEvaluator.
Module CS := PolynomialFormulasSexticMuRecCollisionSemantics.
Module RE := PolynomialFormulasSexticMuRecResolventRootEvaluator.
Module MRX := PolynomialFormulasSexticMuRecMixedRadixSemantics.

Definition sparse_term_one : SP.sparse_term := (1, SP.exponent_zero).

Definition radix_digit (radix code position : nat) : nat :=
  ((code %/ (radix ^ position)) %% radix)%N.

Definition equal_indicator (left right : nat) : nat :=
  if Nat.eqb left right then 1%N else 0%N.

Definition pair_member_value (partition block slot : nat) : nat :=
  match block, slot with
  | 0%N, 0%N => nth 0 (CE.pair_member_table ord0 ord0) partition
  | 0%N, 1%N => nth 0 (CE.pair_member_table ord0 ord_max) partition
  | 1%N, 0%N => nth 0
      (CE.pair_member_table (@Ordinal 3 1 isT) ord0) partition
  | 1%N, 1%N => nth 0
      (CE.pair_member_table (@Ordinal 3 1 isT) ord_max) partition
  | 2%N, 0%N => nth 0 (CE.pair_member_table ord_max ord0) partition
  | 2%N, 1%N => nth 0 (CE.pair_member_table ord_max ord_max) partition
  | _, _ => 0%N
  end.

Definition triple_member_value (partition block slot : nat) : nat :=
  match block, slot with
  | 0%N, 0%N => nth 0 (CE.triple_member_table ord0 ord0) partition
  | 0%N, 1%N => nth 0
      (CE.triple_member_table ord0 (@Ordinal 3 1 isT)) partition
  | 0%N, 2%N => nth 0 (CE.triple_member_table ord0 ord_max) partition
  | 1%N, 0%N => nth 0 (CE.triple_member_table ord_max ord0) partition
  | 1%N, 1%N => nth 0
      (CE.triple_member_table ord_max (@Ordinal 3 1 isT)) partition
  | 1%N, 2%N => nth 0 (CE.triple_member_table ord_max ord_max) partition
  | _, _ => 0%N
  end.

Definition pair_inner_bit_value (digit slot : nat) : nat :=
  radix_digit 2 (digit - 1)%N slot.

Definition triple_inner_bit_value (digit slot : nat) : nat :=
  radix_digit 2 (digit - 1)%N slot.

Definition pair_block_coefficient_value
    (x0 x1 digit : nat) : int :=
  match digit with
  | 0%N => x0%:Z
  | S _ =>
      -1 *
      ((if pair_inner_bit_value digit 0 is 0%N then x1%:Z else -1) *
       (if pair_inner_bit_value digit 1 is 0%N then x1%:Z else -1))
  end.

Definition triple_block_coefficient_value
    (x0 x1 digit : nat) : int :=
  match digit with
  | 0%N => x0%:Z
  | S _ =>
      -1 *
      ((if triple_inner_bit_value digit 0 is 0%N then x1%:Z else -1) *
       ((if triple_inner_bit_value digit 1 is 0%N then x1%:Z else -1) *
        (if triple_inner_bit_value digit 2 is 0%N then x1%:Z else -1)))
  end.

Definition pair_selected_root_indicator_value
    (partition digit coordinate block slot : nat) : nat :=
  match digit with
  | 0%N => 0%N
  | S _ =>
      (pair_inner_bit_value digit slot *
       equal_indicator (pair_member_value partition block slot) coordinate)%N
  end.

Definition triple_selected_root_indicator_value
    (partition digit coordinate block slot : nat) : nat :=
  match digit with
  | 0%N => 0%N
  | S _ =>
      (triple_inner_bit_value digit slot *
       equal_indicator (triple_member_value partition block slot) coordinate)%N
  end.

Definition pair_block_exponent_value
    (partition digit coordinate block : nat) : nat :=
  (pair_selected_root_indicator_value partition digit coordinate block 0 +
   pair_selected_root_indicator_value partition digit coordinate block 1)%N.

Definition triple_block_exponent_value
    (partition digit coordinate block : nat) : nat :=
  (triple_selected_root_indicator_value partition digit coordinate block 0 +
   (triple_selected_root_indicator_value partition digit coordinate block 1 +
    triple_selected_root_indicator_value partition digit coordinate block 2))%N.

Definition pair_descriptor_coefficient_value
    (x0 x1 digit : nat) : int :=
  pair_block_coefficient_value x0 x1 (radix_digit 5 digit 0) *
  (pair_block_coefficient_value x0 x1 (radix_digit 5 digit 1) *
   pair_block_coefficient_value x0 x1 (radix_digit 5 digit 2)).

Definition triple_descriptor_coefficient_value
    (x0 x1 digit : nat) : int :=
  triple_block_coefficient_value x0 x1 (radix_digit 9 digit 0) *
  triple_block_coefficient_value x0 x1 (radix_digit 9 digit 1).

Definition pair_descriptor_exponent_value
    (partition digit coordinate : nat) : nat :=
  (pair_block_exponent_value partition (radix_digit 5 digit 0) coordinate 0 +
   (pair_block_exponent_value partition (radix_digit 5 digit 1) coordinate 1 +
    pair_block_exponent_value partition (radix_digit 5 digit 2)
      coordinate 2))%N.

Definition triple_descriptor_exponent_value
    (partition digit coordinate : nat) : nat :=
  (triple_block_exponent_value partition (radix_digit 9 digit 0)
      coordinate 0 +
   triple_block_exponent_value partition (radix_digit 9 digit 1)
      coordinate 1)%N.

Definition descriptor_sparse_term
    (coefficient_value : nat -> nat -> nat -> int)
    (exponent_value : nat -> nat -> nat -> nat)
    (x0 x1 partition digit : nat) : SP.sparse_term :=
  (coefficient_value x0 x1 digit,
   [tuple exponent_value partition digit (val coordinate)
     | coordinate < 6]).

Definition pair_descriptor_term partition digit x0 x1 : SP.sparse_term :=
  descriptor_sparse_term pair_descriptor_coefficient_value
    pair_descriptor_exponent_value x0 x1 partition digit.

Definition triple_descriptor_term partition digit x0 x1 : SP.sparse_term :=
  descriptor_sparse_term triple_descriptor_coefficient_value
    triple_descriptor_exponent_value x0 x1 partition digit.

Definition recursive_descriptor_coefficient_correct
    (builder : RE.recursive_descriptor_coefficient_builder)
    (coefficient_value : nat -> nat -> nat -> int) : Prop :=
  forall arity
    (term_index x0 x1 : SE.recursive_expression arity) values,
  CS.eval_mathcomp_recursive_signed_expression
      (builder arity term_index x0 x1) values =
  coefficient_value
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (SE.eval_recursive_expression term_index values).

Definition recursive_descriptor_exponent_correct
    (builder : RE.recursive_descriptor_exponent_builder)
    (exponent_value : nat -> nat -> nat -> nat) : Prop :=
  forall arity
    (partition term_index : SE.recursive_expression arity)
    coordinate values,
  SE.eval_recursive_expression
      (builder arity partition term_index coordinate) values =
  exponent_value
    (SE.eval_recursive_expression partition values)
    (SE.eval_recursive_expression term_index values) coordinate.

Lemma gcd_div_rem_mathcomp q p : p <> 0%N ->
  gcd.div q p = (q %/ p)%N /\ gcd.rem q p = (q %% p)%N.
Proof.
move=> hp.
refine (gcd.div_rem_uniq (p:=p)
  (gcd.div q p) (r1:=gcd.rem q p)
  (q %/ p)%N (r2:=(q %% p)%N) hp _ _ _).
- have hg := gcd.div_rem_spec1 q p.
  have hn := divn_eq q p.
  rewrite -hg.
  exact hn.
- exact: gcd.div_rem_spec2.
- have hp0 : (0 < p)%N by case: p hp=> // p _.
  have hmodb : (q %% p < p)%N by rewrite ltn_mod.
  have /ltP hmod := hmodb.
  exact hmod.
Qed.

Lemma nat_pow_expn base exponent :
  Nat.pow base exponent = (base ^ exponent)%N.
Proof.
induction exponent as [|exponent ih].
- reflexivity.
- simpl Nat.pow.
  rewrite expnS mulnE ih.
  reflexivity.
Qed.

Lemma eval_recursive_radix_digit {arity} radix position
    (expression : SE.recursive_expression arity) values :
  radix <> 0%N ->
  SE.eval_recursive_expression
      (SE.RecRemSucc
        (SE.RecDivSucc expression (Nat.pred (Nat.pow radix position)))
        (Nat.pred radix)) values =
  radix_digit radix (SE.eval_recursive_expression expression values) position.
Proof.
move=> hradix.
have hpow : Nat.pow radix position <> 0%N.
  exact: PeanoNat.Nat.pow_nonzero hradix.
have hspow : S (Nat.pred (Nat.pow radix position)) =
    Nat.pow radix position.
  exact: PeanoNat.Nat.succ_pred hpow.
have hsradix : S (Nat.pred radix) = radix.
  exact: PeanoNat.Nat.succ_pred hradix.
cbn [SE.eval_recursive_expression].
replace (S (Nat.pred (Nat.pow radix position))) with
    (Nat.pow radix position) by (symmetry; exact hspow).
replace (S (Nat.pred radix)) with radix by (symmetry; exact hsradix).
rewrite (gcd_div_rem_mathcomp _ hpow).1.
rewrite /radix_digit.
rewrite nat_pow_expn.
exact: (gcd_div_rem_mathcomp _ hradix).2.
Qed.

Lemma eval_pair_outer_digit {arity}
    (term_index : SE.recursive_expression arity) block values :
  SE.eval_recursive_expression (CE.pair_outer_digit term_index block) values =
  radix_digit 5 (SE.eval_recursive_expression term_index values) block.
Proof.
exact: (@eval_recursive_radix_digit arity 5 block term_index values
  ltac:(discriminate)).
Qed.

Lemma eval_triple_outer_digit {arity}
    (term_index : SE.recursive_expression arity) block values :
  SE.eval_recursive_expression (CE.triple_outer_digit term_index block) values =
  radix_digit 9 (SE.eval_recursive_expression term_index values) block.
Proof.
exact: (@eval_recursive_radix_digit arity 9 block term_index values
  ltac:(discriminate)).
Qed.

Lemma eval_pair_inner_bit {arity}
    (outer_digit : SE.recursive_expression arity) slot values :
  SE.eval_recursive_expression (CE.pair_inner_bit outer_digit slot) values =
  pair_inner_bit_value
    (SE.eval_recursive_expression outer_digit values) slot.
Proof.
rewrite /CE.pair_inner_bit /pair_inner_bit_value.
exact: (@eval_recursive_radix_digit arity 2 slot
  (SE.RecMinus outer_digit (SE.RecConst 1)) values
  ltac:(discriminate)).
Qed.

Lemma eval_triple_inner_bit {arity}
    (outer_digit : SE.recursive_expression arity) slot values :
  SE.eval_recursive_expression (CE.triple_inner_bit outer_digit slot) values =
  triple_inner_bit_value
    (SE.eval_recursive_expression outer_digit values) slot.
Proof.
rewrite /CE.triple_inner_bit /triple_inner_bit_value.
exact: (@eval_recursive_radix_digit arity 2 slot
  (SE.RecMinus outer_digit (SE.RecConst 1)) values
  ltac:(discriminate)).
Qed.

Lemma eval_recursive_equal_indicator {arity}
    (left right : SE.recursive_expression arity) values :
  SE.eval_recursive_expression
      (CE.recursive_equal_indicator left right) values =
  equal_indicator
    (SE.eval_recursive_expression left values)
    (SE.eval_recursive_expression right values).
Proof.
rewrite /CE.recursive_equal_indicator CS.eval_recursive_if_zero
  /CE.recursive_equal_distance /equal_indicator /=.
remember (SE.eval_recursive_expression left values) as l.
remember (SE.eval_recursive_expression right values) as r.
case heq: (Nat.eqb l r).
- move/PeanoNat.Nat.eqb_eq: heq=> ->.
  by rewrite subnn.
- move/PeanoNat.Nat.eqb_neq: heq=> hne.
  have hpositive : (l - r + (r - l))%nat <> 0%nat.
    rewrite !subnE !addnE.
    lia.
  case hsum: (l - r + (r - l))%nat=> [|sum].
  + by exfalso; apply hpositive.
  + reflexivity.
Qed.

Lemma pair_member_table_nth partition
    (hpartition : (partition < 15)%N) block slot :
  nth 0 (CE.pair_member_table block slot) partition =
  val (SR.pair_member (@Ordinal 15 partition hpartition) block slot).
Proof.
rewrite /CE.pair_member_table.
rewrite (nth_map ord0 0
  (fun p : SR.pair_partition => val (SR.pair_member p block slot))).
- have henum : nth ord0 (enum SR.pair_partition) partition =
      @Ordinal 15 partition hpartition.
    apply: val_inj.
    exact: (@nth_enum_ord 15 ord0 partition hpartition).
  by rewrite henum.
- by rewrite size_enum_ord.
Qed.

Lemma triple_member_table_nth partition
    (hpartition : (partition < 10)%N) block slot :
  nth 0 (CE.triple_member_table block slot) partition =
  val (SR.triple_member (@Ordinal 10 partition hpartition) block slot).
Proof.
rewrite /CE.triple_member_table.
rewrite (nth_map ord0 0
  (fun p : SR.triple_partition => val (SR.triple_member p block slot))).
- have henum : nth ord0 (enum SR.triple_partition) partition =
      @Ordinal 10 partition hpartition.
    apply: val_inj.
    exact: (@nth_enum_ord 10 ord0 partition hpartition).
  by rewrite henum.
- by rewrite size_enum_ord.
Qed.

Lemma eval_pair_block_coefficient_from {arity}
    (term_index x0 x1 : SE.recursive_expression arity) block values :
  CS.eval_mathcomp_recursive_signed_expression
      (CE.pair_block_coefficient_from term_index x0 x1 block) values =
  pair_block_coefficient_value
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (radix_digit 5 (SE.eval_recursive_expression term_index values) block).
Proof.
rewrite /CE.pair_block_coefficient_from.
rewrite CS.eval_mathcomp_recursive_signed_if_zero eval_pair_outer_digit.
case hdigit: (radix_digit 5
  (SE.eval_recursive_expression term_index values) block)=> [|digit].
- by rewrite CS.eval_mathcomp_recursive_signed_of_nat
    /pair_block_coefficient_value.
- rewrite CS.eval_mathcomp_recursive_signed_mult
    CS.eval_mathcomp_recursive_signed_negate
    CS.eval_mathcomp_recursive_signed_mult
    !CS.eval_mathcomp_recursive_signed_if_zero
    !eval_pair_inner_bit !eval_pair_outer_digit hdigit
    CS.eval_mathcomp_recursive_signed_of_nat.
  rewrite /pair_block_coefficient_value.
  reflexivity.
Qed.

Lemma eval_triple_block_coefficient_from {arity}
    (term_index x0 x1 : SE.recursive_expression arity) block values :
  CS.eval_mathcomp_recursive_signed_expression
      (CE.triple_block_coefficient_from term_index x0 x1 block) values =
  triple_block_coefficient_value
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (radix_digit 9 (SE.eval_recursive_expression term_index values) block).
Proof.
rewrite /CE.triple_block_coefficient_from.
rewrite CS.eval_mathcomp_recursive_signed_if_zero eval_triple_outer_digit.
case hdigit: (radix_digit 9
  (SE.eval_recursive_expression term_index values) block)=> [|digit].
- by rewrite CS.eval_mathcomp_recursive_signed_of_nat
    /triple_block_coefficient_value.
- rewrite !CS.eval_mathcomp_recursive_signed_mult
    CS.eval_mathcomp_recursive_signed_negate
    !CS.eval_mathcomp_recursive_signed_if_zero
    !eval_triple_inner_bit !eval_triple_outer_digit hdigit
    CS.eval_mathcomp_recursive_signed_of_nat.
  rewrite /triple_block_coefficient_value.
  reflexivity.
Qed.

Theorem pair_descriptor_coefficient_from_correct :
  recursive_descriptor_coefficient_correct
    (@CE.pair_descriptor_coefficient_from)
    pair_descriptor_coefficient_value.
Proof.
move=> arity term_index x0 x1 values.
rewrite /CE.pair_descriptor_coefficient_from
  !CS.eval_mathcomp_recursive_signed_mult
  !eval_pair_block_coefficient_from.
reflexivity.
Qed.

Theorem triple_descriptor_coefficient_from_correct :
  recursive_descriptor_coefficient_correct
    (@CE.triple_descriptor_coefficient_from)
    triple_descriptor_coefficient_value.
Proof.
move=> arity term_index x0 x1 values.
rewrite /CE.triple_descriptor_coefficient_from
  CS.eval_mathcomp_recursive_signed_mult
  !eval_triple_block_coefficient_from.
reflexivity.
Qed.

Lemma eval_recursive_plus {arity}
    (left right : SE.recursive_expression arity) values :
  SE.eval_recursive_expression (SE.RecPlus left right) values =
  (SE.eval_recursive_expression left values +
   SE.eval_recursive_expression right values)%N.
Proof. reflexivity. Qed.

Lemma eval_recursive_mult {arity}
    (left right : SE.recursive_expression arity) values :
  SE.eval_recursive_expression (SE.RecMult left right) values =
  (SE.eval_recursive_expression left values *
   SE.eval_recursive_expression right values)%N.
Proof. reflexivity. Qed.

Lemma eval_pair_selected_root_indicator_from {arity}
    (partition term_index : SE.recursive_expression arity)
    coordinate (block : 'I_3) (slot : 'I_2) values :
  SE.eval_recursive_expression
      (CE.pair_selected_root_indicator_from partition term_index
        coordinate block slot) values =
  match radix_digit 5 (SE.eval_recursive_expression term_index values)
      (val block) with
  | 0%N => 0%N
  | S _ =>
      (pair_inner_bit_value
          (radix_digit 5 (SE.eval_recursive_expression term_index values)
            (val block)) (val slot) *
       equal_indicator
         (nth 0 (CE.pair_member_table block slot)
           (SE.eval_recursive_expression partition values)) coordinate)%N
  end.
Proof.
rewrite /CE.pair_selected_root_indicator_from
  eval_recursive_mult CS.eval_recursive_if_zero.
rewrite eval_pair_outer_digit.
rewrite eval_recursive_mult eval_pair_inner_bit eval_pair_outer_digit.
rewrite eval_recursive_equal_indicator
  /CE.recursive_pair_member CS.eval_recursive_lookup_list /=.
case: (radix_digit 5
  (SE.eval_recursive_expression term_index values) (val block))=> [|digit].
- reflexivity.
- by rewrite mul1n.
Qed.

Lemma eval_triple_selected_root_indicator_from {arity}
    (partition term_index : SE.recursive_expression arity)
    coordinate (block : 'I_2) (slot : 'I_3) values :
  SE.eval_recursive_expression
      (CE.triple_selected_root_indicator_from partition term_index
        coordinate block slot) values =
  match radix_digit 9 (SE.eval_recursive_expression term_index values)
      (val block) with
  | 0%N => 0%N
  | S _ =>
      (triple_inner_bit_value
          (radix_digit 9 (SE.eval_recursive_expression term_index values)
            (val block)) (val slot) *
       equal_indicator
         (nth 0 (CE.triple_member_table block slot)
           (SE.eval_recursive_expression partition values)) coordinate)%N
  end.
Proof.
rewrite /CE.triple_selected_root_indicator_from
  eval_recursive_mult CS.eval_recursive_if_zero.
rewrite eval_triple_outer_digit.
rewrite eval_recursive_mult eval_triple_inner_bit eval_triple_outer_digit.
rewrite eval_recursive_equal_indicator
  /CE.recursive_triple_member CS.eval_recursive_lookup_list /=.
case: (radix_digit 9
  (SE.eval_recursive_expression term_index values) (val block))=> [|digit].
- reflexivity.
- by rewrite mul1n.
Qed.

Theorem pair_descriptor_exponent_from_correct :
  recursive_descriptor_exponent_correct
    (@CE.pair_descriptor_exponent_from)
    pair_descriptor_exponent_value.
Proof.
move=> arity partition term_index coordinate values.
rewrite /CE.pair_descriptor_exponent_from !eval_recursive_plus
  !eval_pair_selected_root_indicator_from.
rewrite /pair_descriptor_exponent_value /pair_block_exponent_value
  /pair_selected_root_indicator_value /pair_member_value /=.
rewrite !addnE !mulnE.
repeat rewrite Nat.add_assoc.
reflexivity.
Qed.

Theorem triple_descriptor_exponent_from_correct :
  recursive_descriptor_exponent_correct
    (@CE.triple_descriptor_exponent_from)
    triple_descriptor_exponent_value.
Proof.
move=> arity partition term_index coordinate values.
rewrite /CE.triple_descriptor_exponent_from !eval_recursive_plus
  !eval_triple_selected_root_indicator_from.
rewrite /triple_descriptor_exponent_value /triple_block_exponent_value
  /triple_selected_root_indicator_value /triple_member_value /=.
rewrite !addnE !mulnE.
repeat rewrite Nat.add_assoc.
reflexivity.
Qed.

Definition pair_block_descriptor_term
    (partition digit x0 x1 block : nat) : SP.sparse_term :=
  (pair_block_coefficient_value x0 x1 digit,
   [tuple pair_block_exponent_value partition digit
      (val coordinate) block | coordinate < 6]).

Definition triple_block_descriptor_term
    (partition digit x0 x1 block : nat) : SP.sparse_term :=
  (triple_block_coefficient_value x0 x1 digit,
   [tuple triple_block_exponent_value partition digit
      (val coordinate) block | coordinate < 6]).

Lemma pair_descriptor_term_product partition digit x0 x1 :
  pair_descriptor_term partition digit x0 x1 =
  SP.term_mul
    (pair_block_descriptor_term partition (radix_digit 5 digit 0)
      x0 x1 0)
    (SP.term_mul
      (pair_block_descriptor_term partition (radix_digit 5 digit 1)
        x0 x1 1)
      (pair_block_descriptor_term partition (radix_digit 5 digit 2)
        x0 x1 2)).
Proof.
rewrite /pair_descriptor_term /descriptor_sparse_term
  /pair_descriptor_coefficient_value /pair_descriptor_exponent_value
  /pair_block_descriptor_term /SP.term_mul /=.
congr (_, _).
apply: eq_from_tnth=> coordinate.
by rewrite !tnth_mktuple.
Qed.

Lemma triple_descriptor_term_product partition digit x0 x1 :
  triple_descriptor_term partition digit x0 x1 =
  SP.term_mul
    (triple_block_descriptor_term partition (radix_digit 9 digit 0)
      x0 x1 0)
    (triple_block_descriptor_term partition (radix_digit 9 digit 1)
      x0 x1 1).
Proof.
rewrite /triple_descriptor_term /descriptor_sparse_term
  /triple_descriptor_coefficient_value /triple_descriptor_exponent_value
  /triple_block_descriptor_term /SP.term_mul /=.
congr (_, _).
apply: eq_from_tnth=> coordinate.
by rewrite !tnth_mktuple.
Qed.

Definition encoded_choice_term
    (x1 root bit : nat) : SP.sparse_term :=
  (if bit is 0%N then x1%:Z else -1,
   [tuple (bit * equal_indicator root (val coordinate))%N
     | coordinate < 6]).

Definition pair_inner_encoded_term
    (partition block x1 code : nat) : SP.sparse_term :=
  SP.term_mul
    (encoded_choice_term x1 (pair_member_value partition block 0)
      (radix_digit 2 code 0))
    (encoded_choice_term x1 (pair_member_value partition block 1)
      (radix_digit 2 code 1)).

Definition triple_inner_encoded_term
    (partition block x1 code : nat) : SP.sparse_term :=
  SP.term_mul
    (encoded_choice_term x1 (triple_member_value partition block 0)
      (radix_digit 2 code 0))
    (SP.term_mul
      (encoded_choice_term x1 (triple_member_value partition block 1)
        (radix_digit 2 code 1))
      (encoded_choice_term x1 (triple_member_value partition block 2)
        (radix_digit 2 code 2))).

Lemma pair_block_descriptor_term0 partition x0 x1 block :
  pair_block_descriptor_term partition 0 x0 x1 block =
  (x0%:Z, SP.exponent_zero).
Proof.
rewrite /pair_block_descriptor_term /pair_block_coefficient_value
  /pair_block_exponent_value /pair_selected_root_indicator_value /=.
congr (_, _).
Qed.

Lemma triple_block_descriptor_term0 partition x0 x1 block :
  triple_block_descriptor_term partition 0 x0 x1 block =
  (x0%:Z, SP.exponent_zero).
Proof.
rewrite /triple_block_descriptor_term /triple_block_coefficient_value
  /triple_block_exponent_value /triple_selected_root_indicator_value /=.
congr (_, _).
Qed.

Lemma pair_inner_bit_valueS code slot :
  pair_inner_bit_value code.+1 slot = radix_digit 2 code slot.
Proof. by rewrite /pair_inner_bit_value subn1. Qed.

Lemma triple_inner_bit_valueS code slot :
  triple_inner_bit_value code.+1 slot = radix_digit 2 code slot.
Proof. by rewrite /triple_inner_bit_value subn1. Qed.

Lemma pair_block_descriptor_termS partition code x0 x1 block :
  pair_block_descriptor_term partition code.+1 x0 x1 block =
  SP.term_neg (pair_inner_encoded_term partition block x1 code).
Proof.
rewrite /pair_block_descriptor_term /pair_block_coefficient_value
  /pair_block_exponent_value /pair_selected_root_indicator_value
  /pair_inner_encoded_term /encoded_choice_term /SP.term_neg
  /SP.term_mul /=.
congr (_, _).
- rewrite !pair_inner_bit_valueS.
  finish_mathcomp_int_ring.
- apply: eq_from_tnth=> coordinate.
  by rewrite !pair_inner_bit_valueS SP.tnth_exponent_addE !tnth_mktuple.
Qed.

Lemma triple_block_descriptor_termS partition code x0 x1 block :
  triple_block_descriptor_term partition code.+1 x0 x1 block =
  SP.term_neg (triple_inner_encoded_term partition block x1 code).
Proof.
rewrite /triple_block_descriptor_term /triple_block_coefficient_value
  /triple_block_exponent_value /triple_selected_root_indicator_value
  /triple_inner_encoded_term /encoded_choice_term /SP.term_neg
  /SP.term_mul /=.
congr (_, _).
- rewrite !triple_inner_bit_valueS.
  finish_mathcomp_int_ring.
- apply: eq_from_tnth=> coordinate.
  by rewrite !triple_inner_bit_valueS
    !SP.tnth_exponent_addE !tnth_mktuple.
Qed.

Lemma exponent_add0_left exponent :
  SP.exponent_add SP.exponent_zero exponent = exponent.
Proof.
apply: eq_from_tnth=> coordinate.
by rewrite SP.tnth_exponent_addE SP.tnth_exponent_zeroE.
Qed.

Lemma exponent_add0_right exponent :
  SP.exponent_add exponent SP.exponent_zero = exponent.
Proof.
apply: eq_from_tnth=> coordinate.
rewrite SP.tnth_exponent_addE.
rewrite SP.tnth_exponent_zeroE.
exact: addn0.
Qed.

Lemma sparse_term_mul1_left term :
  SP.term_mul sparse_term_one term = term.
Proof.
case: term=> coefficient exponent.
by rewrite /SP.term_mul /sparse_term_one /= mul1r exponent_add0_left.
Qed.

Lemma sparse_term_mul1_right term :
  SP.term_mul term sparse_term_one = term.
Proof.
case: term=> coefficient exponent.
by rewrite /SP.term_mul /sparse_term_one /= mulr1 exponent_add0_right.
Qed.

Lemma cartesian_terms_sparse_product (factors : seq SP.sparse_polynomial) :
  MRX.cartesian_terms sparse_term_one SP.term_mul factors =
  SP.sparse_product factors.
Proof.
elim: factors=> [|factor factors ih] //=.
by rewrite ih /SP.sparse_mul.
Qed.

Section ObserverSemantics.

Variable R : comSemiRingType.

Lemma nat_sparse_const_observer_sum n
    (target : SP.sparse_term -> R) :
  \sum_(term <- SR.nat_sparse_const n) target term =
  target (n%:Z, SP.exponent_zero).
Proof.
by rewrite /SR.nat_sparse_const /SP.sparse_const big_seq1.
Qed.

Lemma sparse_sub_observer_sum p q
    (target : SP.sparse_term -> R) :
  \sum_(term <- SP.sparse_sub p q) target term =
  \sum_(term <- p) target term +
  \sum_(term <- q) target (SP.term_neg term).
Proof.
by rewrite /SP.sparse_sub /SP.sparse_add /SP.sparse_neg big_cat big_map.
Qed.

Lemma mixed_radix_observer_sparse_product
    (digit_term : nat -> nat -> SP.sparse_term)
    (factor_terms : nat -> SP.sparse_polynomial)
    (observe : SP.sparse_term -> R) b position count :
  (0 < b)%N ->
  (forall (i : nat) (target : SP.sparse_term -> R),
      \sum_(digit < b) target (digit_term i digit) =
      \sum_(term <- factor_terms i) target term) ->
  \sum_(code < b ^ count)
      observe
        (MRX.mixed_radix_term_from sparse_term_one SP.term_mul
          digit_term b position count code) =
  \sum_(term <- SP.sparse_product
      [seq factor_terms i | i <- iota position count]) observe term.
Proof.
move=> hb hfactor.
rewrite (@MRX.mixed_radix_cartesian_observer_sum
  SP.sparse_term R sparse_term_one SP.term_mul digit_term factor_terms
  observe b position count hb hfactor).
by rewrite cartesian_terms_sparse_product.
Qed.

Lemma equal_indicator_ordinal (left right : 'I_6) :
  equal_indicator (val left) (val right) =
  if right == left then 1%N else 0%N.
Proof.
rewrite /equal_indicator.
case hright: (right == left).
- move/eqP: hright=> ->.
  by rewrite PeanoNat.Nat.eqb_refl.
- have hneq : val left <> val right.
    move=> hval; move: hright.
    have -> : right = left by exact: esym (val_inj hval).
    by rewrite eqxx.
  have heqb : Nat.eqb (val left) (val right) = false.
    apply PeanoNat.Nat.eqb_neq.
    exact hneq.
  by rewrite heqb.
Qed.

Lemma encoded_choice_term0 x1 root :
  encoded_choice_term x1 root 0 = (x1%:Z, SP.exponent_zero).
Proof.
rewrite /encoded_choice_term /=.
congr (_, _).
Qed.

Lemma encoded_choice_term1 x1 (root : 'I_6) :
  encoded_choice_term x1 (val root) 1 =
  (-1, SP.exponent_single root).
Proof.
rewrite /encoded_choice_term /=.
congr (_, _).
apply: eq_from_tnth=> coordinate.
rewrite tnth_mktuple SP.tnth_exponent_singleE
  equal_indicator_ordinal.
by case: (coordinate == root).
Qed.

Lemma encoded_choice_observer_sum x1 (root : 'I_6)
    (target : SP.sparse_term -> R) :
  \sum_(bit < 2) target (encoded_choice_term x1 (val root) bit) =
  \sum_(term <-
      SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root))
    target term.
Proof.
rewrite !big_ord_recl !big_ord0 /=
  encoded_choice_term0 encoded_choice_term1.
rewrite /SP.sparse_sub /SP.sparse_add /SP.sparse_neg
  /SR.nat_sparse_const /SP.sparse_const /SP.sparse_var /=.
by rewrite !big_cons big_nil /SP.term_neg /=.
Qed.

Lemma radix_digit0 radix code :
  radix_digit radix code 0 = (code %% radix)%N.
Proof. by rewrite /radix_digit expn0 divn1. Qed.

Lemma radix_digitS radix code position :
  radix_digit radix code position.+1 =
  radix_digit radix (code %/ radix)%N position.
Proof.
by rewrite /radix_digit expnS divnMA.
Qed.

Definition pair_inner_encoded_term_from
    (x1 : nat) (root0 root1 : 'I_6) code : SP.sparse_term :=
  SP.term_mul
    (encoded_choice_term x1 (val root0) (radix_digit 2 code 0))
    (encoded_choice_term x1 (val root1) (radix_digit 2 code 1)).

Definition triple_inner_encoded_term_from
    (x1 : nat) (root0 root1 root2 : 'I_6) code : SP.sparse_term :=
  SP.term_mul
    (encoded_choice_term x1 (val root0) (radix_digit 2 code 0))
    (SP.term_mul
      (encoded_choice_term x1 (val root1) (radix_digit 2 code 1))
      (encoded_choice_term x1 (val root2) (radix_digit 2 code 2))).

Lemma pair_inner_encoded_term_from_mixed x1 root0 root1 code :
  pair_inner_encoded_term_from x1 root0 root1 code =
  MRX.mixed_radix_term_from sparse_term_one SP.term_mul
    (fun position bit =>
      encoded_choice_term x1
        (val (if position is 0%N then root0 else root1)) bit)
    2 0 2 code.
Proof.
rewrite /pair_inner_encoded_term_from /= sparse_term_mul1_right.
rewrite !radix_digit0 radix_digitS radix_digit0.
reflexivity.
Qed.

Lemma triple_inner_encoded_term_from_mixed x1 root0 root1 root2 code :
  triple_inner_encoded_term_from x1 root0 root1 root2 code =
  MRX.mixed_radix_term_from sparse_term_one SP.term_mul
    (fun position bit =>
      encoded_choice_term x1
        (val
          (match position with
           | 0%N => root0
           | 1%N => root1
           | _ => root2
           end)) bit)
    2 0 3 code.
Proof.
rewrite /triple_inner_encoded_term_from /= sparse_term_mul1_right.
rewrite !radix_digit0 !radix_digitS !radix_digit0.
reflexivity.
Qed.

Lemma pair_inner_encoded_observer_sum x1
    (root0 root1 : 'I_6) (observe : SP.sparse_term -> R) :
  \sum_(code < 4)
      observe (pair_inner_encoded_term_from x1 root0 root1 code) =
  \sum_(term <- SP.sparse_product
      [:: SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root0);
          SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root1)])
    observe term.
Proof.
under eq_bigr do rewrite pair_inner_encoded_term_from_mixed.
have hmixed := @mixed_radix_observer_sparse_product
  (fun position bit =>
    encoded_choice_term x1
      (val (if position is 0%N then root0 else root1)) bit)
  (fun position =>
    SP.sparse_sub (SR.nat_sparse_const x1)
      (SP.sparse_var (if position is 0%N then root0 else root1)))
  observe 2 0 2.
rewrite (hmixed isT) //.
- move=> position target.
  exact: encoded_choice_observer_sum.
Qed.

Lemma triple_inner_encoded_observer_sum x1
    (root0 root1 root2 : 'I_6) (observe : SP.sparse_term -> R) :
  \sum_(code < 8)
      observe (triple_inner_encoded_term_from x1 root0 root1 root2 code) =
  \sum_(term <- SP.sparse_product
      [:: SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root0);
          SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root1);
          SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root2)])
    observe term.
Proof.
under eq_bigr do rewrite triple_inner_encoded_term_from_mixed.
have hmixed := @mixed_radix_observer_sparse_product
  (fun position bit =>
    encoded_choice_term x1
      (val
        (match position with
         | 0%N => root0
         | 1%N => root1
         | _ => root2
         end)) bit)
  (fun position =>
    SP.sparse_sub (SR.nat_sparse_const x1)
      (SP.sparse_var
        (match position with
         | 0%N => root0
         | 1%N => root1
         | _ => root2
         end)))
  observe 2 0 3.
rewrite (hmixed isT) //.
- move=> position target.
  exact: encoded_choice_observer_sum.
Qed.

Lemma pair_inner_encoded_term_members partition block x1 code
    (root0 root1 : 'I_6) :
  pair_member_value partition block 0 = val root0 ->
  pair_member_value partition block 1 = val root1 ->
  pair_inner_encoded_term partition block x1 code =
  pair_inner_encoded_term_from x1 root0 root1 code.
Proof.
move=> hroot0 hroot1.
by rewrite /pair_inner_encoded_term /pair_inner_encoded_term_from
  hroot0 hroot1.
Qed.

Lemma triple_inner_encoded_term_members partition block x1 code
    (root0 root1 root2 : 'I_6) :
  triple_member_value partition block 0 = val root0 ->
  triple_member_value partition block 1 = val root1 ->
  triple_member_value partition block 2 = val root2 ->
  triple_inner_encoded_term partition block x1 code =
  triple_inner_encoded_term_from x1 root0 root1 root2 code.
Proof.
move=> hroot0 hroot1 hroot2.
by rewrite /triple_inner_encoded_term /triple_inner_encoded_term_from
  hroot0 hroot1 hroot2.
Qed.

Lemma pair_block_descriptor_observer_sum_from partition block x0 x1
    (root0 root1 : 'I_6) (observe : SP.sparse_term -> R) :
  pair_member_value partition block 0 = val root0 ->
  pair_member_value partition block 1 = val root1 ->
  \sum_(digit < 5)
      observe (pair_block_descriptor_term partition digit x0 x1 block) =
  \sum_(term <- SP.sparse_sub (SR.nat_sparse_const x0)
      (SP.sparse_product
        [:: SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root0);
            SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root1)]))
    observe term.
Proof.
move=> hroot0 hroot1.
rewrite big_ord_recl /= pair_block_descriptor_term0.
under eq_bigr do rewrite pair_block_descriptor_termS
  (pair_inner_encoded_term_members
    (partition := partition) (block := block)
    x1 _ (root0 := root0) (root1 := root1) hroot0 hroot1).
rewrite (pair_inner_encoded_observer_sum x1 root0 root1
  (fun term => observe (SP.term_neg term))).
rewrite sparse_sub_observer_sum nat_sparse_const_observer_sum.
reflexivity.
Qed.

Lemma triple_block_descriptor_observer_sum_from partition block x0 x1
    (root0 root1 root2 : 'I_6) (observe : SP.sparse_term -> R) :
  triple_member_value partition block 0 = val root0 ->
  triple_member_value partition block 1 = val root1 ->
  triple_member_value partition block 2 = val root2 ->
  \sum_(digit < 9)
      observe (triple_block_descriptor_term partition digit x0 x1 block) =
  \sum_(term <- SP.sparse_sub (SR.nat_sparse_const x0)
      (SP.sparse_product
        [:: SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root0);
            SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root1);
            SP.sparse_sub (SR.nat_sparse_const x1) (SP.sparse_var root2)]))
    observe term.
Proof.
move=> hroot0 hroot1 hroot2.
rewrite big_ord_recl /= triple_block_descriptor_term0.
under eq_bigr do rewrite triple_block_descriptor_termS
  (triple_inner_encoded_term_members
    (partition := partition) (block := block)
    x1 _ (root0 := root0) (root1 := root1) (root2 := root2)
    hroot0 hroot1 hroot2).
rewrite (triple_inner_encoded_observer_sum x1 root0 root1 root2
  (fun term => observe (SP.term_neg term))).
rewrite sparse_sub_observer_sum nat_sparse_const_observer_sum.
reflexivity.
Qed.

Lemma pair_block0_descriptor_observer_sum partition
    (hpartition : (partition < 15)%N) x0 x1
    (observe : SP.sparse_term -> R) :
  \sum_(digit < 5)
      observe (pair_block_descriptor_term partition digit x0 x1 0) =
  \sum_(term <- SP.sparse_sub (SR.nat_sparse_const x0)
      (SR.pair_sparse_block_value [tuple x0; x1]
        (@Ordinal 15 partition hpartition) ord0)) observe term.
Proof.
rewrite /SR.pair_sparse_block_value SRS.enum_ord2E /=.
apply: pair_block_descriptor_observer_sum_from.
- exact: pair_member_table_nth.
- exact: pair_member_table_nth.
Qed.

Lemma pair_block1_descriptor_observer_sum partition
    (hpartition : (partition < 15)%N) x0 x1
    (observe : SP.sparse_term -> R) :
  \sum_(digit < 5)
      observe (pair_block_descriptor_term partition digit x0 x1 1) =
  \sum_(term <- SP.sparse_sub (SR.nat_sparse_const x0)
      (SR.pair_sparse_block_value [tuple x0; x1]
        (@Ordinal 15 partition hpartition) (@Ordinal 3 1 isT)))
    observe term.
Proof.
rewrite /SR.pair_sparse_block_value SRS.enum_ord2E /=.
apply: pair_block_descriptor_observer_sum_from.
- exact: pair_member_table_nth.
- exact: pair_member_table_nth.
Qed.

Lemma pair_block2_descriptor_observer_sum partition
    (hpartition : (partition < 15)%N) x0 x1
    (observe : SP.sparse_term -> R) :
  \sum_(digit < 5)
      observe (pair_block_descriptor_term partition digit x0 x1 2) =
  \sum_(term <- SP.sparse_sub (SR.nat_sparse_const x0)
      (SR.pair_sparse_block_value [tuple x0; x1]
        (@Ordinal 15 partition hpartition) ord_max)) observe term.
Proof.
rewrite /SR.pair_sparse_block_value SRS.enum_ord2E /=.
apply: pair_block_descriptor_observer_sum_from.
- exact: pair_member_table_nth.
- exact: pair_member_table_nth.
Qed.

Lemma triple_block0_descriptor_observer_sum partition
    (hpartition : (partition < 10)%N) x0 x1
    (observe : SP.sparse_term -> R) :
  \sum_(digit < 9)
      observe (triple_block_descriptor_term partition digit x0 x1 0) =
  \sum_(term <- SP.sparse_sub (SR.nat_sparse_const x0)
      (SR.triple_sparse_block_value [tuple x0; x1]
        (@Ordinal 10 partition hpartition) ord0)) observe term.
Proof.
rewrite /SR.triple_sparse_block_value SRS.enum_ord3E /=.
apply: triple_block_descriptor_observer_sum_from.
- exact: triple_member_table_nth.
- exact: triple_member_table_nth.
- exact: triple_member_table_nth.
Qed.

Lemma triple_block1_descriptor_observer_sum partition
    (hpartition : (partition < 10)%N) x0 x1
    (observe : SP.sparse_term -> R) :
  \sum_(digit < 9)
      observe (triple_block_descriptor_term partition digit x0 x1 1) =
  \sum_(term <- SP.sparse_sub (SR.nat_sparse_const x0)
      (SR.triple_sparse_block_value [tuple x0; x1]
        (@Ordinal 10 partition hpartition) ord_max)) observe term.
Proof.
rewrite /SR.triple_sparse_block_value SRS.enum_ord3E /=.
apply: triple_block_descriptor_observer_sum_from.
- exact: triple_member_table_nth.
- exact: triple_member_table_nth.
- exact: triple_member_table_nth.
Qed.

Definition pair_block_term_at partition x0 x1 position digit :
    SP.sparse_term :=
  match position with
  | 0%N => pair_block_descriptor_term partition digit x0 x1 0
  | 1%N => pair_block_descriptor_term partition digit x0 x1 1
  | _ => pair_block_descriptor_term partition digit x0 x1 2
  end.

Definition triple_block_term_at partition x0 x1 position digit :
    SP.sparse_term :=
  match position with
  | 0%N => triple_block_descriptor_term partition digit x0 x1 0
  | _ => triple_block_descriptor_term partition digit x0 x1 1
  end.

Lemma pair_descriptor_term_mixed partition digit x0 x1 :
  pair_descriptor_term partition digit x0 x1 =
  MRX.mixed_radix_term_from sparse_term_one SP.term_mul
    (pair_block_term_at partition x0 x1) 5 0 3 digit.
Proof.
rewrite pair_descriptor_term_product /= sparse_term_mul1_right.
rewrite !radix_digit0 !radix_digitS !radix_digit0.
reflexivity.
Qed.

Lemma triple_descriptor_term_mixed partition digit x0 x1 :
  triple_descriptor_term partition digit x0 x1 =
  MRX.mixed_radix_term_from sparse_term_one SP.term_mul
    (triple_block_term_at partition x0 x1) 9 0 2 digit.
Proof.
rewrite triple_descriptor_term_product /= sparse_term_mul1_right.
rewrite !radix_digit0 radix_digitS radix_digit0.
reflexivity.
Qed.

Definition pair_outer_factor_at partition
    (hpartition : (partition < 15)%N) x0 x1 position :
    SP.sparse_polynomial :=
  match position with
  | 0%N =>
      SP.sparse_sub (SR.nat_sparse_const x0)
        (SR.pair_sparse_block_value [tuple x0; x1]
          (@Ordinal 15 partition hpartition) ord0)
  | 1%N =>
      SP.sparse_sub (SR.nat_sparse_const x0)
        (SR.pair_sparse_block_value [tuple x0; x1]
          (@Ordinal 15 partition hpartition) (@Ordinal 3 1 isT))
  | _ =>
      SP.sparse_sub (SR.nat_sparse_const x0)
        (SR.pair_sparse_block_value [tuple x0; x1]
          (@Ordinal 15 partition hpartition) ord_max)
  end.

Definition triple_outer_factor_at partition
    (hpartition : (partition < 10)%N) x0 x1 position :
    SP.sparse_polynomial :=
  match position with
  | 0%N =>
      SP.sparse_sub (SR.nat_sparse_const x0)
        (SR.triple_sparse_block_value [tuple x0; x1]
          (@Ordinal 10 partition hpartition) ord0)
  | _ =>
      SP.sparse_sub (SR.nat_sparse_const x0)
        (SR.triple_sparse_block_value [tuple x0; x1]
          (@Ordinal 10 partition hpartition) ord_max)
  end.

Theorem pair_descriptor_observer_sum partition
    (hpartition : (partition < 15)%N) x0 x1
    (observe : SP.sparse_term -> R) :
  \sum_(digit < 125)
      observe (pair_descriptor_term partition digit x0 x1) =
  \sum_(term <- SR.pair_sparse_descriptor_value [tuple x0; x1]
      (@Ordinal 15 partition hpartition)) observe term.
Proof.
have hfactor : forall (position : nat)
    (target : SP.sparse_term -> R),
    \sum_(digit < 5)
      target (pair_block_term_at partition x0 x1 position digit) =
    \sum_(term <-
      pair_outer_factor_at hpartition x0 x1 position) target term.
  move=> [|[|position]] target /=.
  - exact: pair_block0_descriptor_observer_sum.
  - exact: pair_block1_descriptor_observer_sum.
  - exact: pair_block2_descriptor_observer_sum.
under eq_bigr do rewrite pair_descriptor_term_mixed.
have hmixed := @mixed_radix_observer_sparse_product
  (pair_block_term_at partition x0 x1)
  (pair_outer_factor_at hpartition x0 x1) observe 5 0 3 isT hfactor.
rewrite hmixed.
rewrite /SR.pair_sparse_descriptor_value SRS.enum_ord3E /=.
reflexivity.
Qed.

Theorem triple_descriptor_observer_sum partition
    (hpartition : (partition < 10)%N) x0 x1
    (observe : SP.sparse_term -> R) :
  \sum_(digit < 81)
      observe (triple_descriptor_term partition digit x0 x1) =
  \sum_(term <- SR.triple_sparse_descriptor_value [tuple x0; x1]
      (@Ordinal 10 partition hpartition)) observe term.
Proof.
have hfactor : forall (position : nat)
    (target : SP.sparse_term -> R),
    \sum_(digit < 9)
      target (triple_block_term_at partition x0 x1 position digit) =
    \sum_(term <-
      triple_outer_factor_at hpartition x0 x1 position) target term.
  move=> [|position] target /=.
  - exact: triple_block0_descriptor_observer_sum.
  - exact: triple_block1_descriptor_observer_sum.
under eq_bigr do rewrite triple_descriptor_term_mixed.
have hmixed := @mixed_radix_observer_sparse_product
  (triple_block_term_at partition x0 x1)
  (triple_outer_factor_at hpartition x0 x1) observe 9 0 2 isT hfactor.
rewrite hmixed.
rewrite /SR.triple_sparse_descriptor_value SRS.enum_ord2E /=.
reflexivity.
Qed.

End ObserverSemantics.

End PolynomialFormulasSexticMuRecDescriptorSemantics.
