(** The arithmetic fact used by the alternative NEG compilation.
    This is a kernel-checked arithmetic lemma, not a binary-TM endpoint. *)
From Stdlib Require Import Arith.PeanoNat Lia.

Fixpoint tri (n : nat) : nat :=
  match n with 0 => 0 | S k => S k + tri k end.
Definition P (a b : nat) : nat := tri (a+b)+b.

Theorem pair_false_operand a : P a 1 = P 0 a + 2.
Proof.
  unfold P. replace (a+1) with (S a) by lia.
  change (S a + tri a + 1 = tri a + a + 2). lia.
Qed.

Record neg_registers := mkNeg { top : nat; scratch1 : nat; scratch2 : nat }.
Definition pair_spec (m : neg_registers) : neg_registers :=
  mkNeg 0 0 (scratch2 m + P (scratch1 m) (top m)).
Definition inc7_spec (m : neg_registers) : neg_registers :=
  mkNeg (top m) (scratch1 m) (S (scratch2 m)).
Definition times4_spec (m : neg_registers) : neg_registers :=
  mkNeg (top m + 4 * scratch2 m) (scratch1 m) 0.

Theorem pair_add2_negation a :
  times4_spec (inc7_spec (inc7_spec (pair_spec (mkNeg a 0 0))))
    = mkNeg (4 * P a 1) 0 0.
Proof.
  unfold times4_spec, inc7_spec, pair_spec. cbn [top scratch1 scratch2].
  rewrite pair_false_operand. f_equal. lia.
Qed.

Print Assumptions pair_false_operand.
Print Assumptions pair_add2_negation.
