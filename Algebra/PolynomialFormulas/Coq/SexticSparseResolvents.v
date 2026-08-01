From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import SexticSparsePolynomials.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Fully executable sparse pair/triple block-system resolvents.  The tables
    enumerate the fifteen partitions into three pairs and the ten partitions
    into two triples.  A partition is represented by its six block labels. *)
Module PolynomialFormulasSexticSparseResolvents.

Import PolynomialFormulasSexticSparsePolynomials.

Definition parameter := 2.-tuple nat.
Definition pair_partition := 'I_15.
Definition triple_partition := 'I_10.

Definition pair_label_table : seq (6.-tuple nat) := [::
  [tuple 0; 0; 1; 1; 2; 2];
  [tuple 0; 0; 1; 2; 1; 2];
  [tuple 0; 0; 1; 2; 2; 1];
  [tuple 0; 1; 0; 1; 2; 2];
  [tuple 0; 1; 0; 2; 1; 2];
  [tuple 0; 1; 0; 2; 2; 1];
  [tuple 0; 1; 1; 0; 2; 2];
  [tuple 0; 1; 2; 0; 1; 2];
  [tuple 0; 1; 2; 0; 2; 1];
  [tuple 0; 1; 1; 2; 0; 2];
  [tuple 0; 1; 2; 1; 0; 2];
  [tuple 0; 1; 2; 2; 0; 1];
  [tuple 0; 1; 1; 2; 2; 0];
  [tuple 0; 1; 2; 1; 2; 0];
  [tuple 0; 1; 2; 2; 1; 0]
].

Definition triple_label_table : seq (6.-tuple nat) := [::
  [tuple 0; 0; 0; 1; 1; 1];
  [tuple 0; 0; 1; 0; 1; 1];
  [tuple 0; 0; 1; 1; 0; 1];
  [tuple 0; 0; 1; 1; 1; 0];
  [tuple 0; 1; 0; 0; 1; 1];
  [tuple 0; 1; 0; 1; 0; 1];
  [tuple 0; 1; 0; 1; 1; 0];
  [tuple 0; 1; 1; 0; 0; 1];
  [tuple 0; 1; 1; 0; 1; 0];
  [tuple 0; 1; 1; 1; 0; 0]
].

Definition pair_label (p : pair_partition) : 6.-tuple nat :=
  nth [tuple 0; 0; 1; 1; 2; 2] pair_label_table p.

Definition triple_label (p : triple_partition) : 6.-tuple nat :=
  nth [tuple 0; 0; 0; 1; 1; 1] triple_label_table p.

Definition label_fiber (label : 6.-tuple nat) (b : nat) : seq 'I_6 :=
  [seq i <- enum 'I_6 | tnth label i == b].

Definition pair_member (p : pair_partition) (b : 'I_3) (s : 'I_2) : 'I_6 :=
  nth ord0 (label_fiber (pair_label p) b) s.

Definition triple_member
    (p : triple_partition) (b : 'I_2) (s : 'I_3) : 'I_6 :=
  nth ord0 (label_fiber (triple_label p) b) s.

Definition nat_sparse_const (n : nat) : sparse_polynomial :=
  sparse_const n%:Z.

Definition pair_sparse_block_value
    (x : parameter) (p : pair_partition) (b : 'I_3) : sparse_polynomial :=
  sparse_product
    [seq sparse_sub (nat_sparse_const (tnth x ord_max))
         (sparse_var (pair_member p b s)) | s <- enum 'I_2].

Definition triple_sparse_block_value
    (x : parameter) (p : triple_partition) (b : 'I_2) : sparse_polynomial :=
  sparse_product
    [seq sparse_sub (nat_sparse_const (tnth x ord_max))
         (sparse_var (triple_member p b s)) | s <- enum 'I_3].

Definition pair_sparse_descriptor_value
    (x : parameter) (p : pair_partition) : sparse_polynomial :=
  sparse_product
    [seq sparse_sub (nat_sparse_const (tnth x ord0))
         (pair_sparse_block_value x p b) | b <- enum 'I_3].

Definition triple_sparse_descriptor_value
    (x : parameter) (p : triple_partition) : sparse_polynomial :=
  sparse_product
    [seq sparse_sub (nat_sparse_const (tnth x ord0))
         (triple_sparse_block_value x p b) | b <- enum 'I_2].

(** Ascending coefficient lists for univariate polynomials whose coefficients
    are sparse polynomials in the six root variables. *)
Definition coefficient_list := seq sparse_polynomial.

Fixpoint coefficient_add (p q : coefficient_list) : coefficient_list :=
  match p, q with
  | [::], _ => q
  | _, [::] => p
  | a :: p', b :: q' => sparse_add a b :: coefficient_add p' q'
  end.

Definition coefficient_scale
    (a : sparse_polynomial) (p : coefficient_list) : coefficient_list :=
  map (sparse_mul a) p.

Definition coefficient_shift (p : coefficient_list) : coefficient_list :=
  sparse_zero :: p.

Fixpoint linear_product (roots : seq sparse_polynomial) : coefficient_list :=
  if roots is r :: roots' then
    coefficient_add
      (coefficient_scale (sparse_neg r) (linear_product roots'))
      (coefficient_shift (linear_product roots'))
  else [:: sparse_const 1].

Definition pair_sparse_resolvent (x : parameter) : coefficient_list :=
  linear_product
    [seq pair_sparse_descriptor_value x p | p <- enum pair_partition].

Definition triple_sparse_resolvent (x : parameter) : coefficient_list :=
  linear_product
    [seq triple_sparse_descriptor_value x p | p <- enum triple_partition].

Definition pair_sparse_resolvent_coefficient
    (x : parameter) (i : 'I_16) : sparse_polynomial :=
  nth sparse_zero (pair_sparse_resolvent x) i.

Definition triple_sparse_resolvent_coefficient
    (x : parameter) (i : 'I_11) : sparse_polynomial :=
  nth sparse_zero (triple_sparse_resolvent x) i.

Lemma size_pair_label_table : size pair_label_table = 15%N.
Proof. by []. Qed.

Lemma size_triple_label_table : size triple_label_table = 10%N.
Proof. by []. Qed.

Lemma size_coefficient_add_right p q :
  (size p <= size q)%N -> size (coefficient_add p q) = size q.
Proof.
elim: p q => [|a p ih] [|b q] //=.
by move=> hpq; rewrite ih.
Qed.

Lemma size_linear_product roots : size (linear_product roots) = (size roots).+1.
Proof.
elim: roots => [|r roots ih] //=.
rewrite size_coefficient_add_right.
- by rewrite /coefficient_shift /= ih.
- by rewrite /coefficient_scale /coefficient_shift size_map.
Qed.

Lemma size_pair_sparse_resolvent x : size (pair_sparse_resolvent x) = 16%N.
Proof. by rewrite /pair_sparse_resolvent size_linear_product size_map size_enum_ord. Qed.

Lemma size_triple_sparse_resolvent x :
  size (triple_sparse_resolvent x) = 11%N.
Proof. by rewrite /triple_sparse_resolvent size_linear_product size_map size_enum_ord. Qed.

(** Horner evaluation of an ascending sparse coefficient list. *)
Fixpoint coefficient_list_eval (values : 6.-tuple int) (y : int)
    (p : coefficient_list) : int :=
  if p is a :: p' then
    sparse_eval values a + y * coefficient_list_eval values y p'
  else 0.

Lemma coefficient_list_eval_add values y p q :
  coefficient_list_eval values y (coefficient_add p q) =
    coefficient_list_eval values y p + coefficient_list_eval values y q.
Proof.
elim: p q => [|a p ih] [|b q] //=.
- by rewrite add0r.
- by rewrite addr0.
- by rewrite sparse_eval_add ih mulrDr addrACA.
Qed.

Lemma coefficient_list_eval_scale values y a p :
  coefficient_list_eval values y (coefficient_scale a p) =
    sparse_eval values a * coefficient_list_eval values y p.
Proof.
elim: p => [|b p ih] /=.
- by rewrite mulr0.
- by rewrite sparse_eval_mul ih mulrDr mulrCA.
Qed.

Lemma coefficient_list_eval_shift values y p :
  coefficient_list_eval values y (coefficient_shift p) =
    y * coefficient_list_eval values y p.
Proof. by rewrite /coefficient_shift /= sparse_eval_zero add0r. Qed.

Lemma coefficient_list_eval_linear_product values y roots :
  coefficient_list_eval values y (linear_product roots) =
    \prod_(r <- roots) (y - sparse_eval values r).
Proof.
elim: roots => [|r roots ih] /=.
- rewrite sparse_eval_const big_nil.
  by rewrite mulr0 addr0.
- rewrite coefficient_list_eval_add coefficient_list_eval_scale
    coefficient_list_eval_shift sparse_eval_neg ih big_cons.
  by rewrite mulrBl mulNr addrC.
Qed.

Lemma coefficient_list_eval_pair_resolvent values y x :
  coefficient_list_eval values y (pair_sparse_resolvent x) =
    \prod_(p : pair_partition)
      (y - sparse_eval values (pair_sparse_descriptor_value x p)).
Proof.
rewrite /pair_sparse_resolvent coefficient_list_eval_linear_product
  big_map big_enum.
by apply: eq_bigr => p _.
Qed.

Lemma coefficient_list_eval_triple_resolvent values y x :
  coefficient_list_eval values y (triple_sparse_resolvent x) =
    \prod_(p : triple_partition)
      (y - sparse_eval values (triple_sparse_descriptor_value x p)).
Proof.
rewrite /triple_sparse_resolvent coefficient_list_eval_linear_product
  big_map big_enum.
by apply: eq_bigr => p _.
Qed.

Lemma sparse_eval_pair_block_value values x p b :
  sparse_eval values (pair_sparse_block_value x p b) =
    \prod_(s : 'I_2)
      ((tnth x ord_max)%:Z - tnth values (pair_member p b s)).
Proof.
rewrite /pair_sparse_block_value sparse_eval_product big_map big_enum.
apply: eq_bigr => s _.
by rewrite sparse_eval_sub /nat_sparse_const sparse_eval_const sparse_eval_var.
Qed.

Lemma sparse_eval_triple_block_value values x p b :
  sparse_eval values (triple_sparse_block_value x p b) =
    \prod_(s : 'I_3)
      ((tnth x ord_max)%:Z - tnth values (triple_member p b s)).
Proof.
rewrite /triple_sparse_block_value sparse_eval_product big_map big_enum.
apply: eq_bigr => s _.
by rewrite sparse_eval_sub /nat_sparse_const sparse_eval_const sparse_eval_var.
Qed.

Lemma sparse_eval_pair_descriptor_value values x p :
  sparse_eval values (pair_sparse_descriptor_value x p) =
    \prod_(b : 'I_3)
      ((tnth x ord0)%:Z -
        \prod_(s : 'I_2)
          ((tnth x ord_max)%:Z - tnth values (pair_member p b s))).
Proof.
rewrite /pair_sparse_descriptor_value sparse_eval_product big_map big_enum.
apply: eq_bigr => b _.
by rewrite sparse_eval_sub /nat_sparse_const sparse_eval_const
  sparse_eval_pair_block_value.
Qed.

Lemma sparse_eval_triple_descriptor_value values x p :
  sparse_eval values (triple_sparse_descriptor_value x p) =
    \prod_(b : 'I_2)
      ((tnth x ord0)%:Z -
        \prod_(s : 'I_3)
          ((tnth x ord_max)%:Z - tnth values (triple_member p b s))).
Proof.
rewrite /triple_sparse_descriptor_value sparse_eval_product big_map big_enum.
apply: eq_bigr => b _.
by rewrite sparse_eval_sub /nat_sparse_const sparse_eval_const
  sparse_eval_triple_block_value.
Qed.

End PolynomialFormulasSexticSparseResolvents.
