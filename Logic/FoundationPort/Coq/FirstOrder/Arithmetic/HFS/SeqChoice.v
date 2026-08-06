(** Finite relation-valued sequence choice in the standard HFS model.

    Foundation's [sigmaOne_skolem_seq] theorem constructs an internally
    definable sequence in an arbitrary nonstandard arithmetic model.  The
    finite standard-model content is independent of that coding layer: a
    witness for each index can be selected, and the existing vector-to-HFS
    sequence codec stores those witnesses with exact length and membership
    laws. *)

From Stdlib Require Import Logic.ClassicalEpsilon Arith.PeanoNat Lia
  Lists.List NArith.NArith Vectors.Fin.
From Foundation.Vorspiel.Fin Require Import Basic.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Seq.

Set Implicit Arguments.
Unset Strict Implicit.

(** Select one HFS value for every index in a finite range. *)
Definition hfs_relation_choice_vector (n : nat)
    (R : nat -> hfs_code -> Prop)
    (H : forall i, i < n -> exists y, R i y) : Fin.t n -> hfs_code :=
  fun i => proj1_sig
    (@constructive_indefinite_description hfs_code
      (R (vorspiel_fin_value i))
      (H (vorspiel_fin_value i) (proj2_sig (Fin.to_nat i)))).

Lemma hfs_relation_choice_vector_spec : forall (n : nat)
    (R : nat -> hfs_code -> Prop)
    (H : forall i, i < n -> exists y, R i y) (i : Fin.t n),
  R (vorspiel_fin_value i) (@hfs_relation_choice_vector n R H i).
Proof.
  intros n R H i. unfold hfs_relation_choice_vector.
  exact (proj2_sig
    (@constructive_indefinite_description hfs_code
      (R (vorspiel_fin_value i))
      (H (vorspiel_fin_value i) (proj2_sig (Fin.to_nat i))))).
Qed.

(** Every finite pointwise-witnessed relation has a sequence presentation.
    The final membership clause has no explicit [i < n] premise: membership
    in the exact-length sequence supplies that bound. *)
Theorem hfs_sequence_exists_for_relation : forall n
    (R : nat -> hfs_code -> Prop),
  (forall i, i < n -> exists y, R i y) ->
  exists s,
    hfs_sequence_length s = n /\
    forall i x,
      hfs_mem (hfs_index_pair (N.of_nat i) x)
        (hfs_sequence_code s) ->
      R i x.
Proof.
  intros n R H.
  set (v := @hfs_relation_choice_vector n R H).
  exists (hfs_vector_to_sequence v). split.
  - apply hfs_vector_to_sequence_length.
  - intros i x Hmem.
    unfold hfs_sequence_code in Hmem.
    change (hfs_mem (hfs_index_pair (N.of_nat i) x)
      (hfs_sequence_code_list (map v (vorspiel_fin_enum n)))) in Hmem.
    rewrite hfs_mem_sequence_index_iff in Hmem.
    destruct (Nat.lt_ge_cases i n) as [Hi | Hni].
    + set (j := Fin.of_nat_lt Hi).
      assert (Hji : vorspiel_fin_value j = i).
      { unfold j, vorspiel_fin_value.
        now rewrite Fin.to_nat_of_nat. }
      rewrite <- Hji in Hmem.
      rewrite nth_error_map, vorspiel_fin_enum_nth_error in Hmem.
      inversion Hmem; subst x.
      rewrite <- Hji.
      apply hfs_relation_choice_vector_spec.
    + assert (Hnone : nth_error (map v (vorspiel_fin_enum n)) i = None).
      { apply (proj2 (@nth_error_None hfs_code
          (map v (vorspiel_fin_enum n)) i)).
        rewrite length_map, vorspiel_fin_enum_length. lia. }
      rewrite Hnone in Hmem. discriminate.
Qed.

Print Assumptions hfs_sequence_exists_for_relation.
