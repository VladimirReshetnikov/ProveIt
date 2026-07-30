(** Natural-number codes for finite vectors of naturals. *)

From Stdlib Require Import Arith.Cantor Lia Logic.FunctionalExtensionality.
From Foundation.Vorspiel Require Import Denumerable Matrix.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint nat_to_matrix_vec (code arity : nat) :
    option (Fin.t arity -> nat) :=
  match code, arity with
  | 0, 0 => Some matrix_vec_empty
  | S payload, S n =>
      let '(head, tail_code) := Cantor.of_nat payload in
      option_map (matrix_vec_cons head) (nat_to_matrix_vec tail_code n)
  | _, _ => None
  end.

Theorem nat_to_matrix_vec_encode : forall n (v : Fin.t n -> nat),
  nat_to_matrix_vec (matrix_vec_to_nat v) n = Some v.
Proof.
  induction n as [|n IH]; intro v.
  - cbn [matrix_vec_to_nat matrix_vec_foldr nat_to_matrix_vec].
    f_equal. apply functional_extensionality. intro i. inversion i.
  - cbn [matrix_vec_to_nat matrix_vec_foldr nat_to_matrix_vec].
    rewrite Cantor.cancel_of_to. simpl. rewrite IH.
    simpl. f_equal. apply matrix_vec_eta.
Qed.

Theorem nat_to_matrix_vec_member_lt : forall n code
    (v : Fin.t n -> nat),
  nat_to_matrix_vec code n = Some v ->
  forall i, v i < code.
Proof.
  induction n as [|n IH]; intros code v Hdecode i.
  - inversion i.
  - destruct code as [|payload]; [discriminate |].
    cbn [nat_to_matrix_vec] in Hdecode.
    destruct (Cantor.of_nat payload) as [head tail_code] eqn:Hpair.
    destruct (nat_to_matrix_vec tail_code n) as [tail|] eqn:Htail;
      simpl in Hdecode; [inversion Hdecode; subst v | discriminate].
    pose proof (cantor_of_nat_components_le payload) as Hbounds.
    rewrite Hpair in Hbounds. simpl in Hbounds.
    refine (@Fin.caseS' n i (fun j =>
      matrix_vec_cons head tail j < S payload) _ _).
    + simpl. lia.
    + intro j. simpl. specialize (IH tail_code tail Htail j). lia.
Qed.
