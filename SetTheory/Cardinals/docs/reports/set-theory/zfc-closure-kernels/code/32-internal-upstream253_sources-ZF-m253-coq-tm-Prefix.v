(** Finite normal prefixes preserve and reflect register-machine halting.
    This lemma uses the accepted RM definitions, with no well-formedness
    assumption and no additional logical axiom. *)
From Coq Require Import Lists.List.
From M254 Require Import RM RMEquiv.

Lemma at_halt_step_none p c : at_halt p c -> rm_step p c = None.
Proof.
  destruct c as [P Rg]. intros [d H].
  unfold rm_step. simpl in H. rewrite H. reflexivity.
Qed.

Lemma rm_halts_step p c c' :
  rm_step p c = Some c' -> (rm_halts p c <-> rm_halts p c').
Proof.
  intros E. split.
  - intros ([|n] & z & Hr & Ha).
    + simpl in Hr. injection Hr as <-.
      pose proof (at_halt_step_none p c Ha). congruence.
    + cbn [rm_run] in Hr. rewrite E in Hr.
      exists n, z. split; assumption.
  - intros (n & z & Hr & Ha). exists (S n), z. split.
    + cbn [rm_run]. rewrite E. exact Hr.
    + exact Ha.
Qed.

Theorem rm_halts_prefix p n : forall c c',
  rm_run p n c = Some c' -> (rm_halts p c <-> rm_halts p c').
Proof.
  induction n as [|n IH]; intros c c' Hr.
  - simpl in Hr. injection Hr as <-. reflexivity.
  - cbn [rm_run] in Hr.
    destruct (rm_step p c) as [z|] eqn:E; [|discriminate].
    eapply iff_trans; [apply rm_halts_step, E | apply IH, Hr].
Qed.

Print Assumptions at_halt_step_none.
Print Assumptions rm_halts_step.
Print Assumptions rm_halts_prefix.
