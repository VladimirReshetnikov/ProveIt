(** State relabeling for binary BusyCoq machines.

    Extracted from the byte-identical transport block in eight maintained
    Dense*.v variants.  No inverse, injectivity or surjectivity of the state
    map is needed.  A total transition identity suffices, including terminal
    configurations.  The theorem holds on every input tape.
*)
From Coq Require Import Lists.Streams.
From BusyCoq Require Import TM.

(** Accept the caller's existing semantic modules.  Instantiating [TM.TM]
    again would create fresh inductive relations in Rocq's module system. *)
Module Type Semantics (C : Ctx).
  Include TM.TM C.
End Semantics.

Module StateRelabel
    (Source Target : Ctx with Definition Sym := bool)
    (Dense : Semantics Source) (Sparse : Semantics Target).

Section Transport.
Variable dense_tm : Dense.TM.
Variable tm : Sparse.TM.
Variable decode_state : Source.Q -> Target.Q.

Definition bool_tape := (Stream bool * bool * Stream bool)%type.
Definition decode_conf (c : Source.Q * bool_tape) : Target.Q * bool_tape :=
  let '(q,t) := c in (decode_state q,t).

Hypothesis transition_commutes : forall q b,
  tm (decode_state q,b) =
  match dense_tm (q,b) with
  | None => None
  | Some (w,d,q') => Some (w,d,decode_state q')
  end.

Lemma step_transport c c' :
  Dense.step dense_tm c c' ->
  Sparse.step tm (decode_conf c) (decode_conf c').
Proof.
  intros H. destruct H as [q q' s s' l r E | q q' s s' l r E].
  - apply Sparse.step_left. rewrite transition_commutes.
    exact (f_equal (fun a => match a with None => None | Some (w,d,z) => Some (w,d,decode_state z) end) E).
  - apply Sparse.step_right. rewrite transition_commutes.
    exact (f_equal (fun a => match a with None => None | Some (w,d,z) => Some (w,d,decode_state z) end) E).
Qed.

Lemma halted_transport c :
  Dense.halted dense_tm c -> Sparse.halted tm (decode_conf c).
Proof.
  destruct c as [q [[l b] r]].
  change (dense_tm (q,b) = None -> tm (decode_state q,b) = None).
  rewrite transition_commutes. intros E.
  exact (f_equal (fun a => match a with None => None | Some (w,d,z) => Some (w,d,decode_state z) end) E).
Qed.

Lemma multistep_transport n c c' :
  Dense.multistep dense_tm n c c' ->
  Sparse.multistep tm n (decode_conf c) (decode_conf c').
Proof.
  intros H. induction H.
  - constructor.
  - eapply Sparse.multistep_S; [apply step_transport; exact H | exact IHmultistep].
Qed.

Lemma preserves_halts c :
  Dense.halts dense_tm c -> Sparse.halts tm (decode_conf c).
Proof.
  intros (n & d & Hr & Hh). exists n, (decode_conf d). split.
  - apply multistep_transport, Hr.
  - apply halted_transport, Hh.
Qed.

Lemma dense_next c :
  Dense.halted dense_tm c \/ exists c', Dense.step dense_tm c c'.
Proof.
  destruct c as [q [[l b] r]].
  destruct (dense_tm (q,b)) as [[[w d] q']|] eqn:E.
  - right. destruct d.
    + eexists. eapply Dense.step_left. exact E.
    + eexists. eapply Dense.step_right. exact E.
  - left. exact E.
Qed.

Lemma reflects_halts initial :
  Sparse.halts tm (decode_conf initial) -> Dense.halts dense_tm initial.
Proof.
  intros HH.
  set (P := fun c : Target.Q * bool_tape =>
      exists d, c = decode_conf d /\ Dense.evstep dense_tm initial d).
  destruct (Sparse.progress_halts tm P
      (fun _ => Dense.halts dense_tm initial) (decode_conf initial)) as (c & _ & HZ).
  - intros c [d [-> Hr]].
    destruct (dense_next d) as [Hh | (d' & Hs)].
    + left. exact (Dense.halted_evstep_halts dense_tm initial d Hr Hh).
    + right. exists (decode_conf d'). split.
      * exists d'. split; [reflexivity|].
        eapply Dense.evstep_trans; [exact Hr|].
        eapply Dense.evstep_step; [exact Hs|constructor].
      * apply Sparse.progress_base. apply step_transport, Hs.
  - exists initial. split; [reflexivity|constructor].
  - exact HH.
  - exact HZ.
Qed.

Theorem halts_iff c :
  Dense.halts dense_tm c <-> Sparse.halts tm (decode_conf c).
Proof. split; [apply preserves_halts | apply reflects_halts]. Qed.

End Transport.
End StateRelabel.
