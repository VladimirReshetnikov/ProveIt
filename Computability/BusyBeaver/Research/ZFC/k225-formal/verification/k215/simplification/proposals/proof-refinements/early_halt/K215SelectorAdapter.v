(** Exact production-command adapter. This source is checked against the
    pinned K215F compiler layer and included inherited code dependencies.
    It does not rebuild the full binary-machine/ZFC endpoint. *)
From Coq Require Import List.
From K230L Require Import Codes230.
From K215F Require Import Codes222 EnumPerm L1_CompPerm.
Require Import EarlyHaltSelection NativeSelection.
Import ListNotations.

Definition selector_cmd (k : EarlyHaltSelection.cmd) : L1_CompPerm.cmd :=
  match k with NIP => CNIP | DROP => CDROP end.

Lemma selector_step_bridge k q :
  L1_CompPerm.xstep (selector_cmd k) q = NativeSelection.xstep P unP k q.
Proof. destruct k; destruct q as [[[t w] d] h]; reflexivity. Qed.

Lemma selector_exec_bridge L q :
  L1_CompPerm.exec (map selector_cmd L) q = NativeSelection.exec P unP L q.
Proof.
  revert q; induction L as [|k rest IH]; intro q; [reflexivity|].
  cbn [map L1_CompPerm.exec NativeSelection.exec].
  rewrite selector_step_bridge.
  destruct (NativeSelection.xstep P unP k q); [apply IH|reflexivity].
Qed.

Definition SELECT (j n : nat) : list L1_CompPerm.cmd :=
  map selector_cmd (repeat NIP (j + 1) ++ DROP :: repeat NIP (n + 1 - j)).

Lemma SELECT_word j n :
  SELECT j n = repeat CNIP (j + 1) ++ CDROP :: repeat CNIP (n + 1 - j).
Proof. unfold SELECT; rewrite map_app, map_cons, !map_repeat; reflexivity. Qed.

Theorem select_actual rows j x g d h tail
    (Hx : nth_error rows j = Some x) :
  L1_CompPerm.exec (SELECT j (length rows))
    (g, pack P (rows ++ [0]) tail, d, h) = None \/
  L1_CompPerm.exec (SELECT j (length rows))
    (g, pack P (rows ++ [0]) tail, d, h) = Some (x, tail, d, 0).
Proof.
  unfold SELECT; rewrite !selector_exec_bridge.
  exact (NativeSelection.native_select_nth P unP unP_P rows j x g d h tail Hx).
Qed.

Definition AXRows (a h b c u : nat) : list nat :=
  [rho1 a b; rho2 a b c; rho3 a b c; rho4 a b c; rho5 a b c;
   rho6 a c; growG a b c; rho8 a b c u; wal u h].

Lemma ax_stack_selector_view a h b c u tail :
  ax_stack a h b c u 0 tail = pack P (AXRows a h b c u ++ [0]) tail.
Proof. reflexivity. Qed.

Theorem select_AX_row a h b c u j x g tail
    (Hx : nth_error (AXRows a h b c u) j = Some x) :
  L1_CompPerm.exec (SELECT j 9) (g, ax_stack a h b c u 0 tail, 0, 0) = None \/
  L1_CompPerm.exec (SELECT j 9) (g, ax_stack a h b c u 0 tail, 0, 0)
    = Some (x, tail, 0, 0).
Proof.
  rewrite ax_stack_selector_view.
  exact (select_actual (AXRows a h b c u) j x g 0 0 tail Hx).
Qed.

Print Assumptions select_actual.
Print Assumptions select_AX_row.
