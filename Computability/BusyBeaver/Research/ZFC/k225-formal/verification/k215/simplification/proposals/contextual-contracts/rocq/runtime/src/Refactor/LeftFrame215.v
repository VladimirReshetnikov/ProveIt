(** Input SHA256: e2b8fd178afba6c85edf17eb647751d90a606541f03b01b76ec309acfdd62238. Untrusted finite data. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith.
From K215F Require Import Runtime230Core.
From Refactor Require Import LeftFrame.
Import ListNotations.

Record template := mkTemplate { start : sconf; steps : nat; right : list seg }.
Definition templates : list template := [
  (* Template 0: CC 3, suffix 10111. *)
  mkTemplate (62,false,[SB true; SB true; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 12 [SB true; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 1: CC 2, suffix 111. *)
  mkTemplate (13,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 8 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 2: CB 1, suffix 1001. *)
  mkTemplate (108,false,[SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 7 [SB true; SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 3: CC 2, suffix 111. *)
  mkTemplate (42,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 5 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 4: CC 2, suffix 111. *)
  mkTemplate (138,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 11 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 5: CC 2, suffix 111. *)
  mkTemplate (141,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 5 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 6: CC 2, suffix 10000011. *)
  mkTemplate (42,false,[SB true; SB false; SB false; SB false; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 15 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 7: CC 2, suffix 1011. *)
  mkTemplate (57,false,[SB true; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 7 [SB true; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 8: CC 3, suffix 100111. *)
  mkTemplate (62,false,[SB true; SB true; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 14 [SB true; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 9: CC 2, suffix 111. *)
  mkTemplate (57,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 5 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 10: CC 3, suffix 10111. *)
  mkTemplate (80,false,[SB true; SB true; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 21 [SB true; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 11: CC 2, suffix 111. *)
  mkTemplate (72,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 8 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 12: CC 2, suffix 111. *)
  mkTemplate (126,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 5 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 13: CC 2, suffix 10011. *)
  mkTemplate (42,false,[SB true; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 9 [SB true; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 14: CC 2, suffix 111. *)
  mkTemplate (47,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 5 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 15: CC 3, suffix 1000111. *)
  mkTemplate (83,false,[SB true; SB true; SB false; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 13 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 16: CC 2, suffix 111. *)
  mkTemplate (139,false,[SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 5 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 17: CC 2, suffix 1000011. *)
  mkTemplate (42,false,[SB true; SB false; SB false; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 13 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 18: CC 3, suffix 100000111. *)
  mkTemplate (83,false,[SB true; SB true; SB false; SB false; SB false; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 17 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 19: CC 3, suffix 10000111. *)
  mkTemplate (83,false,[SB true; SB true; SB false; SB false; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 15 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 20: CC 2, suffix 1011. *)
  mkTemplate (126,false,[SB true; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 7 [SB true; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 21: CC 3, suffix 100111. *)
  mkTemplate (83,false,[SB true; SB true; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 11 [SB true; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 22: CC 2, suffix 100011. *)
  mkTemplate (42,false,[SB true; SB false; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 11 [SB true; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 23: CC 3, suffix 1111. *)
  mkTemplate (62,false,[SB true; SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 10 [SB true; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 24: CC 2, suffix 1000101. *)
  mkTemplate (108,false,[SB false; SB true; SB false; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 13 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 25: CB 1, suffix 0011. *)
  mkTemplate (103,false,[SB true; SB false; SB false],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 24 [SB true; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 26: CC 1, suffix 101. *)
  mkTemplate (122,false,[SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 5 [SB true; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 27: CC 2, suffix 1101. *)
  mkTemplate (108,false,[SB false; SB true; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 7 [SB true; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 28: CB 1, suffix 0110111. *)
  mkTemplate (103,false,[SB true; SB true; SB false; SB true; SB true; SB false],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 39 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 29: CC 1, suffix 11. *)
  mkTemplate (122,false,[SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 3 [SB true; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 30: CC 2, suffix 1011. *)
  mkTemplate (42,false,[SB true; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 7 [SB true; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 31: CC 2, suffix 10000101. *)
  mkTemplate (108,false,[SB false; SB true; SB false; SB false; SB false; SB false; SB true],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 15 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 32: CB 1, suffix 00111. *)
  mkTemplate (103,false,[SB true; SB true; SB false; SB false],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 29 [SB true; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 33: CB 1, suffix 0011111. *)
  mkTemplate (96,false,[SB true; SB true; SB true; SB true; SB false; SB false],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 39 [SB true; SB false; SB false; SB false; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)];
  (* Template 34: CB 1, suffix 0011. *)
  mkTemplate (162,false,[SB true; SB false; SB false],[SB true; SR false 1 16; SB true; SBox (BPlain FNone)]) 24 [SB true; SB false; SB false; SB false; SR false 1 16; SB true; SBox (BPlain FNone)]].

Definition seg_dec (x y : seg) : {x = y} + {x <> y}.
Proof. decide equality; first [apply Nat.eq_dec | apply bool_dec | apply boxst_dec]. Defined.
Definition sconf_dec (x y : sconf) : {x = y} + {x <> y}.
Proof. unfold sconf; repeat decide equality. Defined.

Definition checked (t : template) : bool :=
  match run_local None (steps t) (start t) with
  | None => false
  | Some s => if sconf_dec s (2,true,[],right t) then true else false
  end.

Lemma checked_ok t : checked t = true ->
  run_local None (steps t) (start t) = Some (2,true,[],right t).
Proof.
  unfold checked. destruct (run_local None (steps t) (start t)) as [s|] eqn:E; [|discriminate].
  destruct (sconf_dec s (2,true,[],right t)) as [Hs|Hs]; [intros _; now rewrite Hs|discriminate].
Qed.

Theorem template_count : length templates = 35.
Proof. reflexivity. Qed.
Theorem all_checked : forallb checked templates = true.
Proof. vm_compute. reflexivity. Qed.

Theorem template_replay t F : In t templates ->
  run_local None (steps t) (add_left F (start t)) =
  Some (add_left F (2,true,[],right t)).
Proof.
  intro Ht. apply run_local_frame, checked_ok.
  exact (proj1 (forallb_forall checked templates) all_checked t Ht).
Qed.

Print Assumptions all_checked.
Print Assumptions template_replay.
