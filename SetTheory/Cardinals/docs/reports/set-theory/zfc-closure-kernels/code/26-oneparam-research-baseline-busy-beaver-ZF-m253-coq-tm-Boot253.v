(** * Boot253: exact blank-tape prefix and its finite register-machine certificate.

    The literal 253-state candidate starts in [st 5] (actual numeric state 0).
    After 312,975 steps it reaches the original numeric dispatch label 96,
    with the exact configuration of [rm_run p254 330 ([], R0)].

    The PC is [false; false; false], followed by 37 padding zeros, so the
    head-to-header distance is 40. Physical registers are
    [0;2;0;0;0;0;5;0;0]. The complete 158-block spare suffix has value 1 at
    indices 2 and 8 and value 0 elsewhere; it is retained in the theorem.

    The zipper computation and its soundness proof follow M254.Boot, whose
    authorship and provenance remain preserved in the original source. *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia PArith.
From BusyCoq Require Import TM.
From M254 Require Import RM Prog254.
From M253 Require Import TM253 Zip SymExec Check253.
Import ListNotations.

(** ** The exact finite RM prefix, without functional extensionality *)
Definition P330 : list bool := [false; false; false].

Definition prefix330_result : option conf := rm_run p254 330 ([], R0).

(* Retaining the computed function avoids an extensional equality between
   register functions. Its complete pointwise values are checked below. *)
Definition R330 : regs :=
  match prefix330_result with
  | Some (_, Rg) => Rg
  | None => regs0
  end.

Definition prefix330_ok : bool :=
  match prefix330_result with
  | Some (P, _) => if list_eq_dec bool_dec P P330 then true else false
  | None => false
  end.

Lemma prefix330_ok_true : prefix330_ok = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem rm_prefix330 : rm_run p254 330 ([], R0) = Some (P330, R330).
Proof.
  change (prefix330_result = Some (P330, R330)).
  pose proof prefix330_ok_true as H.
  unfold prefix330_ok in H. unfold R330.
  destruct prefix330_result as [[P Rg]|] eqn:E; [|discriminate].
  destruct (list_eq_dec bool_dec P P330) as [EP|]; [|discriminate].
  subst P. reflexivity.
Qed.

Lemma R330_values r :
  R330 r = if Nat.eqb r 0 then 5 else if Nat.eqb r 4 then 2 else 0.
Proof.
  do 9 (destruct r as [|r]; [vm_compute; reflexivity|]).
  vm_compute. reflexivity.
Qed.

Lemma R330_first9 : map R330 (seq 0 9) = [5; 0; 0; 0; 2; 0; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.

Lemma R330_physical : vregs R330 = [0; 2; 0; 0; 0; 0; 5; 0; 0].
Proof. vm_compute. reflexivity. Qed.

Definition ext158 : list nat := [0; 0; 1; 0; 0; 0; 0; 0; 1] ++ repeat 0 149.
Definition boot_regs : list nat := vregs R330 ++ ext158.

Lemma ext158_length : length ext158 = 158.
Proof. reflexivity. Qed.

Lemma boot_regs_length : length boot_regs = 167.
Proof. vm_compute. reflexivity. Qed.

(** ** Computable numeric steps on finite list zippers *)
Definition lconf := (nat * list bool * list bool)%type.

Definition lstep (s : lconf) : option lconf :=
  let '(q, l, r) := s in
  match tmn q (hd false r) with
  | None => None
  | Some (w, R, q') => Some (q', w :: l, tl r)
  | Some (w, L, q') => Some (q', tl l, hd false l :: w :: tl r)
  end.

Definition lconc (s : lconf) : Q * tape := let '(q, l, r) := s in zc (st q) l r.

Lemma lstep_sound s s' : lstep s = Some s' -> lconc s -[ tm ]-> lconc s'.
Proof.
  destruct s as [[q l] r]. unfold lstep. intros H.
  assert (E : zc (st q) l r = zc (st q) l (hd false r :: tl r))
    by (destruct r; reflexivity).
  simpl. rewrite E. clear E.
  destruct (tmn q (hd false r)) as [[[w [|]] q1]|] eqn:T; [| |discriminate];
    injection H as <-; simpl.
  - apply zL, tm_st, T.
  - apply zR, tm_st, T.
Qed.

Fixpoint lrunp (p : positive) (s : lconf) : option lconf :=
  match p with
  | xH => lstep s
  | xO p => match lrunp p s with None => None | Some s => lrunp p s end
  | xI p => match lstep s with
            | None => None
            | Some s => match lrunp p s with None => None | Some s => lrunp p s end
            end
  end.

Lemma lrunp_sound p s s' : lrunp p s = Some s' -> lconc s -->* lconc s'.
Proof.
  revert s s'. induction p as [p IH|p IH|]; intros s s' H; simpl in H.
  - destruct (lstep s) as [s1|] eqn:E1; [|discriminate].
    destruct (lrunp p s1) as [s2|] eqn:E2; [|discriminate].
    eapply evstep_step; [apply lstep_sound, E1|].
    eapply evstep_trans; [apply IH, E2 | apply IH, H].
  - destruct (lrunp p s) as [s1|] eqn:E1; [|discriminate].
    eapply evstep_trans; [apply IH, E1 | apply IH, H].
  - eapply evstep_step; [apply lstep_sound, H | apply evstep_refl].
Qed.

(** ** Removing only exterior blank cells *)
Fixpoint dropf (l : list bool) : list bool :=
  match l with false :: l => dropf l | _ => l end.
Definition trim (l : list bool) : list bool := rev (dropf (rev l)).

Lemma dropf_spec l : exists n, l = zeros n ++ dropf l.
Proof.
  induction l as [|[|] l IH]; [exists 0; reflexivity | exists 0; reflexivity|].
  destruct IH as [n E]. exists (S n). simpl. rewrite <- E. reflexivity.
Qed.

Lemma rev_zeros n : rev (zeros n) = zeros n.
Proof.
  induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH.
  symmetry. apply (rep_snoc false n).
Qed.

Lemma trim_spec l : exists n, l = trim l ++ zeros n.
Proof.
  destruct (dropf_spec (rev l)) as [n E]. exists n. unfold trim.
  rewrite <- rev_zeros, <- rev_app_distr, <- E. symmetry. apply rev_involutive.
Qed.

Definition boot_right : list bool := P330 ++ zeros 37 ++ true :: sepsR boot_regs.

Lemma boot_right_shape : boot_right = zeros 40 ++ true :: sepsR (vregs R330 ++ ext158).
Proof. reflexivity. Qed.

Definition boot_ok : bool :=
  match lrunp 312975 (5, [], []) with
  | Some (q, l, r) =>
      andb (Nat.eqb q 96)
           (andb (if list_eq_dec bool_dec (trim l) [true] then true else false)
                 (if list_eq_dec bool_dec (trim r) boot_right then true else false))
  | None => false
  end.

Lemma boot_ok_true : boot_ok = true.
Proof. Time vm_compute. reflexivity. Qed.

(** This direct certificate records the finite zipper's exterior blank
    padding. Using its equality avoids destructing a closed 312,975-step
    computation inside the reachability proof. *)
Lemma boot_run :
  lrunp 312975 (5, [], []) =
  Some (96, [true] ++ zeros 10, boot_right ++ zeros 1).
Proof. Time vm_compute. reflexivity. Qed.

Theorem boot : c0 -->* zc (st 96) [true] boot_right.
Proof.
  pose proof (lrunp_sound 312975 (5, [], [])
    (96, [true] ++ zeros 10, boot_right ++ zeros 1) boot_run) as H.
  change (zc (st 5) [] [] -->*
          zc (st 96) ([true] ++ zeros 10) (boot_right ++ zeros 1)) in H.
  rewrite zc_padl, zc_padr in H.
  change c0 with (zc (st 5) [] []). exact H.
Qed.

Corollary boot_at_prefix330 :
  c0 -->* zc (st 96) [true]
     (P330 ++ zeros 37 ++ true :: sepsR (vregs R330 ++ ext158)).
Proof. exact boot. Qed.

Print Assumptions rm_prefix330.
Print Assumptions R330_values.
Print Assumptions R330_first9.
Print Assumptions R330_physical.
Print Assumptions boot_ok_true.
Print Assumptions boot_run.
Print Assumptions boot.
Print Assumptions boot_at_prefix330.
