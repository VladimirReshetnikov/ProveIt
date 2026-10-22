(** REVIEW DRAFT, NOT COMPILED IN THIS SESSION.
    Semantic replacement interface for the maintained K215 site checker.
    Base: ProveIt 2ca3a5c16f0876d2cab842056353c03a1ed2f5f0.

    The definitions below preserve the exact physical start/target configurations,
    branch premises, progress, logical/physical register map and depth guard.
    The proposed adapter proofs reuse the existing, checked site theorems.
    They are supplied for review, not represented as new Rocq kernel evidence. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K230 Require Import RM.
From K215F Require Import TM230 Zip Runtime230Core Interpreter230Sites
  Interpreter230Check Tape230Blocks Tape230Carry.
Import ListNotations.

Definition RunSpec (br : branch) (Q P : list bool) (ovf : bool) (x : boxst) : Prop :=
  forall n vs, valid br vs ->
    conc n vs (start Q) -->+ conc n vs (tgt_conf P ovf x).

Definition HaltSpec (Q : list bool) : Prop :=
  forall n vs, 10 <= length vs ->
    exists c, conc n vs (start Q) -->+ c /\ halted tm c.

Definition SiteSpec (Q : list bool) (o : op) : Prop :=
  match o with
  | OInc r => RunSpec None Q (inc_path Q) (allones Q) (BPlain (FInc r))
  | ODec r =>
      RunSpec (Some (r, true)) Q (brk 1 Q)
        (allones (strip_path false 1 Q)) (BPlain FNone) /\
      RunSpec (Some (r, false)) Q (inc_path Q)
        (allones Q) (BPlain (FDec r))
  | OBrk k => RunSpec None Q (brk k Q)
      (allones (strip_path false k Q)) (BPlain FNone)
  | OCont k => RunSpec None Q (cont k Q) false (BPlain FNone)
  | OHalt => HaltSpec Q
  end.

Definition EdgeSpec (Q : list bool) (e : edge) : Prop :=
  length Q <= 48 /\
  match e with
  | EInc r => r < 9 /\ SiteSpec Q (OInc (phys_of r))
  | EDecnz r => r < 9 /\ SiteSpec Q (ODec (phys_of r))
  | EBreak k => SiteSpec Q (OBrk k)
  | EContinue k => SiteSpec Q (OCont k)
  | EHalt => SiteSpec Q OHalt
  | ENode _ => False
  end.

Lemma run_to_spec br Q P ovf x :
  run_to br Q (tgt_conf P ovf x) = true -> RunSpec br Q P ovf x.
Proof.
  intros H n vs V.
  exact (run_to_sound Tape230Blocks.box_mark Tape230Carry.box_inc
    Tape230Carry.box_dec0 Tape230Carry.box_decp
    br Q (tgt_conf P ovf x) H n vs V).
Qed.

Lemma run_halt_spec Q : run_halt Q = true -> HaltSpec Q.
Proof.
  intros H n vs V. rewrite conc_start.
  exact (site_halt Tape230Blocks.box_mark Tape230Carry.box_inc
    Tape230Carry.box_dec0 Tape230Carry.box_decp Q H n vs V).
Qed.

Theorem check_site_sound Q o : check_site Q o = true -> SiteSpec Q o.
Proof.
  destruct o; cbn [check_site SiteSpec].
  - apply run_to_spec.
  - intros H. apply andb_prop in H as [H0 H1].
    split; apply run_to_spec; assumption.
  - apply run_to_spec.
  - apply run_to_spec.
  - apply run_halt_spec.
Qed.

Theorem check_edge_sound Q e : check_edge Q e = true -> EdgeSpec Q e.
Proof.
  unfold check_edge, EdgeSpec.
  destruct (Nat.leb (length Q) 48) eqn:Hd; [|discriminate].
  intros H. split; [apply Nat.leb_le, Hd|].
  destruct e as [n|r|r|k|k|]; cbn in *; try discriminate.
  - destruct (Nat.ltb r 9) eqn:Hr; [|discriminate].
    split; [apply Nat.ltb_lt, Hr | apply check_site_sound, H].
  - destruct (Nat.ltb r 9) eqn:Hr; [|discriminate].
    split; [apply Nat.ltb_lt, Hr | apply check_site_sound, H].
  - apply check_site_sound, H.
  - apply check_site_sound, H.
  - apply check_site_sound, H.
Qed.

(** Required consumer interface (the producer may later be factored):

    forall P e d,
      walk p215 (nnodes p215 + 1) (root p215) P 0 = Some (e,d) ->
      EdgeSpec (firstn d (P ++ repeat false d)) e.

    Current provider: check_edge_sound followed by Interpreter230Check.leaf_check.
    A future provider can compose a zero-or-more-step decoder prefix with a
    strictly positive primitive/continuation theorem. The consumed padded path,
    physical target, overflow, file growth and branch premise must be unchanged.

    Refactor Sim230.inv_view to return EdgeSpec; refactor inv_step/inv_halt to
    eliminate EdgeSpec/SiteSpec, not check_edge/check_site. Keep the existing
    Inv and public endpoint statements. This draft does not perform that edit. *)

Print Assumptions check_site_sound.
Print Assumptions check_edge_sound.
