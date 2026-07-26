(**
  The quasinormal extensions GL + box^n bottom.

  This module ports the active theorem surface of Foundation's pinned
  [Modal/Logic/GLPlusBoxBot/Basic.lean].  Extended natural numbers are
  represented by [option nat]: [Some n] is the finite stage obtained by
  adjoining [box_iter n Bottom] to GL, while [None] is the omega stage and
  is definitionally just GL.

  The finite stages use [logic_sum_quasi_normal], the least closure under
  classical reasoning, modus ponens, and substitution containing GL and the
  displayed singleton axiom.  They deliberately do not acquire a
  necessitation rule.  The exact deduction theorem below is proved directly
  from this inductive presentation; its substitution case relies only on
  the fact that iterated boxed falsity contains no atoms.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From FoundationModal Require Import
  Syntax NormalHilbert LogicInfrastructure GLGrzDerivations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The singleton logic containing exactly [box^n bottom]. *)
Definition GLPlusBoxBot_axiom (n : nat) : modal_logic_set nat :=
  fun p => p = box_iter n (@Bottom nat).

(** Foundation [Modal.GLPlusBoxBot].  [None] represents [omega]. *)
Definition GLPlusBoxBot (n : option nat) : modal_logic_set nat :=
  match n with
  | Some k =>
      logic_sum_quasi_normal (@GL_proves nat) (GLPlusBoxBot_axiom k)
  | None => @GL_proves nat
  end.

(** Every stage is quasinormal, including the omega stage. *)
Theorem GLPlusBoxBot_quasi_normal :
  forall n, quasi_normal_logic (GLPlusBoxBot n).
Proof.
  intros [n |]; simpl.
  - apply logic_sum_quasi_normal_quasi_left.
    exact (normal_quasi GL_normal_logic).
  - exact (normal_quasi GL_normal_logic).
Qed.

(** Foundation's inclusion instance [GL <= GLPlusBoxBot n]. *)
Theorem GL_weaker_than_GLPlusBoxBot :
  forall n, logic_subset (@GL_proves nat) (GLPlusBoxBot n).
Proof.
  intros [n |] p Hp; simpl.
  - now apply LSQ_mem_left.
  - exact Hp.
Qed.

(** Foundation [Logic.GLPlusBoxBot.boxbot]. *)
Theorem GLPlusBoxBot_boxbot :
  forall n, GLPlusBoxBot (Some n) (box_iter n (@Bottom nat)).
Proof.
  intro n. simpl. apply LSQ_mem_right. reflexivity.
Qed.

(** The axiom is letterless, so every substitution fixes it. *)
Lemma substitute_GLPlusBoxBot_axiom :
  forall (sigma : nat -> formula nat) n,
    substitute sigma (box_iter n (@Bottom nat)) =
    box_iter n Bottom.
Proof.
  intros sigma n. rewrite substitute_box_iter. reflexivity.
Qed.

(** Foundation [iff_provable_GLPlusBoxBot_provable_GL]. *)
Theorem iff_provable_GLPlusBoxBot_provable_GL :
  forall n (p : formula nat),
    GLPlusBoxBot (Some n) p <->
    GL_proves (Imp (box_iter n Bottom) p).
Proof.
  intros n p; split.
  - intro Hp. simpl in Hp.
    induction Hp as
        [p Hp
        | p Hp
        | p q Hpq IHpq Hp IHp
        | sigma p Hp IH].
    + now apply (logic_imply_intro GL_classical_logic).
    + unfold GLPlusBoxBot_axiom in Hp. subst p.
      apply logic_identity. exact GL_classical_logic.
    + exact (logic_under_mp GL_classical_logic IHpq IHp).
    + pose proof
        (@normal_proves_substitute schema_L
          schema_L_substitution_closed nat nat sigma
          (Imp (box_iter n Bottom) p) IH) as Hsub.
      change
        (GL_proves
          (Imp (substitute sigma (box_iter n Bottom))
               (substitute sigma p))) in Hsub.
      rewrite substitute_GLPlusBoxBot_axiom in Hsub.
      exact Hsub.
  - intro Hp. simpl.
    eapply LSQ_mp.
    + apply LSQ_mem_left. exact Hp.
    + apply LSQ_mem_right. reflexivity.
Qed.

(** Foundation [eq_GLPlusBoxBot_omega_GL]. *)
Theorem eq_GLPlusBoxBot_omega_GL :
  GLPlusBoxBot None = @GL_proves nat.
Proof. reflexivity. Qed.

(** Iterated regularity of box in GL. *)
Lemma GL_proves_box_iter_regularity :
  forall n (p q : formula nat),
    GL_proves (Imp p q) ->
    GL_proves (Imp (box_iter n p) (box_iter n q)).
Proof.
  induction n as [|n IH]; intros p q Hpq; simpl.
  - exact Hpq.
  - apply logic_box_regularity; [exact GL_normal_logic |].
    now apply IH.
Qed.

Lemma box_iter_box :
  forall n (p : formula nat),
    box_iter n (Box p) = box_iter (S n) p.
Proof.
  induction n as [|n IH]; intro p; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

(** The stage-[n] axiom entails the stage-[n+1] axiom already in GL. *)
Lemma GL_proves_boxbot_successor :
  forall n,
    GL_proves
      (Imp (box_iter n (@Bottom nat))
           (box_iter (S n) Bottom)).
Proof.
  intro n.
  assert (Hbottom :
    GL_proves (Imp (@Bottom nat) (Box Bottom))).
  {
    apply (logic_classical_tautology GL_classical_logic).
    intro rho; simpl; tauto.
  }
  pose proof (GL_proves_box_iter_regularity n Hbottom) as Hiter.
  now rewrite box_iter_box in Hiter.
Qed.

(** Foundation [Logic.GLPlusBoxBot.weakerThan_succ]. *)
Theorem GLPlusBoxBot_weakerThan_succ :
  forall n,
    logic_subset (GLPlusBoxBot (Some (S n)))
                 (GLPlusBoxBot (Some n)).
Proof.
  intros n p Hp.
  apply (proj2 (iff_provable_GLPlusBoxBot_provable_GL n p)).
  eapply logic_imp_trans; [exact GL_classical_logic | |].
  - apply GL_proves_boxbot_successor.
  - now apply
      (proj1 (iff_provable_GLPlusBoxBot_provable_GL (S n) p)).
Qed.

(** Foundation [Logic.GLPlusBoxBot.weakerThan_add]. *)
Theorem GLPlusBoxBot_weakerThan_add :
  forall n k,
    logic_subset (GLPlusBoxBot (Some (n + k)))
                 (GLPlusBoxBot (Some n)).
Proof.
  intros n k. induction k as [|k IH].
  - rewrite Nat.add_0_r. intros p Hp; exact Hp.
  - intros p Hp.
    replace (n + S k) with (S (n + k)) in Hp by lia.
    apply IH.
    exact (@GLPlusBoxBot_weakerThan_succ (n + k) p Hp).
Qed.

(** Foundation [Logic.GLPlusBoxBot.weakerThan_lt]. *)
Theorem GLPlusBoxBot_weakerThan_lt :
  forall n m,
    n < m ->
    logic_subset (GLPlusBoxBot (Some m))
                 (GLPlusBoxBot (Some n)).
Proof.
  intros n m Hlt p Hp.
  replace m with (n + (m - n)) in Hp by lia.
  exact (@GLPlusBoxBot_weakerThan_add n (m - n) p Hp).
Qed.

(** Snake-case aliases for clients following the surrounding Coq API. *)
Definition GLPlusBoxBot_weaker_than_succ := GLPlusBoxBot_weakerThan_succ.
Definition GLPlusBoxBot_weaker_than_add := GLPlusBoxBot_weakerThan_add.
Definition GLPlusBoxBot_weaker_than_lt := GLPlusBoxBot_weakerThan_lt.
