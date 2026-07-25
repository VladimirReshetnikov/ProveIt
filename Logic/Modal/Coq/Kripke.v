(**
  Kripke semantics for the modal syntax in [Syntax].

  The semantic clauses follow
  Foundation/Modal/Kripke/Basic.lean at the pinned read-only source revision.
  Classical logic is used only to expose the existential reading of diamond
  (which Foundation defines as [~ box ~]); box, implication, substitution,
  and their iteration laws are constructive.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record frame : Type := {
  World : Type;
  Rel : World -> World -> Prop
}.

Arguments World _ : clear implicits.
Arguments Rel f _ _ : clear implicits.

Definition valuation (AtomType : Type) (F : frame) : Type :=
  AtomType -> World F -> Prop.

Fixpoint satisfies {AtomType} (F : frame) (V : valuation AtomType F)
    (w : World F) (p : formula AtomType) : Prop :=
  match p with
  | Atom a => V a w
  | Bottom => False
  | Imp q r => @satisfies AtomType F V w q ->
               @satisfies AtomType F V w r
  | Box q => forall u, Rel F w u -> @satisfies AtomType F V u q
  end.

Arguments satisfies {AtomType} F V w p.

Definition valid {AtomType} (F : frame) (p : formula AtomType) : Prop :=
  forall (V : valuation AtomType F) (w : World F), satisfies F V w p.

Definition model_valid {AtomType} (F : frame) (V : valuation AtomType F)
    (p : formula AtomType) : Prop :=
  forall w, satisfies F V w p.

Lemma satisfies_bottom :
  forall AtomType F (V : valuation AtomType F) w,
    ~ satisfies F V w Bottom.
Proof. intros; simpl; auto. Qed.

Lemma satisfies_imp :
  forall AtomType F (V : valuation AtomType F) w (p q : formula AtomType),
    satisfies F V w (Imp p q) <->
    (satisfies F V w p -> satisfies F V w q).
Proof. reflexivity. Qed.

Lemma satisfies_neg :
  forall AtomType F (V : valuation AtomType F) w (p : formula AtomType),
    satisfies F V w (Neg p) <-> ~ satisfies F V w p.
Proof. reflexivity. Qed.

Lemma satisfies_top :
  forall AtomType F (V : valuation AtomType F) w,
    satisfies F V w (@Top AtomType).
Proof. intros; simpl; auto. Qed.

Lemma satisfies_and :
  forall AtomType F (V : valuation AtomType F) w (p q : formula AtomType),
    satisfies F V w (And p q) <->
    satisfies F V w p /\ satisfies F V w q.
Proof.
  intros; unfold And, Neg; simpl; tauto.
Qed.

Lemma satisfies_or :
  forall AtomType F (V : valuation AtomType F) w (p q : formula AtomType),
    satisfies F V w (Or p q) <->
    satisfies F V w p \/ satisfies F V w q.
Proof.
  intros; unfold Or, Neg; simpl; tauto.
Qed.

Lemma satisfies_iff :
  forall AtomType F (V : valuation AtomType F) w (p q : formula AtomType),
    satisfies F V w (Iff p q) <->
    (satisfies F V w p <-> satisfies F V w q).
Proof.
  intros; unfold Iff; rewrite satisfies_and; simpl; tauto.
Qed.

Lemma satisfies_box :
  forall AtomType F (V : valuation AtomType F) w (p : formula AtomType),
    satisfies F V w (Box p) <->
    forall u, Rel F w u -> satisfies F V u p.
Proof. reflexivity. Qed.

Lemma satisfies_dia_intro :
  forall AtomType F (V : valuation AtomType F) w (p : formula AtomType),
    (exists u, Rel F w u /\ satisfies F V u p) ->
    satisfies F V w (Dia p).
Proof.
  intros AtomType F V w p [u [Rwu Hu]].
  unfold Dia, Neg; simpl.
  intro Hbox. exact (Hbox u Rwu Hu).
Qed.

Lemma satisfies_dia_elim :
  forall AtomType F (V : valuation AtomType F) w (p : formula AtomType),
    satisfies F V w (Dia p) ->
    exists u, Rel F w u /\ satisfies F V u p.
Proof.
  intros AtomType F V w p Hdia.
  apply NNPP; intro Hnone.
  apply Hdia. intros u Rwu Hu.
  apply Hnone. exists u; auto.
Qed.

Lemma satisfies_dia :
  forall AtomType F (V : valuation AtomType F) w (p : formula AtomType),
    satisfies F V w (Dia p) <->
    exists u, Rel F w u /\ satisfies F V u p.
Proof.
  split; [apply satisfies_dia_elim | apply satisfies_dia_intro].
Qed.

Fixpoint rel_iter {W : Type} (R : W -> W -> Prop) (n : nat) (x y : W)
    : Prop :=
  match n with
  | 0 => x = y
  | S k => exists z, R x z /\ rel_iter R k z y
  end.

Lemma rel_iter_zero :
  forall W (R : W -> W -> Prop) x y,
    rel_iter R 0 x y <-> x = y.
Proof. reflexivity. Qed.

Lemma rel_iter_succ :
  forall W (R : W -> W -> Prop) n x y,
    rel_iter R (S n) x y <->
    exists z, R x z /\ rel_iter R n z y.
Proof. reflexivity. Qed.

Lemma rel_iter_one :
  forall W (R : W -> W -> Prop) x y,
    rel_iter R 1 x y <-> R x y.
Proof.
  intros; simpl; split.
  - intros [z [Rxz ->]]; exact Rxz.
  - intro Rxy; exists y; auto.
Qed.

Lemma rel_iter_plus :
  forall W (R : W -> W -> Prop) n m x z,
    rel_iter R (n + m) x z <->
    exists y, rel_iter R n x y /\ rel_iter R m y z.
Proof.
  intros W R n; induction n as [|n IH]; intros m x z; simpl.
  - split.
    + intro H; exists x; auto.
    + intros [y [-> H]]; exact H.
  - split.
    + intros [u [Rxu Huz]].
      destruct (proj1 (IH m u z) Huz) as [y [Huy Hyz]].
      exists y; split; [exists u; auto | exact Hyz].
    + intros [y [[u [Rxu Huy]] Hyz]].
      exists u; split; [exact Rxu |].
      apply (proj2 (IH m u z)); exists y; auto.
Qed.

Lemma rel_iter_step_left :
  forall W (R : W -> W -> Prop) n x y z,
    R x y -> rel_iter R n y z -> rel_iter R (S n) x z.
Proof. intros; exists y; auto. Qed.

Lemma rel_iter_step_right :
  forall W (R : W -> W -> Prop) n x y z,
    rel_iter R n x y -> R y z -> rel_iter R (S n) x z.
Proof.
  intros W R n x y z Hxy Hyz.
  replace (S n) with (n + 1) by lia.
  apply rel_iter_plus; exists y; split; auto.
  apply rel_iter_one; exact Hyz.
Qed.

Lemma satisfies_box_iter :
  forall AtomType F (V : valuation AtomType F) n w
         (p : formula AtomType),
    satisfies F V w (box_iter n p) <->
    forall u, rel_iter (Rel F) n w u -> satisfies F V u p.
Proof.
  intros AtomType F V n; induction n as [|n IH]; intros w p; simpl.
  - split.
    + intros Hp u ->; exact Hp.
    + intro H; apply H; reflexivity.
  - split.
    + intros H u [z [Rwz Hzu]].
      apply (proj1 (IH z p)); auto.
    + intros H z Rwz.
      apply (proj2 (IH z p)).
      intros u Hzu; apply H; exists z; auto.
Qed.

Lemma satisfies_dia_iter_intro :
  forall AtomType F (V : valuation AtomType F) n w
         (p : formula AtomType),
    (exists u, rel_iter (Rel F) n w u /\ satisfies F V u p) ->
    satisfies F V w (dia_iter n p).
Proof.
  intros AtomType F V n; induction n as [|n IH]; intros w p [u [Hwu Hp]];
    simpl in *.
  - now subst.
  - destruct Hwu as [z [Rwz Hzu]].
    apply satisfies_dia_intro. exists z; split; auto.
    apply IH. exists u; auto.
Qed.

Lemma satisfies_dia_iter_elim :
  forall AtomType F (V : valuation AtomType F) n w
         (p : formula AtomType),
    satisfies F V w (dia_iter n p) ->
    exists u, rel_iter (Rel F) n w u /\ satisfies F V u p.
Proof.
  intros AtomType F V n; induction n as [|n IH]; intros w p H; simpl in *.
  - exists w; auto.
  - apply satisfies_dia_elim in H.
    destruct H as [z [Rwz Hz]].
    destruct (IH z p Hz) as [u [Hzu Hu]].
    exists u; split; auto. exists z; auto.
Qed.

Lemma satisfies_dia_iter :
  forall AtomType F (V : valuation AtomType F) n w
         (p : formula AtomType),
    satisfies F V w (dia_iter n p) <->
    exists u, rel_iter (Rel F) n w u /\ satisfies F V u p.
Proof.
  split; [apply satisfies_dia_iter_elim | apply satisfies_dia_iter_intro].
Qed.

Lemma satisfies_substitute :
  forall (A B : Type) F (V : valuation B F) (sigma : A -> formula B)
         w (p : formula A),
    satisfies F V w (substitute sigma p) <->
    satisfies F (fun a u => satisfies F V u (sigma a)) w p.
Proof.
  intros A B F V sigma w p; revert w.
  induction p as [a| |p IHp q IHq|p IHp]; intro w; simpl.
  - reflexivity.
  - tauto.
  - rewrite IHp, IHq; reflexivity.
  - split; intros H u Rwu.
    + apply (proj1 (IHp u)); auto.
    + apply (proj2 (IHp u)); auto.
Qed.

Lemma valid_substitution :
  forall (A B : Type) F (p : formula A) (sigma : A -> formula B),
    valid F p -> valid F (substitute sigma p).
Proof.
  intros A B F p sigma Hp V w.
  apply (proj2 (@satisfies_substitute A B F V sigma w p)).
  apply Hp.
Qed.

Lemma valid_K :
  forall AtomType (F : frame) (p q : formula AtomType),
    valid F (Imp (Box (Imp p q)) (Imp (Box p) (Box q))).
Proof.
  intros AtomType F p q V w Hpq Hp u Rwu.
  exact (Hpq u Rwu (Hp u Rwu)).
Qed.
