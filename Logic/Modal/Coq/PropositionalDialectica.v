(** A Dialectica-style realizability interpretation for intuitionistic
    propositional formulas.

    This ports Foundation/Propositional/Dialectica/Basic.  Witness and
    counter types are indexed directly by formulas; realizability is then a
    structurally recursive dependent predicate.  Atoms remain polymorphic. *)

From Stdlib Require Import Logic.Classical_Prop Logic.Classical_Pred_Type.
From FoundationModal Require Import PropositionalFormula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive p_dialectica_player : Type :=
| PDEloise
| PDAbelard.

Fixpoint p_dialectica_argument {Atom : Type}
    (player : p_dialectica_player) (p : pformula Atom) : Type :=
  match player, p with
  | _, PAtom _ => unit
  | _, PFalsum => unit
  | PDEloise, PAnd q r =>
      (p_dialectica_argument PDEloise q *
       p_dialectica_argument PDEloise r)%type
  | PDAbelard, PAnd q r =>
      (p_dialectica_argument PDAbelard q +
       p_dialectica_argument PDAbelard r)%type
  | PDEloise, POr q r =>
      (p_dialectica_argument PDEloise q +
       p_dialectica_argument PDEloise r)%type
  | PDAbelard, POr q r =>
      (p_dialectica_argument PDAbelard q *
       p_dialectica_argument PDAbelard r)%type
  | PDEloise, PImp q r =>
      ((p_dialectica_argument PDEloise q ->
        p_dialectica_argument PDEloise r) *
       (p_dialectica_argument PDEloise q ->
        p_dialectica_argument PDAbelard r ->
        p_dialectica_argument PDAbelard q))%type
  | PDAbelard, PImp q r =>
      (p_dialectica_argument PDEloise q *
       p_dialectica_argument PDAbelard r)%type
  end.

Definition p_dialectica_witness {Atom : Type} (p : pformula Atom) : Type :=
  p_dialectica_argument PDEloise p.

Definition p_dialectica_counter {Atom : Type} (p : pformula Atom) : Type :=
  p_dialectica_argument PDAbelard p.

Fixpoint p_dialectica_realizes {Atom : Type} (V : Atom -> Prop)
    (p : pformula Atom) :
    p_dialectica_witness p -> p_dialectica_counter p -> Prop :=
  match p as p0 return
      p_dialectica_witness p0 -> p_dialectica_counter p0 -> Prop with
  | PAtom a => fun _ _ => V a
  | PFalsum => fun _ _ => False
  | PAnd q r => fun witness counter =>
      match counter with
      | inl cq => @p_dialectica_realizes Atom V q (fst witness) cq
      | inr cr => @p_dialectica_realizes Atom V r (snd witness) cr
      end
  | POr q r => fun witness counter =>
      match witness with
      | inl wq => @p_dialectica_realizes Atom V q wq (fst counter)
      | inr wr => @p_dialectica_realizes Atom V r wr (snd counter)
      end
  | PImp q r => fun witness counter =>
      @p_dialectica_realizes Atom V q (fst counter)
        ((snd witness) (fst counter) (snd counter)) ->
      @p_dialectica_realizes Atom V r ((fst witness) (fst counter))
        (snd counter)
  end.

Arguments p_dialectica_realizes {Atom} V p _ _.

Definition p_dialectica_valid {Atom : Type} (p : pformula Atom) : Prop :=
  exists witness : p_dialectica_witness p,
    forall (V : Atom -> Prop) (counter : p_dialectica_counter p),
      p_dialectica_realizes V p witness counter.

Definition p_dialectica_not_valid {Atom : Type} (p : pformula Atom) : Prop :=
  forall witness : p_dialectica_witness p,
    exists (V : Atom -> Prop) (counter : p_dialectica_counter p),
      ~ p_dialectica_realizes V p witness counter.

Lemma p_dialectica_not_valid_iff :
  forall (Atom : Type) (p : pformula Atom),
    ~ p_dialectica_valid p <-> p_dialectica_not_valid p.
Proof.
  intros Atom p; split.
  - intros Hnot witness.
    assert (HVC : ~ forall (V : Atom -> Prop)
      (counter : p_dialectica_counter p),
      p_dialectica_realizes V p witness counter).
    { intro Hall. apply Hnot. now exists witness. }
    apply not_all_ex_not in HVC. destruct HVC as [V HV].
    apply not_all_ex_not in HV. destruct HV as [counter Hcounter].
    now exists V, counter.
  - intros Hnot [witness Hall].
    destruct (Hnot witness) as [V [counter Hcounter]].
    exact (Hcounter (Hall V counter)).
Qed.

Lemma p_dialectica_realizes_falsum :
  forall (Atom : Type) (V : Atom -> Prop)
         (w : p_dialectica_witness (@PFalsum Atom))
         (c : p_dialectica_counter (@PFalsum Atom)),
    ~ p_dialectica_realizes V PFalsum w c.
Proof. intros; exact (fun H => H). Qed.

Lemma p_dialectica_realizes_atom :
  forall (Atom : Type) (V : Atom -> Prop) a
         (w : p_dialectica_witness (PAtom a))
         (c : p_dialectica_counter (PAtom a)),
    p_dialectica_realizes V (PAtom a) w c <-> V a.
Proof. reflexivity. Qed.

Lemma p_dialectica_realizes_and_left :
  forall (Atom : Type) (V : Atom -> Prop) p q
         (w : p_dialectica_witness (PAnd p q))
         (c : p_dialectica_counter p),
    p_dialectica_realizes V (PAnd p q) w (inl c) <->
    p_dialectica_realizes V p (fst w) c.
Proof. reflexivity. Qed.

Lemma p_dialectica_realizes_and_right :
  forall (Atom : Type) (V : Atom -> Prop) p q
         (w : p_dialectica_witness (PAnd p q))
         (c : p_dialectica_counter q),
    p_dialectica_realizes V (PAnd p q) w (inr c) <->
    p_dialectica_realizes V q (snd w) c.
Proof. reflexivity. Qed.

Lemma p_dialectica_realizes_or_left :
  forall (Atom : Type) (V : Atom -> Prop) p q
         (w : p_dialectica_witness p)
         (c : p_dialectica_counter (POr p q)),
    p_dialectica_realizes V (POr p q) (inl w) c <->
    p_dialectica_realizes V p w (fst c).
Proof. reflexivity. Qed.

Lemma p_dialectica_realizes_or_right :
  forall (Atom : Type) (V : Atom -> Prop) p q
         (w : p_dialectica_witness q)
         (c : p_dialectica_counter (POr p q)),
    p_dialectica_realizes V (POr p q) (inr w) c <->
    p_dialectica_realizes V q w (snd c).
Proof. reflexivity. Qed.

Lemma p_dialectica_realizes_imp :
  forall (Atom : Type) (V : Atom -> Prop) p q
         (w : p_dialectica_witness (PImp p q))
         (c : p_dialectica_counter (PImp p q)),
    p_dialectica_realizes V (PImp p q) w c <->
    (p_dialectica_realizes V p (fst c)
       ((snd w) (fst c) (snd c)) ->
     p_dialectica_realizes V q ((fst w) (fst c)) (snd c)).
Proof. reflexivity. Qed.

Lemma p_dialectica_realizes_top :
  forall (Atom : Type) (V : Atom -> Prop)
         (w : p_dialectica_witness (@ptop Atom))
         (c : p_dialectica_counter (@ptop Atom)),
    p_dialectica_realizes V ptop w c.
Proof. intros Atom V w [u c]; exact (fun H => H). Qed.

Lemma p_dialectica_realizes_neg :
  forall (Atom : Type) (V : Atom -> Prop) p
         (w : p_dialectica_witness (pneg p))
         (c : p_dialectica_counter (pneg p)),
    p_dialectica_realizes V (pneg p) w c <->
    ~ p_dialectica_realizes V p (fst c)
        ((snd w) (fst c) (snd c)).
Proof. reflexivity. Qed.

Theorem p_dialectica_valid_identity :
  forall (Atom : Type) (p : pformula Atom),
    p_dialectica_valid (PImp p p).
Proof.
  intros Atom p.
  exists (fun w => w, fun _ c => c).
  intros V [w c]; cbn. tauto.
Qed.

Theorem p_dialectica_excluded_middle_not_valid :
  forall (Atom : Type) (a : Atom),
    p_dialectica_not_valid (POr (PAtom a) (pneg (PAtom a))).
Proof.
  intros Atom a [w | w].
  - exists (fun _ => False), (tt, (tt, tt)). cbn. tauto.
  - exists (fun _ => True), (tt, (tt, tt)). cbn. tauto.
Qed.
