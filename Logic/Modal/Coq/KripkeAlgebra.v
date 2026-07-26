(**
  The relational complex algebra of a Kripke frame.

  This file ports the mathematical content of Foundation's
  [Modal/Kripke/Algebra.lean].  A subset of worlds is represented directly
  by its membership predicate.  Equality in the complex algebra is therefore
  the extensional equivalence [world_set_equiv]; this avoids adding functional
  or propositional extensionality merely to package pointwise set laws.

  Formula evaluation in this algebra is atom-polymorphic.  Its defining
  theorem says exactly that membership in the algebraic value is Kripke
  satisfaction.  The three validity characterizations then follow without a
  separate induction or a quotient construction.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import Syntax Kripke.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The complex algebra carried by predicates on worlds *)

Definition world_set (F : frame) : Type := World F -> Prop.

Definition world_set_included {F : frame}
    (A B : world_set F) : Prop :=
  forall x, A x -> B x.

Definition world_set_equiv {F : frame}
    (A B : world_set F) : Prop :=
  forall x, A x <-> B x.

Definition world_set_top (F : frame) : world_set F :=
  fun _ => True.

Definition world_set_bottom (F : frame) : world_set F :=
  fun _ => False.

Definition world_set_complement {F : frame}
    (A : world_set F) : world_set F :=
  fun x => ~ A x.

Definition world_set_intersection {F : frame}
    (A B : world_set F) : world_set F :=
  fun x => A x /\ B x.

Definition world_set_union {F : frame}
    (A B : world_set F) : world_set F :=
  fun x => A x \/ B x.

Definition world_set_implication {F : frame}
    (A B : world_set F) : world_set F :=
  fun x => A x -> B x.

Definition complex_box {F : frame}
    (A : world_set F) : world_set F :=
  fun x => forall y, Rel F x y -> A y.

Definition complex_dia {F : frame}
    (A : world_set F) : world_set F :=
  fun x => exists y, Rel F x y /\ A y.

Lemma complex_dia_member :
  forall (F : frame) (A : world_set F) x,
    complex_dia A x <-> exists y, Rel F x y /\ A y.
Proof. reflexivity. Qed.

Lemma complex_box_member :
  forall (F : frame) (A : world_set F) x,
    complex_box A x <-> forall y, Rel F x y -> A y.
Proof. reflexivity. Qed.

Lemma world_set_equiv_refl :
  forall (F : frame) (A : world_set F), world_set_equiv A A.
Proof. intros F A x; reflexivity. Qed.

Lemma world_set_equiv_sym :
  forall (F : frame) (A B : world_set F),
    world_set_equiv A B -> world_set_equiv B A.
Proof. intros F A B H x; symmetry; apply H. Qed.

Lemma world_set_equiv_trans :
  forall (F : frame) (A B C : world_set F),
    world_set_equiv A B -> world_set_equiv B C -> world_set_equiv A C.
Proof.
  intros F A B C HAB HBC x.
  transitivity (B x); [apply HAB | apply HBC].
Qed.

Lemma world_set_equiv_antisymmetry :
  forall (F : frame) (A B : world_set F),
    world_set_included A B ->
    world_set_included B A ->
    world_set_equiv A B.
Proof. intros F A B HAB HBA x; split; auto. Qed.

Lemma complex_box_monotone :
  forall (F : frame) (A B : world_set F),
    world_set_included A B ->
    world_set_included (complex_box A) (complex_box B).
Proof.
  intros F A B HAB x Hbox y Rxy.
  apply HAB. exact (Hbox y Rxy).
Qed.

Lemma complex_dia_monotone :
  forall (F : frame) (A B : world_set F),
    world_set_included A B ->
    world_set_included (complex_dia A) (complex_dia B).
Proof.
  intros F A B HAB x [y [Rxy HA]].
  exists y; split; [exact Rxy | now apply HAB].
Qed.

Lemma complex_box_top :
  forall (F : frame),
    world_set_equiv (complex_box (F := F) (@world_set_top F))
      (@world_set_top F).
Proof.
  intros F x; split.
  - intros _. constructor.
  - intros _ y _. constructor.
Qed.

Lemma complex_box_intersection :
  forall (F : frame) (A B : world_set F),
    world_set_equiv
      (complex_box (world_set_intersection A B))
      (world_set_intersection (complex_box A) (complex_box B)).
Proof.
  intros F A B x; split.
  - intro H; split; intros y Rxy; apply (H y Rxy).
  - intros [HA HB] y Rxy. split; [now apply HA | now apply HB].
Qed.

Lemma complex_dia_dual :
  forall (F : frame) (A : world_set F),
    world_set_equiv
      (complex_dia A)
      (world_set_complement
        (complex_box (world_set_complement A))).
Proof.
  intros F A x; split.
  - intros [y [Rxy HA]] Hbox. exact (Hbox y Rxy HA).
  - intro Hnotbox. apply NNPP. intro Hnodia. apply Hnotbox.
    intros y Rxy HA. apply Hnodia. exists y; auto.
Qed.

(** * Algebraic formula evaluation *)

Fixpoint algebra_eval {AtomType : Type} {F : frame}
    (V : AtomType -> world_set F) (p : formula AtomType) : world_set F :=
  match p with
  | Atom a => V a
  | Bottom => @world_set_bottom F
  | Imp q r => world_set_implication (algebra_eval V q) (algebra_eval V r)
  | Box q => complex_box (algebra_eval V q)
  end.

Lemma algebra_eval_top :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F),
    world_set_equiv (algebra_eval V Top) (@world_set_top F).
Proof.
  intros AtomType F V x.
  cbn [Top Neg algebra_eval world_set_implication
    world_set_bottom world_set_top].
  unfold world_set_implication, world_set_bottom, world_set_top.
  tauto.
Qed.

Lemma algebra_eval_bottom :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F),
    world_set_equiv (algebra_eval V Bottom) (@world_set_bottom F).
Proof. intros AtomType F V x; reflexivity. Qed.

Lemma algebra_eval_imp :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F) (p q : formula AtomType),
    world_set_equiv (algebra_eval V (Imp p q))
      (world_set_implication (algebra_eval V p) (algebra_eval V q)).
Proof. intros AtomType F V p q x; reflexivity. Qed.

Lemma algebra_eval_neg :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F) (p : formula AtomType),
    world_set_equiv (algebra_eval V (Neg p))
      (world_set_complement (algebra_eval V p)).
Proof. intros AtomType F V p x; reflexivity. Qed.

Lemma algebra_eval_and :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F) (p q : formula AtomType),
    world_set_equiv (algebra_eval V (And p q))
      (world_set_intersection (algebra_eval V p) (algebra_eval V q)).
Proof.
  intros AtomType F V p q x; simpl.
  unfold world_set_intersection, world_set_implication,
    world_set_bottom.
  tauto.
Qed.

Lemma algebra_eval_or :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F) (p q : formula AtomType),
    world_set_equiv (algebra_eval V (Or p q))
      (world_set_union (algebra_eval V p) (algebra_eval V q)).
Proof.
  intros AtomType F V p q x; simpl.
  unfold world_set_union, world_set_implication, world_set_bottom.
  tauto.
Qed.

Lemma algebra_eval_box :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F) (p : formula AtomType),
    world_set_equiv (algebra_eval V (Box p))
      (complex_box (algebra_eval V p)).
Proof. intros AtomType F V p x; reflexivity. Qed.

Lemma algebra_eval_dia :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F) (p : formula AtomType),
    world_set_equiv (algebra_eval V (Dia p))
      (complex_dia (algebra_eval V p)).
Proof.
  intros AtomType F V p x. simpl.
  symmetry. apply (@complex_dia_dual F (algebra_eval V p) x).
Qed.

(** The source fixes natural-number atoms here.  The Coq statement is valid
    for every atom type. *)
Theorem algebraic_satisfies :
  forall (AtomType : Type) (F : frame)
      (V : AtomType -> world_set F) (x : World F)
      (p : formula AtomType),
    satisfies F V x p <-> algebra_eval V p x.
Proof.
  intros AtomType F V x p; revert x.
  induction p as [a | | p IHp q IHq | p IHp]; intro x; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHp, IHq. reflexivity.
  - split; intros H y Rxy.
    + apply (proj1 (IHp y)). exact (H y Rxy).
    + apply (proj2 (IHp y)). exact (H y Rxy).
Qed.

(** * Validity as order and equality in the complex algebra *)

Theorem algebraic_valid_imp :
  forall (AtomType : Type) (F : frame) (p q : formula AtomType),
    valid F (Imp p q) <->
    forall V : AtomType -> world_set F,
      world_set_included (algebra_eval V p) (algebra_eval V q).
Proof.
  intros AtomType F p q; split.
  - intros H V x Hp.
    apply (proj1 (@algebraic_satisfies AtomType F V x q)).
    apply (H V x).
    now apply (proj2 (@algebraic_satisfies AtomType F V x p)).
  - intros H V x Hp.
    apply (proj2 (@algebraic_satisfies AtomType F V x q)).
    apply (H V x).
    now apply (proj1 (@algebraic_satisfies AtomType F V x p)).
Qed.

Theorem algebraic_valid_iff :
  forall (AtomType : Type) (F : frame) (p q : formula AtomType),
    valid F (Iff p q) <->
    forall V : AtomType -> world_set F,
      world_set_equiv (algebra_eval V p) (algebra_eval V q).
Proof.
  intros AtomType F p q; split.
  - intros H V x. pose proof (H V x) as Hx.
    apply (proj1 (@satisfies_iff AtomType F V x p q)) in Hx.
    split; intro Hp.
    + apply (proj1 (@algebraic_satisfies AtomType F V x q)).
      apply (proj1 Hx).
      now apply (proj2 (@algebraic_satisfies AtomType F V x p)).
    + apply (proj1 (@algebraic_satisfies AtomType F V x p)).
      apply (proj2 Hx).
      now apply (proj2 (@algebraic_satisfies AtomType F V x q)).
  - intros H V x.
    apply (proj2 (@satisfies_iff AtomType F V x p q)).
    specialize (H V x). split; intro Hp.
    + apply (proj2 (@algebraic_satisfies AtomType F V x q)).
      apply (proj1 H).
      now apply (proj1 (@algebraic_satisfies AtomType F V x p)).
    + apply (proj2 (@algebraic_satisfies AtomType F V x p)).
      apply (proj2 H).
      now apply (proj1 (@algebraic_satisfies AtomType F V x q)).
Qed.

Theorem algebraic_valid :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    valid F p <->
    forall V : AtomType -> world_set F,
      world_set_equiv (algebra_eval V p) (@world_set_top F).
Proof.
  intros AtomType F p; split.
  - intros H V x; split.
    + intro Hvalue. constructor.
    + intro Htop.
      apply (proj1 (@algebraic_satisfies AtomType F V x p)).
      exact (H V x).
  - intros H V x.
    apply (proj2 (@algebraic_satisfies AtomType F V x p)).
    apply (proj2 (H V x)). constructor.
Qed.
