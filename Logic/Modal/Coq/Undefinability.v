(**
  Irreflexivity is not definable by a basic modal formula.

  The proof is Foundation/Modal/Kripke/Undefinability.lean's two-world to
  one-world bounded-morphism argument.  Booleans make the back witness
  [negb x] explicit, so the entire theorem is constructive.
*)

From Stdlib Require Import Bool.Bool.
From FoundationModal Require Import Syntax Kripke Preservation.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition irreflexive (F : frame) : Prop :=
  forall x, ~ Rel F x x.

Definition two_cycle_frame : frame :=
  {| World := bool;
     Rel := fun x y => x <> y |}.

Definition reflexive_singleton_frame : frame :=
  {| World := unit;
     Rel := fun x y => x = y |}.

Lemma two_cycle_irreflexive : irreflexive two_cycle_frame.
Proof. intros x H; exact (H eq_refl). Qed.

Lemma reflexive_singleton_not_irreflexive :
  ~ irreflexive reflexive_singleton_frame.
Proof.
  intro H. exact (H tt eq_refl).
Qed.

Definition collapse_p_morphism :
  @p_morphism two_cycle_frame reflexive_singleton_frame.
Proof.
  refine {| pmap := fun _ : World two_cycle_frame =>
                       (tt : World reflexive_singleton_frame) |}.
  - intros; reflexivity.
  - intros x z _. destruct z.
    exists (negb x); split; [reflexivity |].
    destruct x; discriminate.
Defined.

Lemma collapse_surjective :
  forall z, exists x, pmap collapse_p_morphism x = z.
Proof.
  intro z; destruct z. exists false; reflexivity.
Qed.

Theorem irreflexivity_not_modally_definable :
  forall AtomType : Type,
    ~ exists p : formula AtomType,
        forall F : frame, irreflexive F <-> valid F p.
Proof.
  intros AtomType [p Hdefines].
  assert (Htwo : valid two_cycle_frame p).
  { apply (proj1 (Hdefines two_cycle_frame)).
    exact two_cycle_irreflexive. }
  assert (Hone : valid reflexive_singleton_frame p).
  { eapply valid_of_surjective_p_morphism.
    - exact collapse_surjective.
    - exact Htwo. }
  apply reflexive_singleton_not_irreflexive.
  apply (proj2 (Hdefines reflexive_singleton_frame)).
  exact Hone.
Qed.
