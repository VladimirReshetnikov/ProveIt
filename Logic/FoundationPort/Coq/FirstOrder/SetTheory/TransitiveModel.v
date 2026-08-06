(** Well-founded induction on membership submodels.

    Foundation specializes this construction to subsets of its concrete
    universe.  The induction argument only uses well-foundedness of ambient
    membership, so it is stated here for every membership structure and every
    carrier predicate.  No transitivity or closure hypothesis on the
    predicate is needed for well-foundedness of the induced relation. *)

From Stdlib Require Import Logic.Classical_Prop Wellfounded.Inverse_Image.
From Foundation.FirstOrder.SetTheory Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition membership_well_founded (m : membership_structure) : Prop :=
  well_founded (@membership_rel m).

Definition transitive_model (m : membership_structure)
    (U : membership_carrier m -> Prop) : membership_structure :=
  membership_submodel m U.

Arguments transitive_model m U : clear implicits.

(** Generic relation lemma factored from the membership specialization. *)
Lemma well_founded_predicate_subtype : forall
    (A : Type) (R : A -> A -> Prop) (U : A -> Prop),
  well_founded R ->
  well_founded (fun x y : {z : A | U z} => R (proj1_sig x) (proj1_sig y)).
Proof.
  intros A R U Hwf.
  exact (wf_inverse_image {z : A | U z} A R (@proj1_sig A U) Hwf).
Qed.

Lemma transitive_model_well_founded : forall m U,
  membership_well_founded m ->
  membership_well_founded (transitive_model m U).
Proof.
  intros m U Hwf. unfold membership_well_founded, transitive_model,
    membership_submodel. simpl.
  apply well_founded_predicate_subtype. exact Hwf.
Qed.

Theorem membership_well_founded_induction : forall m,
  membership_well_founded m ->
  forall (P : membership_carrier m -> Prop),
    (forall x,
      (forall y, membership_rel y x -> P y) -> P x) ->
    forall x, P x.
Proof.
  intros m Hwf P Hstep.
  exact (@well_founded_ind (membership_carrier m) (@membership_rel m)
    Hwf P Hstep).
Qed.

(** Source-shaped induction on the subtype model. *)
Theorem transitive_model_induction : forall m U,
  membership_well_founded m ->
  forall (P : membership_carrier (transitive_model m U) -> Prop),
    (forall x,
      (forall y, @membership_rel (transitive_model m U) y x -> P y) ->
      P x) ->
    forall x, P x.
Proof.
  intros m U Hwf P Hstep.
  apply (membership_well_founded_induction
    (transitive_model_well_founded (m := m) (U := U) Hwf)).
  exact Hstep.
Qed.

(** Expanded ambient-membership form, convenient when a proof should not
    mention the induced structure explicitly. *)
Corollary transitive_model_induction_ambient : forall m U,
  membership_well_founded m ->
  forall (P : membership_carrier (transitive_model m U) -> Prop),
    (forall x,
      (forall y,
        @membership_rel m (proj1_sig y) (proj1_sig x) -> P y) ->
      P x) ->
    forall x, P x.
Proof.
  intros m U Hwf P Hstep.
  apply (transitive_model_induction (m := m) (U := U) Hwf).
  exact Hstep.
Qed.

(** A relation-generic version of Foundation's
    [Universe.minimal_exists_of_isNonempty].  The proof starts with an
    arbitrary member of the set and repeatedly descends to a member of that
    member when one exists.  The only nonconstructive step is the source's
    classical choice between having such a predecessor and not having one;
    no extensionality, transitivity, or set-construction axiom is required. *)
Theorem membership_minimal_of_nonempty : forall m,
  membership_well_founded m ->
  forall S : membership_carrier m,
    set_model_is_nonempty S ->
    exists z, membership_rel z S /\
      forall x, membership_rel x S -> ~ membership_rel x z.
Proof.
  intros m Hwf S HS.
  destruct HS as [x0 HxS].
  assert (Hmin :
      forall x, membership_rel x S ->
        exists z, membership_rel z S /\
          forall y, membership_rel y S -> ~ membership_rel y z).
  {
    apply (@well_founded_ind
      (membership_carrier m) (@membership_rel m) Hwf
      (fun x => membership_rel x S ->
        exists z, membership_rel z S /\
          forall y, membership_rel y S -> ~ membership_rel y z)).
    intros x1 IH HxS'.
    destruct (classic (exists y,
      membership_rel y x1 /\ membership_rel y S)) as [Hpred | Hnone].
    - destruct Hpred as [y [Hyx HyS]].
      exact (IH y Hyx HyS).
    - exists x1. split; [exact HxS' |].
      intros y HyS Hyx.
      apply Hnone. exists y. split; assumption.
  }
  exact (Hmin x0 HxS).
Qed.

Print Assumptions well_founded_predicate_subtype.
Print Assumptions transitive_model_induction.
Print Assumptions transitive_model_induction_ambient.
Print Assumptions membership_minimal_of_nonempty.
