(**
  Kripke correspondence for Loeb's axiom.

  This is an independent Coq proof of the main semantic results in
  Foundation/Modal/Kripke/AxiomL.lean.  Converse well-foundedness is stated
  in its maximal-element form, exactly the characterization used by the Lean
  proof: every inhabited predicate has an accessibility-maximal member.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import Syntax Axioms Kripke Correspondence.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition frame_converse_well_founded (F : frame) : Prop :=
  forall X : World F -> Prop,
    (exists x, X x) ->
    exists m, X m /\ forall y, X y -> ~ Rel F m y.

(** Transitivity and converse well-foundedness validate Loeb's schema. *)
Theorem valid_Loeb_of_transitive_cwf :
  forall AtomType (F : frame) (p : formula AtomType),
    frame_transitive F -> frame_converse_well_founded F ->
    valid F (Loeb p).
Proof.
  intros AtomType F p Htrans Hcwf V w Hstep x Rwx.
  apply NNPP; intro Hnotx.
  destruct (Hcwf (fun u => Rel F w u /\ ~ satisfies F V u p))
    as [m [[Rwm Hnotm] Hmax]].
  - exists x; auto.
  - apply Hnotm.
    apply (Hstep m Rwm).
    intros u Rmu.
    apply NNPP; intro Hnotu.
    apply (Hmax u).
    + split; [eapply Htrans; eauto | exact Hnotu].
    + exact Rmu.
Qed.

(** Atomic validity of Loeb's axiom forces transitivity. *)
Theorem transitive_of_valid_Loeb_atom :
  forall F : frame,
    valid F (Loeb (Atom 0)) -> frame_transitive F.
Proof.
  intros F Hvalid w v u Rwv Rvu.
  apply NNPP; intro HnotRwu.
  pose (V := (fun _ x => x <> v /\ x <> u) : valuation nat F).
  assert (Hantecedent :
    satisfies F V w (Box (Imp (Box (Atom 0)) (Atom 0)))).
  {
    intros x Rwx Hbox.
    split.
    - intro Hxv; subst x.
      specialize (Hbox u Rvu).
      exact (proj2 Hbox eq_refl).
    - intro Hxu; subst x. exact (HnotRwu Rwx).
  }
  pose proof (Hvalid V w Hantecedent) as Hbox.
  specialize (Hbox v Rwv).
  exact (proj1 Hbox eq_refl).
Qed.

(** Atomic validity also forces the maximal-element form of converse
    well-foundedness. *)
Theorem cwf_of_valid_Loeb_atom :
  forall F : frame,
    valid F (Loeb (Atom 0)) -> frame_converse_well_founded F.
Proof.
  intros F Hvalid X [x Hx].
  destruct (classic (exists m, X m /\ forall y, X y -> ~ Rel F m y))
    as [Hmax | Hno_max]; [exact Hmax |].
  exfalso.
  assert (Hnext : forall y, X y -> exists z, X z /\ Rel F y z).
  {
    intros y Hy.
    apply NNPP; intro Hnone.
    apply Hno_max. exists y; split; [exact Hy |].
    intros z Hz Ryz.
    apply Hnone. exists z; auto.
  }
  pose (V := (fun _ y => ~ X y) : valuation nat F).
  assert (Hantecedent :
    satisfies F V x (Box (Imp (Box (Atom 0)) (Atom 0)))).
  {
    intros y Rxy Hbox Hy.
    destruct (Hnext y Hy) as [z [Hz Ryz]].
    exact (Hbox z Ryz Hz).
  }
  pose proof (Hvalid V x Hantecedent) as Hbox.
  destruct (Hnext x Hx) as [y [Hy Rxy]].
  exact (Hbox y Rxy Hy).
Qed.

Theorem valid_Loeb_atom_iff_transitive_cwf :
  forall F : frame,
    valid F (Loeb (Atom 0)) <->
    frame_transitive F /\ frame_converse_well_founded F.
Proof.
  split.
  - intro H; split.
    + now apply transitive_of_valid_Loeb_atom.
    + now apply cwf_of_valid_Loeb_atom.
  - intros [Htrans Hcwf].
    exact (@valid_Loeb_of_transitive_cwf nat F (Atom 0) Htrans Hcwf).
Qed.
