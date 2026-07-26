(**
  Iterated independence from consistency in GL.

  This file ports the active theorem surface of Foundation's pinned
  [Modal/Logic/GL/Independency.lean].  The independence formula says that
  neither a sentence nor its negation is necessary.  Starting from GL's
  usual consistency sentence [~ box bottom], iterating that construction
  produces formulas for which GL proves neither side.

  The first obstruction has a particularly small semantic proof: on the
  irreflexive singleton every boxed formula is vacuously true, so no formula
  [~ box p] is GL-provable.  The negative half of the iteration uses the
  separately checked modal disjunction property and unnecessitation theorem,
  exactly as in the source development.  The two commented-out wrappers in
  Foundation are intentionally omitted; all five active lemmas are present.
*)

From FoundationModal Require Import
  Syntax HilbertK Kripke HilbertKSoundness NormalHilbert
  LogicInfrastructure GLGrzDerivations GLUnnecessitation
  GLModalDisjunction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Foundation [independency p] is [~ box p /\ ~ box ~p]. *)
Definition independency {AtomType : Type} (p : formula AtomType)
    : formula AtomType :=
  And (Neg (Box p)) (Neg (Box (Neg p))).

(** Foundation [higherIndependency]. *)
Fixpoint higher_independency {AtomType : Type}
    (p : formula AtomType) (n : nat) : formula AtomType :=
  match n with
  | 0 => p
  | S k => independency (higher_independency p k)
  end.

(** Camel-case source-facing alias. *)
Definition higherIndependency {AtomType : Type}
    (p : formula AtomType) (n : nat) : formula AtomType :=
  higher_independency p n.

(** Foundation [GL.unprovable_notbox].  This semantic proof is shorter than
    translating the source's detour through the classical fragment. *)
Theorem GL_unprovable_notbox :
  forall p : formula nat, ~ GL_proves (Neg (Box p)).
Proof.
  intros p Hnotbox.
  pose proof
    (GL_proves_sound_on_transitive_cwf_frame
      (F := irreflexive_singleton_frame) (p := Neg (Box p))
      irreflexive_singleton_transitive irreflexive_singleton_cwf
      Hnotbox) as Hvalid.
  specialize (Hvalid (fun _ _ => False) tt).
  apply Hvalid. intros u Hrel. contradiction.
Qed.

(** Foundation [GL.unprovable_independency]. *)
Theorem GL_unprovable_independency :
  forall p : formula nat, ~ GL_proves (independency p).
Proof.
  intros p Hindependent.
  apply (GL_unprovable_notbox (p := p)).
  eapply (logic_modus_ponens GL_classical_logic).
  - exact
      (@logic_and_elim_left_imp nat GL_proves GL_classical_logic
        (Neg (Box p)) (Neg (Box (Neg p)))).
  - exact Hindependent.
Qed.

(** The propositional step called [A!_of_ANNNN! $ ANN!_of_NK!] in the Lean
    proof: failure of independence gives a disjunction of boxes. *)
Lemma GL_proves_box_or_box_neg_of_not_independency :
  forall p : formula nat,
    GL_proves (Neg (independency p)) ->
    GL_proves (Or (Box p) (Box (Neg p))).
Proof.
  intros p Hnot_independent.
  eapply (logic_modus_ponens GL_classical_logic); [|exact Hnot_independent].
  apply (logic_classical_tautology GL_classical_logic).
  intro rho. unfold independency, And, Or, Neg; simpl; tauto.
Qed.

(** Foundation [GL.unprovable_not_independency_of_consistency]. *)
Theorem GL_unprovable_not_independency_of_consistency :
  ~ GL_proves
      (Neg (independency (Neg (Box (@Bottom nat))))).
Proof.
  intro Hnot_independent.
  pose proof
    (GL_proves_box_or_box_neg_of_not_independency
      (p := Neg (Box (@Bottom nat))) Hnot_independent) as Hdisjunction.
  destruct
    (GL_modal_disjunction
      (p := Neg (Box (@Bottom nat)))
      (q := Neg (Neg (Box (@Bottom nat)))) Hdisjunction)
    as [Hconsistency | Hdouble_neg_box_bottom].
  - exact (GL_unprovable_notbox (p := Bottom) Hconsistency).
  - apply (@GL_is_consistent nat).
    apply GL_unnecessitation.
    eapply Np_mp; [|exact Hdouble_neg_box_bottom].
    apply K_proves_normal, K_proves_dne.
Qed.

(** Foundation [GL.unprovable_higherIndependency_of_consistency]. *)
Theorem GL_unprovable_higher_independency_of_consistency :
  forall n : nat,
    ~ GL_proves
        (higher_independency (Neg (Box (@Bottom nat))) n).
Proof.
  intros [|n]; simpl.
  - apply GL_unprovable_notbox.
  - apply GL_unprovable_independency.
Qed.

(** Foundation [GL.unprovable_not_higherIndependency_of_consistency]. *)
Theorem GL_unprovable_not_higher_independency_of_consistency :
  forall n : nat,
    ~ GL_proves
        (Neg (higher_independency (Neg (Box (@Bottom nat))) n)).
Proof.
  induction n as [|n IH]; simpl.
  - intro Hdouble_neg_box_bottom.
    apply (@GL_is_consistent nat).
    apply GL_unnecessitation.
    eapply Np_mp; [|exact Hdouble_neg_box_bottom].
    apply K_proves_normal, K_proves_dne.
  - intro Hnot_independent.
    pose proof
      (GL_proves_box_or_box_neg_of_not_independency
        (p := higher_independency (Neg (Box (@Bottom nat))) n)
        Hnot_independent) as Hdisjunction.
    destruct
      (GL_modal_disjunction
        (p := higher_independency (Neg (Box (@Bottom nat))) n)
        (q := Neg (higher_independency
                    (Neg (Box (@Bottom nat))) n))
        Hdisjunction) as [Hpositive | Hnegative].
    + exact (GL_unprovable_higher_independency_of_consistency
               (n := n) Hpositive).
    + exact (IH Hnegative).
Qed.

(** Namespace-flattened source aliases. *)
Definition unprovable_notbox := GL_unprovable_notbox.
Definition unprovable_independency := GL_unprovable_independency.
Definition unprovable_not_independency_of_consistency :=
  GL_unprovable_not_independency_of_consistency.
Definition unprovable_higherIndependency_of_consistency :=
  GL_unprovable_higher_independency_of_consistency.
Definition unprovable_not_higherIndependency_of_consistency :=
  GL_unprovable_not_higher_independency_of_consistency.
