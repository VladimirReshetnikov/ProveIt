(**
  Unnecessitation for GL.

  This module ports the theorem surface of Foundation's pinned
  [Modal/Kripke/Logic/GL/Unnecessitation.lean].  The key semantic argument
  starts with a finite rooted countermodel to [boxdot p -> q].  Adding one
  fresh root turns it into a finite rooted countermodel to [box p -> box q]:
  [boxdot p] at the old root makes [p] true at every original world, while
  failure of [q] at that root witnesses failure of [box q] at the new one.

  The proof reuses the independently checked finite rooted countermodel
  theorem for GL and the root-extension construction.  No proof-theoretic
  rule is postulated.
*)

From Stdlib Require Import Arith.PeanoNat Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Kripke LogicInfrastructure NormalHilbert FrameTransformations
  GLGrzDerivations CanonicalGL.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Foundation [imply_boxdot_plain_of_imply_box_box]. *)
Theorem imply_boxdot_plain_of_imply_box_box :
  forall p q : formula nat,
    GL_proves (Imp (Box p) (Box q)) ->
    GL_proves (Imp (Boxdot p) q).
Proof.
  intros p q Hbox_imp.
  apply NNPP. intro Hboxdot_imp.
  destruct (GL_unprovable_exists_finite_rooted_countermodel Hboxdot_imp)
    as [F [V [r [Hfinite [Htrans [Hirr [Hroot Hcounter]]]]]]].
  set (one_positive := Nat.lt_0_succ 0).
  set (E := extend_root_frame F 1).
  set (VE := extend_root_valuation V r 1).
  set (e := extend_root_top F 1 one_positive).

  assert (Hold :
    satisfies F V r (Boxdot p) /\ ~ satisfies F V r q).
  { simpl in Hcounter. tauto. }
  destruct Hold as [Hboxdot_p Hnot_q].
  destruct (proj1 (@satisfies_and nat F V r p (Box p)) Hboxdot_p)
    as [Hp Hbox_p].

  assert (Hextended_counter :
    ~ satisfies E VE e (Imp (Box p) (Box q))).
  {
    intro Himp.
    assert (Hnew_box_p : satisfies E VE e (Box p)).
    {
      intros x Hex.
      destruct (@extend_root_one_successor_is_original F x Hex)
        as [y ->].
      apply (proj2 (@extend_root_embedded_truth nat F V r 1 y p)).
      destruct (classic (y = r)) as [-> | Hneq].
      - exact Hp.
      - apply Hbox_p, Hroot. exact Hneq.
    }
    pose proof (Himp Hnew_box_p) as Hnew_box_q.
    apply Hnot_q.
    apply (proj1 (@extend_root_embedded_truth nat F V r 1 r q)).
    apply Hnew_box_q.
    unfold E, e, one_positive.
    apply extend_root_rel_original_root; exact Hroot.
  }

  assert (Hextended_unprovable :
    ~ GL_proves (Imp (Box p) (Box q))).
  {
    apply (proj2
      (GL_unprovable_iff_exists_finite_rooted_countermodel
        (Imp (Box p) (Box q)))).
    exists E, VE, e. repeat split.
    - unfold E. now apply extend_root_finite.
    - unfold E. now apply extend_root_transitive.
    - unfold E. now apply extend_root_irreflexive.
    - unfold E, e, one_positive. apply extend_root_top_is_root.
    - exact Hextended_counter.
  }
  exact (Hextended_unprovable Hbox_imp).
Qed.

(** Foundation [unnecessitation!]. *)
Theorem GL_unnecessitation :
  forall p : formula nat, GL_proves (Box p) -> GL_proves p.
Proof.
  intros p Hbox_p.
  assert (Hbox_top_imp : GL_proves (Imp (Box Top) (Box p))).
  {
    apply (logic_imply_intro GL_classical_logic).
    exact Hbox_p.
  }
  pose proof
    (imply_boxdot_plain_of_imply_box_box
      (p := Top) (q := p) Hbox_top_imp) as Hboxdot_top_imp.
  apply (Np_mp Hboxdot_top_imp).
  unfold Boxdot.
  apply (logic_and_intro GL_classical_logic).
  - apply logic_mem_top. exact GL_classical_logic.
  - apply Np_nec. apply logic_mem_top. exact GL_classical_logic.
Qed.

(** Predicate-valued analogue of Foundation's [Entailment.Unnecessitation]
    class, and the checked GL inhabitant corresponding to its instance. *)
Definition logic_unnecessitation {AtomType : Type}
    (L : modal_logic_set AtomType) : Prop :=
  forall p, L (Box p) -> L p.

Definition GL_unnecessitation_instance :
  logic_unnecessitation (@GL_proves nat) :=
  GL_unnecessitation.

(** Source-facing theorem alias. *)
Definition unnecessitation_GL := GL_unnecessitation.
