(**
  Canonical completeness for S4.4 (S4 plus Sobocinski's Point4 axiom).

  This module ports the complete theorem surface of the pinned Foundation
  file [Modal/Kripke/Logic/S4Point4.lean], together with the generic
  canonical-frame theorem from [Modal/Kripke/AxiomPoint4.lean].  The local
  name [S4Point4_axiom_schema] is extensionally the Point4 schema used by
  Foundation; it is deliberately distinct from the earlier compatibility
  schema in [CanonicalTrivVer].

  The canonical proof follows the separating-formula argument upstream.  A
  formula distinguishing the predecessor from one successor is disjoined
  with an arbitrary boxed formula at the other successor.  Point4 promotes
  that disjunction to a box at the predecessor, and the separator can then
  be eliminated at the first successor.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  Root Filtration NormalHilbert CanonicalK CanonicalExtensions CanonicalPoint2
  CanonicalCombinations Boxdot CanonicalPoint3.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Schema, calculus, and frames *)

Definition S4Point4_axiom_schema : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = Point4 q.

Definition S4Point4_schema : modal_axiom_schema :=
  schema_union S4_schema S4Point4_axiom_schema.

Definition S4Point4_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves S4Point4_schema AtomType.

Lemma S4Point4_axiom_schema_substitution_closed :
  schema_substitution_closed S4Point4_axiom_schema.
Proof.
  intros A B sigma p [q ->].
  exists (substitute sigma q). reflexivity.
Qed.

Lemma S4Point4_schema_substitution_closed :
  schema_substitution_closed S4Point4_schema.
Proof.
  apply schema_union_substitution_closed.
  - apply schema_union_substitution_closed.
    + exact schema_T_substitution_closed.
    + exact schema_Four_substitution_closed.
  - exact S4Point4_axiom_schema_substitution_closed.
Qed.

Definition S4Point4_frame_class (F : frame) : Prop :=
  frame_reflexive F /\ frame_transitive F /\ frame_sobocinski F.

Lemma S4Point4_frame_is_S4Point3 :
  forall F,
    S4Point4_frame_class F -> S4Point3_frame_class F.
Proof.
  intros F [HR [HT HSob]]. repeat split; try assumption.
  now apply sobocinski_piecewise_strongly_connected.
Qed.

(** * Soundness and consistency *)

Lemma S4Point4_axiom_schema_valid_on_sobocinski :
  forall F,
    frame_sobocinski F ->
    schema_valid_on_frame S4Point4_axiom_schema F.
Proof.
  intros F HSob AtomType p [q ->].
  now apply valid_Point4_of_sobocinski.
Qed.

Theorem S4Point4_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F -> frame_transitive F -> frame_sobocinski F ->
    S4Point4_proves p -> valid F p.
Proof.
  intros AtomType F p HR HT HSob Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  apply schema_union_valid_on_frame.
  - apply schema_union_valid_on_frame.
    + now apply schema_T_valid_on_reflexive.
    + now apply schema_Four_valid_on_transitive.
  - now apply S4Point4_axiom_schema_valid_on_sobocinski.
Qed.

Theorem S4Point4_is_consistent :
  forall AtomType, ~ @S4Point4_proves AtomType Bottom.
Proof.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := S4Point4_schema) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_union_valid_on_frame.
    + apply schema_union_valid_on_frame.
      * apply schema_T_valid_on_reflexive.
        exact reflexive_singleton_reflexive.
      * apply schema_Four_valid_on_transitive.
        exact reflexive_singleton_transitive.
    + apply S4Point4_axiom_schema_valid_on_sobocinski.
      intros [] [] [] Hneq _ _. exfalso. apply Hneq. reflexivity.
Qed.

(** * Propositional-modal support for canonicality *)

Lemma normal_proves_point4_box_or_right :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp (Box q) (Box (Or p q))).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hbox u Rwu.
  apply (proj2 (@satisfies_or nat F V u p q)).
  right. exact (Hbox u Rwu).
Qed.

Lemma normal_proves_point4_or_left :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp p (Or p q)).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hp.
  apply (proj2 (@satisfies_or nat F V w p q)). now left.
Qed.

Lemma normal_proves_point4_or_neg_left :
  forall Ax (p q : formula nat),
    normal_proves Ax (Imp (Or p q) (Imp (Neg p) q)).
Proof.
  intros Ax p q. apply normal_proves_of_valid_on_all_frames.
  intros F V w Hor Hneg.
  destruct (proj1 (@satisfies_or nat F V w p q) Hor) as [Hp | Hq].
  - exfalso. exact (Hneg Hp).
  - exact Hq.
Qed.

(** Point4 is canonical for every normal extension containing all of its
    substitution instances. *)
Theorem normal_canonical_sobocinski_of_schema_Point4 :
  forall Ax,
    schema_included S4Point4_axiom_schema Ax ->
    frame_sobocinski (normal_canonical_frame Ax).
Proof.
  intros Ax HPoint4 X Y Z Hneq HXY HXZ p HboxpZ.
  destruct (@normal_mct_separator Ax X Y Hneq)
    as [d [HdX HnegdY]].
  assert (HboxOrZ : normal_mct_mem Z (Box (Or d p))).
  {
    apply normal_mct_derivable_mem. eapply ND_mp.
    - apply ND_theorem. apply normal_proves_point4_box_or_right.
    - apply ND_assumption. exact HboxpZ.
  }
  assert (HdiaBoxOrX : normal_mct_mem X (Dia (Box (Or d p)))).
  {
    now apply normal_canonical_predecessor_dia_mem with (N := Z).
  }
  assert (HPoint4X : normal_mct_mem X (Point4 (Or d p))).
  {
    apply normal_mct_derivable_mem. apply ND_theorem. apply Np_extra.
    apply HPoint4. exists (Or d p). reflexivity.
  }
  assert (HlocalX : normal_mct_mem X (Imp (Or d p) (Box (Or d p)))).
  {
    apply normal_mct_derivable_mem. eapply ND_mp.
    - apply ND_assumption. exact HPoint4X.
    - apply ND_assumption. exact HdiaBoxOrX.
  }
  assert (HorX : normal_mct_mem X (Or d p)).
  {
    apply normal_mct_derivable_mem. eapply ND_mp.
    - apply ND_theorem. apply normal_proves_point4_or_left.
    - apply ND_assumption. exact HdX.
  }
  assert (HboxOrX : normal_mct_mem X (Box (Or d p))).
  {
    apply normal_mct_derivable_mem. eapply ND_mp.
    - apply ND_assumption. exact HlocalX.
    - apply ND_assumption. exact HorX.
  }
  pose proof (HXY (Or d p) HboxOrX) as HorY.
  apply normal_mct_derivable_mem. eapply ND_mp.
  - eapply ND_mp.
    + apply ND_theorem. apply normal_proves_point4_or_neg_left.
    + apply ND_assumption. exact HorY.
  - apply ND_assumption. exact HnegdY.
Qed.

(** * Canonicality and completeness *)

Lemma S4Point4_canonical_frame :
  S4Point4_frame_class (normal_canonical_frame S4Point4_schema).
Proof.
  repeat split.
  - apply normal_canonical_reflexive_of_schema_T.
    intros A p Hp. left. now left.
  - apply normal_canonical_transitive_of_schema_Four.
    intros A p Hp. left. now right.
  - apply normal_canonical_sobocinski_of_schema_Point4.
    intros A p Hp. now right.
Qed.

Theorem S4Point4_complete :
  forall p : formula nat,
    normal_valid_on_class S4Point4_frame_class p -> S4Point4_proves p.
Proof.
  unfold S4Point4_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := S4Point4_schema) (C := S4Point4_frame_class)).
  - exact (@S4Point4_is_consistent nat).
  - exact S4Point4_canonical_frame.
Qed.

Theorem S4Point4_sound_complete :
  forall p : formula nat,
    S4Point4_proves p <->
    normal_valid_on_class S4Point4_frame_class p.
Proof.
  intro p; split.
  - intros Hp F [HR [HT HSob]].
    now apply S4Point4_proves_sound_on_frame.
  - apply S4Point4_complete.
Qed.

(** * S4.3 is strictly weaker than S4.4 *)

Theorem S4Point3_weaker_than_S4Point4 :
  forall p : formula nat, S4Point3_proves p -> S4Point4_proves p.
Proof.
  intros p Hp. apply S4Point4_complete.
  intros F HF.
  destruct (S4Point4_frame_is_S4Point3 HF) as [HR [HT HC]].
  now apply S4Point3_proves_sound_on_frame.
Qed.

Inductive point4_three_world : Type :=
| P40 | P41 | P42.

Inductive point4_three_chain_relation
    : point4_three_world -> point4_three_world -> Prop :=
| point4_R00 : point4_three_chain_relation P40 P40
| point4_R01 : point4_three_chain_relation P40 P41
| point4_R02 : point4_three_chain_relation P40 P42
| point4_R11 : point4_three_chain_relation P41 P41
| point4_R12 : point4_three_chain_relation P41 P42
| point4_R22 : point4_three_chain_relation P42 P42.

Definition point4_three_chain_frame : frame :=
  {| World := point4_three_world;
     Rel := point4_three_chain_relation |}.

Lemma point4_three_chain_finite :
  finite_frame point4_three_chain_frame.
Proof.
  exists [P40; P41; P42]. intros []; simpl; auto.
Qed.

Lemma point4_three_chain_reflexive :
  frame_reflexive point4_three_chain_frame.
Proof. intros []; constructor. Qed.

Lemma point4_three_chain_transitive :
  frame_transitive point4_three_chain_frame.
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; constructor.
Qed.

Lemma point4_three_chain_strongly_connected :
  frame_strongly_connected point4_three_chain_frame.
Proof.
  intros x y. destruct x, y;
    try (left; constructor); right; constructor.
Qed.

Lemma point4_three_chain_piecewise_strongly_connected :
  frame_piecewise_strongly_connected point4_three_chain_frame.
Proof.
  intros x y z _ _. exact (point4_three_chain_strongly_connected y z).
Qed.

Lemma point4_three_chain_not_sobocinski :
  ~ frame_sobocinski point4_three_chain_frame.
Proof.
  intro HSob.
  pose proof (HSob P40 P41 P42 ltac:(discriminate)
    point4_R01 point4_R02) as H21.
  inversion H21.
Qed.

Theorem S4Point3_strictly_weaker_S4Point4 :
  normal_strictly_weaker S4Point3_proves S4Point4_proves.
Proof.
  split.
  - exact S4Point3_weaker_than_S4Point4.
  - exists (Point4 (Atom 0)); split.
    + apply Np_extra. right. exists (Atom 0). reflexivity.
    + intro HPoint3.
      pose proof (S4Point3_proves_sound_on_frame
        point4_three_chain_reflexive point4_three_chain_transitive
        point4_three_chain_piecewise_strongly_connected HPoint3) as Hvalid.
      apply point4_three_chain_not_sobocinski.
      now apply sobocinski_of_valid_Point4_atom.
Qed.
