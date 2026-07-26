(**
  Derived entailment laws for GL and Grz.

  This file ports the active theorem surfaces of the pinned Foundation
  modules [Modal/Entailment/GL.lean] and [Modal/Entailment/Grz.lean] that are
  needed before their finite mini-canonical completeness proofs.  In
  particular, none of the results below appeals to GL or Grz completeness.

  The canonical developments in this repository use formulas over [nat], so
  the theorem statements follow that interface.  The proofs themselves use
  only the normal Hilbert rules, the indicated axiom schema, and ordinary
  classical propositional reasoning internal to the Hilbert calculus.

  Deliberately, this module does not import [Boxdot].  Consequently the
  syntactic proof that GL proves the boxdot translation of Grz can be used by
  that later layer without introducing an import cycle.
*)

From FoundationModal Require Import
  Syntax Axioms HilbertK NormalHilbert LogicInfrastructure
  FrameTransformations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Small normal-logic combinators *)

Lemma closed_normal_proves_propositional :
  forall Ax,
    schema_substitution_closed Ax ->
    forall p : formula nat,
      classical_tautology p -> normal_proves Ax p.
Proof.
  intros Ax Hclosed p Hp.
  pose proof (@normal_proves_logic_is_normal Ax Hclosed) as Hnormal.
  exact (@logic_classical_tautology nat (@normal_proves Ax nat)
    (quasi_classical (normal_quasi Hnormal)) p Hp).
Qed.

Lemma closed_normal_proves_imp_trans :
  forall Ax,
    schema_substitution_closed Ax ->
    forall p q r : formula nat,
      normal_proves Ax (Imp p q) ->
      normal_proves Ax (Imp q r) ->
      normal_proves Ax (Imp p r).
Proof.
  intros Ax Hclosed p q r Hpq Hqr.
  pose proof (@normal_proves_logic_is_normal Ax Hclosed) as Hnormal.
  exact (logic_imp_trans
    (quasi_classical (normal_quasi Hnormal)) Hpq Hqr).
Qed.

Lemma closed_normal_proves_under_mp :
  forall Ax,
    schema_substitution_closed Ax ->
    forall a p q : formula nat,
      normal_proves Ax (Imp a (Imp p q)) ->
      normal_proves Ax (Imp a p) ->
      normal_proves Ax (Imp a q).
Proof.
  intros Ax Hclosed a p q Hpq Hp.
  pose proof (@normal_proves_logic_is_normal Ax Hclosed) as Hnormal.
  exact (logic_under_mp
    (quasi_classical (normal_quasi Hnormal)) Hpq Hp).
Qed.

Lemma closed_normal_proves_box_regularity :
  forall Ax,
    schema_substitution_closed Ax ->
    forall p q : formula nat,
      normal_proves Ax (Imp p q) ->
      normal_proves Ax (Imp (Box p) (Box q)).
Proof.
  intros Ax Hclosed p q Hpq.
  exact (logic_box_regularity
    (@normal_proves_logic_is_normal Ax Hclosed) Hpq).
Qed.

Lemma closed_normal_proves_box_boxdot_to_boxdot_box :
  forall Ax,
    schema_substitution_closed Ax ->
    forall p : formula nat,
      normal_proves Ax (Imp (Box (Boxdot p)) (Boxdot (Box p))).
Proof.
  intros Ax Hclosed p.
  pose proof (@normal_proves_logic_is_normal Ax Hclosed) as Hnormal.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  unfold Boxdot.
  apply logic_imp_and_intro; [exact Hclass | |].
  - apply logic_box_regularity; [exact Hnormal |].
    now apply logic_and_elim_left_imp.
  - apply logic_box_regularity; [exact Hnormal |].
    now apply logic_and_elim_right_imp.
Qed.

(** * GL consequences *)

Definition GL_normal_logic : normal_logic (@GL_proves nat) :=
  @normal_proves_logic_is_normal schema_L schema_L_substitution_closed.

Definition GL_classical_logic : classical_logic (@GL_proves nat) :=
  quasi_classical (normal_quasi GL_normal_logic).

Lemma GL_proves_L :
  forall p : formula nat, GL_proves (L p).
Proof.
  intro p. apply Np_extra. exists p. reflexivity.
Qed.

(** Foundation [GL.axiomFour].  The crucial bridge

      box (boxdot p) -> boxdot (box p)

    is already a theorem of K.  Loeb at [boxdot p] then turns [box p] into
    [box (boxdot p)], whose right conjunct is [box (box p)]. *)
Theorem GL_proves_Four :
  forall p : formula nat, GL_proves (Four p).
Proof.
  intro p; unfold Four.
  assert (Hdrop :
    GL_proves (Imp p (Imp (Boxdot (Box p)) (Boxdot p)))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Boxdot, And, Neg; simpl; tauto. }
  assert (Hdistribute :
    GL_proves (Imp (Box (Boxdot p)) (Boxdot (Box p)))).
  { exact (closed_normal_proves_box_boxdot_to_boxdot_box
      schema_L_substitution_closed p). }
  assert (Hbridge :
    GL_proves (Imp p (Imp (Box (Boxdot p)) (Boxdot p)))).
  { assert (Hcompose : GL_proves
      (Imp (Imp p (Imp (Boxdot (Box p)) (Boxdot p)))
        (Imp (Imp (Box (Boxdot p)) (Boxdot (Box p)))
          (Imp p (Imp (Box (Boxdot p)) (Boxdot p)))))).
    { apply (logic_classical_tautology GL_classical_logic).
      intro rho. unfold Boxdot, And, Neg; simpl; tauto. }
    exact (Np_mp (Np_mp Hcompose Hdrop) Hdistribute). }
  assert (Hboxed :
    GL_proves
      (Imp (Box p)
        (Box (Imp (Box (Boxdot p)) (Boxdot p))))).
  { exact (logic_box_regularity GL_normal_logic Hbridge). }
  assert (Hloeb :
    GL_proves
      (Imp (Box (Imp (Box (Boxdot p)) (Boxdot p)))
        (Box (Boxdot p)))).
  { exact (GL_proves_L (Boxdot p)). }
  assert (Hto_boxdot :
    GL_proves (Imp (Box p) (Box (Boxdot p)))).
  { exact (logic_imp_trans GL_classical_logic Hboxed Hloeb). }
  assert (Helim :
    GL_proves (Imp (Box (Boxdot p)) (Box (Box p)))).
  { apply logic_box_regularity; [exact GL_normal_logic |].
    apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Boxdot, And, Neg; simpl; tauto. }
  exact (logic_imp_trans GL_classical_logic Hto_boxdot Helim).
Qed.

(** Two K4-style box/conjunction bridges used in the GL seed argument. *)
Theorem GL_proves_box_to_box_boxdot :
  forall p : formula nat,
    GL_proves (Imp (Box p) (Box (Boxdot p))).
Proof.
  intro p.
  pose proof (GL_proves_Four p) as Hfour.
  pose proof (logic_identity GL_classical_logic (Box p)) as Hid.
  pose proof
    (logic_imp_and_intro GL_classical_logic Hid Hfour) as Hpair.
  exact (logic_imp_trans GL_classical_logic Hpair
    (logic_box_and_collect GL_normal_logic p (Box p))).
Qed.

Theorem GL_proves_box_to_boxdot_box :
  forall p : formula nat,
    GL_proves (Imp (Box p) (Boxdot (Box p))).
Proof.
  intro p; unfold Boxdot.
  apply logic_imp_and_intro; [exact GL_classical_logic | |].
  - apply logic_identity; exact GL_classical_logic.
  - apply GL_proves_Four.
Qed.

Theorem GL_proves_box_boxdot_equivalence :
  forall p : formula nat,
    GL_proves (Iff (Box p) (Box (Boxdot p))).
Proof.
  intro p; unfold Iff.
  apply logic_and_intro; [exact GL_classical_logic | |].
  - apply GL_proves_box_to_box_boxdot.
  - apply logic_box_regularity; [exact GL_normal_logic |].
    apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Boxdot, And, Neg; simpl; tauto.
Qed.

Theorem GL_proves_box_boxdotbox_equivalence :
  forall p : formula nat,
    GL_proves (Iff (Box p) (Boxdot (Box p))).
Proof.
  intro p; unfold Iff.
  apply logic_and_intro; [exact GL_classical_logic | |].
  - apply GL_proves_box_to_boxdot_box.
  - apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Boxdot, And, Neg; simpl; tauto.
Qed.

Theorem GL_proves_boxdot_idempotent :
  forall p : formula nat,
    GL_proves (Imp (Boxdot p) (Boxdot (Boxdot p))).
Proof.
  intro p.
  change (GL_proves
    (Imp (Boxdot p) (And (Boxdot p) (Box (Boxdot p))))).
  apply logic_imp_and_intro; [exact GL_classical_logic | |].
  - apply logic_identity; exact GL_classical_logic.
  - assert (Hproj : GL_proves (Imp (Boxdot p) (Box p))).
    { apply (logic_classical_tautology GL_classical_logic).
      intro rho. unfold Boxdot, And, Neg; simpl; tauto. }
    exact (logic_imp_trans GL_classical_logic Hproj
      (GL_proves_box_to_box_boxdot p)).
Qed.

(** Foundation [GL.axiomHen] and [GL.axiomZ]. *)
Theorem GL_proves_Hen :
  forall p : formula nat, GL_proves (Hen p).
Proof.
  intro p; unfold Hen.
  assert (Hleft :
    GL_proves (Imp (Iff (Box p) p) (Imp (Box p) p))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Iff, And, Neg; simpl; tauto. }
  exact (logic_imp_trans GL_classical_logic
    (logic_box_regularity GL_normal_logic Hleft)
    (GL_proves_L p)).
Qed.

Theorem GL_proves_Z :
  forall p : formula nat, GL_proves (Z p).
Proof.
  intro p.
  assert (Hweak : GL_proves (Imp (L p) (Z p))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold L, Loeb, Z; simpl; tauto. }
  exact (Np_mp Hweak (GL_proves_L p)).
Qed.

(** Foundation [godel2]: the modalized second incompleteness equivalence. *)
Theorem GL_proves_godel2 :
  GL_proves
    (Iff (Neg (Box (@Bottom nat)))
         (Neg (Box (Neg (Box Bottom))))).
Proof.
  unfold Iff.
  apply logic_and_intro; [exact GL_classical_logic | |].
  - assert (HL :
      GL_proves
        (Imp (Box (Neg (Box (@Bottom nat)))) (Box Bottom))).
    { exact (GL_proves_L Bottom). }
    assert (Hcontra : GL_proves
      (Imp
        (Imp (Box (Neg (Box (@Bottom nat)))) (Box Bottom))
        (Imp (Neg (Box Bottom))
          (Neg (Box (Neg (Box Bottom))))))).
    { apply (logic_classical_tautology GL_classical_logic).
      intro rho. unfold Neg; simpl; tauto. }
    exact (Np_mp Hcontra HL).
  - assert (Hefq :
      GL_proves (Imp (@Bottom nat) (Neg (Box Bottom)))).
    { apply (logic_classical_tautology GL_classical_logic).
      intro rho. unfold Neg; simpl; tauto. }
    pose proof (logic_box_regularity GL_normal_logic Hefq) as Hbox.
    assert (Hcontra :
      GL_proves
        (Imp (Imp (Box (@Bottom nat)) (Box (Neg (Box Bottom))))
          (Imp (Neg (Box (Neg (Box Bottom))))
            (Neg (Box Bottom))))).
    { apply (logic_classical_tautology GL_classical_logic).
      intro rho. unfold Neg; simpl; tauto. }
    exact (Np_mp Hcontra Hbox).
Qed.

Corollary GL_proves_godel2_mp :
  GL_proves
    (Imp (Neg (Box (@Bottom nat)))
      (Neg (Box (Neg (Box Bottom))))).
Proof.
  assert (Helim : GL_proves
    (Imp
      (Iff (Neg (Box (@Bottom nat)))
        (Neg (Box (Neg (Box Bottom)))))
      (Imp (Neg (Box Bottom))
        (Neg (Box (Neg (Box Bottom))))))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Iff, And, Neg; simpl; tauto. }
  exact (Np_mp Helim GL_proves_godel2).
Qed.

Corollary GL_proves_godel2_mpr :
  GL_proves
    (Imp (Neg (Box (Neg (Box (@Bottom nat)))))
      (Neg (Box Bottom))).
Proof.
  assert (Helim : GL_proves
    (Imp
      (Iff (Neg (Box (@Bottom nat)))
        (Neg (Box (Neg (Box Bottom)))))
      (Imp (Neg (Box (Neg (Box Bottom))))
        (Neg (Box Bottom))))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Iff, And, Neg; simpl; tauto. }
  exact (Np_mp Helim GL_proves_godel2).
Qed.

(** The K-valid first half of Foundation [lem_boxdot_Grz_of_L]. *)
Lemma GL_proves_boxdot_Grz_antecedent :
  forall p : formula nat,
    let b := Imp p (Boxdot p) in
    let a := Imp (Boxdot b) p in
    GL_proves (Imp (Boxdot a) (Imp (Box b) p)).
Proof.
  intros p b a.
  apply (logic_classical_tautology GL_classical_logic).
  intro rho. unfold a, b, Boxdot, And, Neg; simpl; tauto.
Qed.

(** Foundation [boxdot_Grz_of_L], definitionally the boxdot translation of
    the Grz axiom.  This is the key axiom-instance proof for the syntactic
    Grz-to-GL boxdot translation. *)
Theorem GL_proves_boxdot_Grz :
  forall p : formula nat,
    let b := Imp p (Boxdot p) in
    let a := Imp (Boxdot b) p in
    GL_proves (Imp (Boxdot a) p).
Proof.
  intros p b a.
  assert (HKdist :
    GL_proves (Imp (Box a) (Imp (Box (Boxdot b)) (Box p)))).
  { assert (Hreg :
      GL_proves (Imp (Box a) (Box (Imp (Boxdot b) p)))).
    { apply logic_box_regularity; [exact GL_normal_logic |].
      apply logic_identity; exact GL_classical_logic. }
    exact (logic_imp_trans GL_classical_logic Hreg
      (quasi_modal_K (normal_quasi GL_normal_logic) (Boxdot b) p)). }
  assert (Hb_to_boxdot :
    GL_proves (Imp (Box b) (Box (Boxdot b)))).
  { apply GL_proves_box_to_box_boxdot. }
  assert (HKdist' :
    GL_proves (Imp (Box a) (Imp (Box b) (Box p)))).
  { assert (Hcompose : GL_proves
      (Imp (Imp (Box a) (Imp (Box (Boxdot b)) (Box p)))
        (Imp (Imp (Box b) (Box (Boxdot b)))
          (Imp (Box a) (Imp (Box b) (Box p)))))).
    { apply (logic_classical_tautology GL_classical_logic).
      intro rho. simpl; tauto. }
    exact (Np_mp (Np_mp Hcompose HKdist) Hb_to_boxdot). }
  assert (Hmake_b :
    GL_proves (Imp (Box a) (Imp (Box b) b))).
  { assert (Hconvert : GL_proves
      (Imp (Imp (Box a) (Imp (Box b) (Box p)))
        (Imp (Box a) (Imp (Box b) b)))).
    { apply (logic_classical_tautology GL_classical_logic).
      intro rho. unfold b, Boxdot, And, Neg; simpl; tauto. }
    exact (Np_mp Hconvert HKdist'). }
  assert (Hboxed_make_b :
    GL_proves (Imp (Box (Box a))
      (Box (Imp (Box b) b)))).
  { apply logic_box_regularity; [exact GL_normal_logic | exact Hmake_b]. }
  assert (Hfour_a : GL_proves (Imp (Box a) (Box (Box a)))).
  { apply GL_proves_Four. }
  assert (Hto_loeb_premise :
    GL_proves (Imp (Box a) (Box (Imp (Box b) b)))).
  { exact (logic_imp_trans GL_classical_logic Hfour_a Hboxed_make_b). }
  assert (Hloeb_b :
    GL_proves (Imp (Box (Imp (Box b) b)) (Box b))).
  { exact (GL_proves_L b). }
  assert (Hboxa_to_boxb : GL_proves (Imp (Box a) (Box b))).
  { exact (logic_imp_trans GL_classical_logic Hto_loeb_premise Hloeb_b). }
  assert (Hboxdota_to_boxb : GL_proves (Imp (Boxdot a) (Box b))).
  { assert (Hproj : GL_proves (Imp (Boxdot a) (Box a))).
    { apply (logic_classical_tautology GL_classical_logic).
      intro rho. unfold Boxdot, And, Neg; simpl; tauto. }
    exact (logic_imp_trans GL_classical_logic Hproj Hboxa_to_boxb). }
  exact (logic_under_mp GL_classical_logic
    (GL_proves_boxdot_Grz_antecedent p) Hboxdota_to_boxb).
Qed.

(** Exact source-facing form of Foundation [boxdot_Grz_of_L]. *)
Corollary GL_proves_boxdot_translated_Grz :
  forall p : formula nat,
    GL_proves (boxdot_translate (Grz p)).
Proof.
  intro p; change
    (GL_proves
      (Imp
        (Boxdot
          (Imp
            (Boxdot
              (Imp (boxdot_translate p)
                (Boxdot (boxdot_translate p))))
            (boxdot_translate p)))
        (boxdot_translate p))).
  exact (GL_proves_boxdot_Grz (boxdot_translate p)).
Qed.

(** Foundation's three GL lifting steps. *)
Theorem GL_proves_boxdot_boxdot_of_boxdot_plain :
  forall p q : formula nat,
    GL_proves (Imp (Boxdot p) q) ->
    GL_proves (Imp (Boxdot p) (Boxdot q)).
Proof.
  intros p q Hpq; unfold Boxdot at 2.
  apply logic_imp_and_intro; [exact GL_classical_logic | exact Hpq |].
  pose proof (logic_box_regularity GL_normal_logic Hpq) as Hboxed.
  assert (Hproj : GL_proves (Imp (Boxdot p) (Box p))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Boxdot, And, Neg; simpl; tauto. }
  exact (logic_imp_trans GL_classical_logic
    (logic_imp_trans GL_classical_logic Hproj
      (GL_proves_box_to_box_boxdot p)) Hboxed).
Qed.

Theorem GL_proves_boxdot_T_of_boxdot_boxdot :
  forall p q : formula nat,
    GL_proves (Imp (Boxdot p) (Boxdot q)) ->
    GL_proves (Imp (Boxdot p) (Imp (Box q) q)).
Proof.
  intros p q Hpq.
  assert (Hconvert : GL_proves
    (Imp (Imp (Boxdot p) (Boxdot q))
      (Imp (Boxdot p) (Imp (Box q) q)))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Boxdot, And, Neg; simpl; tauto. }
  exact (Np_mp Hconvert Hpq).
Qed.

Theorem GL_proves_box_box_of_boxdot_T :
  forall p q : formula nat,
    GL_proves (Imp (Boxdot p) (Imp (Box q) q)) ->
    GL_proves (Imp (Box p) (Box q)).
Proof.
  intros p q Hpq.
  pose proof (logic_box_regularity GL_normal_logic Hpq) as Hboxed.
  assert (Hto_boxboxdot :
    GL_proves (Imp (Box p) (Box (Boxdot p)))).
  { apply GL_proves_box_to_box_boxdot. }
  assert (Hto_loeb :
    GL_proves (Imp (Box p) (Box (Imp (Box q) q)))).
  { exact (logic_imp_trans GL_classical_logic Hto_boxboxdot Hboxed). }
  exact (logic_imp_trans GL_classical_logic Hto_loeb (GL_proves_L q)).
Qed.

Corollary GL_proves_box_box_of_boxdot_plain :
  forall p q : formula nat,
    GL_proves (Imp (Boxdot p) q) ->
    GL_proves (Imp (Box p) (Box q)).
Proof.
  intros p q Hpq.
  apply GL_proves_box_box_of_boxdot_T.
  apply GL_proves_boxdot_T_of_boxdot_boxdot.
  now apply GL_proves_boxdot_boxdot_of_boxdot_plain.
Qed.

(** * Grz consequences *)

Definition Grz_normal_logic : normal_logic (@Grz_proves nat) :=
  @normal_proves_logic_is_normal schema_Grz schema_Grz_substitution_closed.

Definition Grz_classical_logic : classical_logic (@Grz_proves nat) :=
  quasi_classical (normal_quasi Grz_normal_logic).

Lemma Grz_proves_axiom :
  forall p : formula nat, Grz_proves (Grz p).
Proof.
  intro p. apply Np_extra. exists p. reflexivity.
Qed.

(** Foundation [lemma_Grz_1].  Its proof is pure K; the formula packages the
    self-referential propositional argument that extracts both T and Four
    from one Grz instance. *)
Lemma normal_proves_Grz_seed :
  forall Ax,
    schema_substitution_closed Ax ->
    forall p : formula nat,
      let seed := And p (Imp (Box p) (Box (Box p))) in
      normal_proves Ax
        (Imp (Box p)
          (Box (Imp (Box (Imp seed (Box seed))) seed))).
Proof.
  intros Ax Hclosed p seed.
  pose proof (@normal_proves_logic_is_normal Ax Hclosed) as Hnormal.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  assert (Hd1 :
    normal_proves Ax
      (Imp (Imp seed (Box p)) (Imp p (Box p)))).
  { apply (logic_classical_tautology Hclass).
    intro rho. unfold seed, And, Neg; simpl; tauto. }
  assert (Hseed_to_p : normal_proves Ax (Imp seed p)).
  { apply logic_and_elim_left_imp; exact Hclass. }
  assert (Hboxseed_to_boxp :
    normal_proves Ax (Imp (Box seed) (Box p))).
  { exact (logic_box_regularity Hnormal Hseed_to_p). }
  assert (Hd2 :
    normal_proves Ax
      (Imp (Imp seed (Box seed)) (Imp seed (Box p)))).
  { assert (Hconvert : normal_proves Ax
      (Imp (Imp (Box seed) (Box p))
        (Imp (Imp seed (Box seed)) (Imp seed (Box p))))).
    { apply (logic_classical_tautology Hclass).
      intro rho. simpl; tauto. }
    exact (Np_mp Hconvert Hboxseed_to_boxp). }
  assert (Hstep :
    normal_proves Ax
      (Imp (Imp seed (Box seed)) (Imp p (Box p)))).
  { exact (logic_imp_trans Hclass Hd2 Hd1). }
  assert (Hboxed_step :
    normal_proves Ax
      (Imp (Box (Imp seed (Box seed)))
        (Box (Imp p (Box p))))).
  { exact (logic_box_regularity Hnormal Hstep). }
  assert (Hfour_component :
    normal_proves Ax
      (Imp (Box (Imp seed (Box seed)))
        (Imp (Box p) (Box (Box p))))).
  { exact (logic_imp_trans Hclass Hboxed_step
      (quasi_modal_K (normal_quasi Hnormal) p (Box p))). }
  assert (Hunboxed :
    normal_proves Ax
      (Imp p
        (Imp (Box (Imp seed (Box seed))) seed))).
  { assert (Hconvert : normal_proves Ax
      (Imp
        (Imp (Box (Imp seed (Box seed)))
          (Imp (Box p) (Box (Box p))))
        (Imp p (Imp (Box (Imp seed (Box seed))) seed)))).
    { apply (logic_classical_tautology Hclass).
      intro rho. unfold seed, And, Neg; simpl; tauto. }
    exact (Np_mp Hconvert Hfour_component). }
  exact (logic_box_regularity Hnormal Hunboxed).
Qed.

Theorem Grz_proves_T_and_Four :
  forall p : formula nat,
    Grz_proves
      (Imp (Box p) (And p (Imp (Box p) (Box (Box p))))).
Proof.
  intro p.
  set (seed := And p (Imp (Box p) (Box (Box p)))).
  assert (Hseeded :
    Grz_proves
      (Imp (Box p)
        (Box (Imp (Box (Imp seed (Box seed))) seed)))).
  { exact (normal_proves_Grz_seed schema_Grz_substitution_closed p). }
  exact (logic_imp_trans Grz_classical_logic Hseeded
    (Grz_proves_axiom seed)).
Qed.

Theorem Grz_proves_T :
  forall p : formula nat, Grz_proves (T p).
Proof.
  intro p; unfold T.
  assert (Hproj : Grz_proves
    (Imp (And p (Imp (Box p) (Box (Box p)))) p)).
  { apply (logic_classical_tautology Grz_classical_logic).
    intro rho. unfold And, Neg; simpl; tauto.
  }
  exact (logic_imp_trans Grz_classical_logic
    (Grz_proves_T_and_Four p) Hproj).
Qed.

Theorem Grz_proves_Four :
  forall p : formula nat, Grz_proves (Four p).
Proof.
  intro p; unfold Four.
  assert (Hconvert : Grz_proves
    (Imp
      (Imp (Box p) (And p (Imp (Box p) (Box (Box p)))))
      (Imp (Box p) (Box (Box p))))).
  { apply (logic_classical_tautology Grz_classical_logic).
    intro rho. unfold And, Neg; simpl; tauto.
  }
  exact (Np_mp Hconvert (Grz_proves_T_and_Four p)).
Qed.

(** [Grz.truthlemma_lemma3] from the finite mini-canonical proof. *)
Theorem Grz_proves_truth_box_bridge :
  forall p : formula nat,
    Grz_proves
      (Imp (And p (Box (Imp p (Box p)))) (Box p)).
Proof.
  intro p.
  assert (HT : Grz_proves (Imp (Box (Imp p (Box p)))
      (Imp p (Box p)))).
  { apply Grz_proves_T. }
  assert (Hconvert : Grz_proves
    (Imp (Imp (Box (Imp p (Box p))) (Imp p (Box p)))
      (Imp (And p (Box (Imp p (Box p)))) (Box p)))).
  { apply (logic_classical_tautology Grz_classical_logic).
    intro rho. unfold And, Neg; simpl; tauto.
  }
  exact (Np_mp Hconvert HT).
Qed.

(** Grz contains S4, directly at the theorem level. *)
Theorem S4_weaker_than_Grz :
  forall (p : formula nat), S4_proves p -> Grz_proves p.
Proof.
  intros p Hp. induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [[q ->] | [q ->]].
    + apply Grz_proves_T.
    + apply Grz_proves_Four.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

(** Foundation [Grz.axiomDum]. *)
Theorem Grz_proves_Dum :
  forall p : formula nat, Grz_proves (Dum p).
Proof.
  intro p.
  assert (Hconvert : Grz_proves (Imp (Grz p) (Dum p))).
  { apply (logic_classical_tautology Grz_classical_logic).
    intro rho. unfold Grz, Dum; simpl; tauto. }
  exact (Np_mp Hconvert (Grz_proves_axiom p)).
Qed.
