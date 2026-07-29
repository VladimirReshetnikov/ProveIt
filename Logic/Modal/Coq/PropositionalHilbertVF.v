(** Hilbert VF calculi and formula-indexed semantic soundness.

    This ports Foundation/Propositional/Hilbert/VF/Basic and
    Foundation/Propositional/FMT/Hilbert/Basic.  The proof calculus remains
    polymorphic in its atom type; only the FMT interpretation is specialized
    to the source's nat atoms.  Structural proof transformations and semantic
    soundness share the generated proof induction, while consistency and
    semantic comparison are factored through explicit soundness/completeness
    predicates. *)

From FoundationModal Require Import
  PropositionalFormula PropositionalLogic PropositionalHilbert PropositionalFMT.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Substitution-closed VF schemata *)

Record phvf_hilbert (Atom : Type) : Type := {
  phvf_schema : pformula Atom -> Prop;
  phvf_schema_substitute : forall p,
    phvf_schema p -> forall sigma : psubstitution Atom Atom,
    phvf_schema (pformula_substitute sigma p)
}.

Arguments phvf_schema {Atom} _ _.
Arguments phvf_schema_substitute {Atom} _ _ _ _.

Definition phvf_axiom_ser {Atom : Type} : pformula Atom :=
  pneg (pneg ptop).

Definition phvf_hilbert_VF (Atom : Type) : phvf_hilbert Atom.
Proof.
  refine {| phvf_schema := fun _ => False |}.
  intros p H; contradiction.
Defined.

Definition phvf_hilbert_VF_Ser (Atom : Type) : phvf_hilbert Atom.
Proof.
  refine {| phvf_schema := fun p => p = phvf_axiom_ser |}.
  intros p -> sigma. reflexivity.
Defined.

Definition phvf_distribute_and_or {Atom : Type}
    (p q r : pformula Atom) : pformula Atom :=
  PImp (PAnd p (POr q r)) (POr (PAnd p q) (PAnd p r)).

(** * Type-valued proofs and factored proof transformations *)

Inductive phvf_proof {Atom : Type} (H : phvf_hilbert Atom) :
    pformula Atom -> Type :=
| PHVFPAxiom : forall p, phvf_schema H p -> phvf_proof H p
| PHVFPAndElimL : forall p q, phvf_proof H (ph_axiom_and1 p q)
| PHVFPAndElimR : forall p q, phvf_proof H (ph_axiom_and2 p q)
| PHVFPOrIntroL : forall p q, phvf_proof H (ph_axiom_or1 p q)
| PHVFPOrIntroR : forall p q, phvf_proof H (ph_axiom_or2 p q)
| PHVFPDistributeAndOr : forall p q r,
    phvf_proof H (phvf_distribute_and_or p q r)
| PHVFPIdentity : forall p, phvf_proof H (PImp p p)
| PHVFPEfq : forall p, phvf_proof H (ph_axiom_efq p)
| PHVFPModusPonens : forall p q,
    phvf_proof H (PImp p q) -> phvf_proof H p -> phvf_proof H q
| PHVFPFortiori : forall p q,
    phvf_proof H p -> phvf_proof H (PImp q p)
| PHVFPAndRule : forall p q,
    phvf_proof H p -> phvf_proof H q -> phvf_proof H (PAnd p q)
| PHVFPRuleC : forall p q r,
    phvf_proof H (PImp p q) -> phvf_proof H (PImp p r) ->
    phvf_proof H (PImp p (PAnd q r))
| PHVFPRuleD : forall p q r,
    phvf_proof H (PImp p r) -> phvf_proof H (PImp q r) ->
    phvf_proof H (PImp (POr p q) r)
| PHVFPRuleI : forall p q r,
    phvf_proof H (PImp p q) -> phvf_proof H (PImp q r) ->
    phvf_proof H (PImp p r).

Arguments PHVFPAxiom {Atom H p} _.
Arguments PHVFPAndElimL {Atom H} p q.
Arguments PHVFPAndElimR {Atom H} p q.
Arguments PHVFPOrIntroL {Atom H} p q.
Arguments PHVFPOrIntroR {Atom H} p q.
Arguments PHVFPDistributeAndOr {Atom H} p q r.
Arguments PHVFPIdentity {Atom H} p.
Arguments PHVFPEfq {Atom H} p.
Arguments PHVFPModusPonens {Atom H p q} _ _.
Arguments PHVFPFortiori {Atom H p} q _.
Arguments PHVFPAndRule {Atom H p q} _ _.
Arguments PHVFPRuleC {Atom H p q r} _ _.
Arguments PHVFPRuleD {Atom H p q r} _ _.
Arguments PHVFPRuleI {Atom H p q r} _ _.

Definition phvf_provable {Atom : Type}
    (H : phvf_hilbert Atom) (p : pformula Atom) : Prop :=
  inhabited (phvf_proof H p).

Lemma phvf_provable_of_schema :
  forall (Atom : Type) (H : phvf_hilbert Atom) p,
    phvf_schema H p -> phvf_provable H p.
Proof. intros Atom H p Hp; constructor; now apply PHVFPAxiom. Qed.

Fixpoint phvf_proof_of_schema_inclusion {Atom : Type}
    {H K : phvf_hilbert Atom}
    (Hinc : forall p, phvf_schema H p -> phvf_schema K p)
    {p} (d : phvf_proof H p) : phvf_proof K p.
Proof.
  destruct d.
  - apply PHVFPAxiom, Hinc; assumption.
  - apply PHVFPAndElimL.
  - apply PHVFPAndElimR.
  - apply PHVFPOrIntroL.
  - apply PHVFPOrIntroR.
  - apply PHVFPDistributeAndOr.
  - apply PHVFPIdentity.
  - apply PHVFPEfq.
  - exact (PHVFPModusPonens
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHVFPFortiori _
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d)).
  - exact (PHVFPAndRule
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHVFPRuleC
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHVFPRuleD
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHVFPRuleI
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phvf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
Defined.

Lemma phvf_provable_of_schema_inclusion :
  forall (Atom : Type) (H K : phvf_hilbert Atom),
    (forall p, phvf_schema H p -> phvf_schema K p) ->
    forall p, phvf_provable H p -> phvf_provable K p.
Proof.
  intros Atom H K Hinc p [d]. constructor.
  exact (@phvf_proof_of_schema_inclusion Atom H K Hinc p d).
Qed.

Fixpoint phvf_proof_substitute {Atom : Type} {H : phvf_hilbert Atom}
    (sigma : psubstitution Atom Atom) {p} (d : phvf_proof H p) :
    phvf_proof H (pformula_substitute sigma p).
Proof.
  destruct d; cbn [ph_axiom_and1 ph_axiom_and2 ph_axiom_or1 ph_axiom_or2
    phvf_distribute_and_or ph_axiom_efq].
  - apply PHVFPAxiom. now apply phvf_schema_substitute.
  - apply PHVFPAndElimL.
  - apply PHVFPAndElimR.
  - apply PHVFPOrIntroL.
  - apply PHVFPOrIntroR.
  - apply PHVFPDistributeAndOr.
  - apply PHVFPIdentity.
  - apply PHVFPEfq.
  - exact (PHVFPModusPonens (@phvf_proof_substitute Atom H sigma _ d1)
      (@phvf_proof_substitute Atom H sigma _ d2)).
  - exact (PHVFPFortiori _ (@phvf_proof_substitute Atom H sigma _ d)).
  - exact (PHVFPAndRule (@phvf_proof_substitute Atom H sigma _ d1)
      (@phvf_proof_substitute Atom H sigma _ d2)).
  - exact (PHVFPRuleC (@phvf_proof_substitute Atom H sigma _ d1)
      (@phvf_proof_substitute Atom H sigma _ d2)).
  - exact (PHVFPRuleD (@phvf_proof_substitute Atom H sigma _ d1)
      (@phvf_proof_substitute Atom H sigma _ d2)).
  - exact (PHVFPRuleI (@phvf_proof_substitute Atom H sigma _ d1)
      (@phvf_proof_substitute Atom H sigma _ d2)).
Defined.

Lemma phvf_provable_substitute :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (sigma : psubstitution Atom Atom) p,
    phvf_provable H p ->
    phvf_provable H (pformula_substitute sigma p).
Proof.
  intros Atom H sigma p [d]. constructor.
  exact (@phvf_proof_substitute Atom H sigma p d).
Qed.

Fixpoint phvf_proof_of_proof_schema {Atom : Type}
    {H K : phvf_hilbert Atom}
    (Hschema : forall p, phvf_schema H p -> phvf_proof K p)
    {p} (d : phvf_proof H p) : phvf_proof K p.
Proof.
  destruct d.
  - now apply Hschema.
  - apply PHVFPAndElimL.
  - apply PHVFPAndElimR.
  - apply PHVFPOrIntroL.
  - apply PHVFPOrIntroR.
  - apply PHVFPDistributeAndOr.
  - apply PHVFPIdentity.
  - apply PHVFPEfq.
  - exact (PHVFPModusPonens
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHVFPFortiori _
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d)).
  - exact (PHVFPAndRule
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHVFPRuleC
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHVFPRuleD
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHVFPRuleI
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phvf_proof_of_proof_schema Atom H K Hschema _ d2)).
Defined.

Lemma phvf_provable_of_provable_schema :
  forall (Atom : Type) (H K : phvf_hilbert Atom),
    (forall p, phvf_schema H p -> phvf_provable K p) ->
    forall p, phvf_provable H p -> phvf_provable K p.
Proof.
  intros Atom H K Hschema p [d]. constructor.
  exact (@phvf_proof_of_proof_schema Atom H K
    (fun q Hq => ph_inhabited_get (Hschema q Hq)) p d).
Qed.

Lemma phvf_VF_schema_in_VF_Ser :
  forall (Atom : Type) p,
    phvf_schema (phvf_hilbert_VF Atom) p ->
    phvf_schema (phvf_hilbert_VF_Ser Atom) p.
Proof. intros Atom p H; contradiction. Qed.

Lemma phvf_VF_Ser_provable_ser : forall Atom : Type,
  phvf_provable (phvf_hilbert_VF_Ser Atom) phvf_axiom_ser.
Proof. intros Atom; apply phvf_provable_of_schema; reflexivity. Qed.

(** * Logic packaging *)

Definition phvf_logic_included {Atom : Type}
    (H K : phvf_hilbert Atom) : Prop :=
  forall p, phvf_provable H p -> phvf_provable K p.

Definition phvf_logic_strictly_included {Atom : Type}
    (H K : phvf_hilbert Atom) : Prop :=
  phvf_logic_included H K /\
  exists p, phvf_provable K p /\ ~ phvf_provable H p.

Definition phvf_consistent {Atom : Type} (H : phvf_hilbert Atom) : Prop :=
  ~ phvf_provable H PFalsum.

Definition phvf_hilbert_logic {Atom : Type}
    (H : phvf_hilbert Atom) : pformula_logic Atom.
Proof.
  refine {| pformula_logic_theorems := phvf_provable H |}.
  - intros sigma p Hp. exact (phvf_provable_substitute sigma Hp).
  - intros p q [Hpq] [Hp]. constructor. exact (PHVFPModusPonens Hpq Hp).
Defined.

Lemma phvf_hilbert_logic_iff_provable :
  forall (Atom : Type) (H : phvf_hilbert Atom) p,
    pformula_logic_theorems (phvf_hilbert_logic H) p <->
    phvf_provable H p.
Proof. reflexivity. Qed.

Lemma phvf_hilbert_logic_subset_of_schema_inclusion :
  forall (Atom : Type) (H K : phvf_hilbert Atom),
    (forall p, phvf_schema H p -> phvf_schema K p) ->
    pformula_logic_subset (phvf_hilbert_logic H) (phvf_hilbert_logic K).
Proof. intros Atom H K Hinc p Hp; now apply phvf_provable_of_schema_inclusion with H. Qed.

Lemma phvf_hilbert_logic_subset_of_provable_schema :
  forall (Atom : Type) (H K : phvf_hilbert Atom),
    (forall p, phvf_schema H p -> phvf_provable K p) ->
    pformula_logic_subset (phvf_hilbert_logic H) (phvf_hilbert_logic K).
Proof. intros Atom H K Hschema p Hp; now apply phvf_provable_of_provable_schema with H. Qed.

Definition phvf_logic_VF (Atom : Type) : pformula_logic Atom :=
  phvf_hilbert_logic (phvf_hilbert_VF Atom).

Definition phvf_logic_VF_Ser (Atom : Type) : pformula_logic Atom :=
  phvf_hilbert_logic (phvf_hilbert_VF_Ser Atom).

(** * Formula-indexed model, frame-class, and model-class soundness *)

Theorem phvf_proof_fmt_model_sound :
  forall (H : phvf_hilbert nat) p,
    phvf_proof H p -> forall M : fmt_model,
    (forall q, phvf_schema H q -> fmt_model_valid M q) ->
    fmt_model_valid M p.
Proof.
  intros H p d. induction d; intros M Hschema.
  - now apply Hschema.
  - apply fmt_valid_and1.
  - apply fmt_valid_and2.
  - apply fmt_valid_or1.
  - apply fmt_valid_or2.
  - apply fmt_valid_distribute_and_or.
  - apply fmt_valid_identity.
  - apply fmt_valid_efq.
  - apply fmt_valid_mdp with p; [apply IHd1 | apply IHd2]; exact Hschema.
  - apply fmt_valid_afortiori. now apply IHd.
  - apply fmt_valid_and_rule; [apply IHd1 | apply IHd2]; exact Hschema.
  - apply fmt_valid_rule_C; [apply IHd1 | apply IHd2]; exact Hschema.
  - apply fmt_valid_rule_D; [apply IHd1 | apply IHd2]; exact Hschema.
  - apply fmt_valid_rule_I with q; [apply IHd1 | apply IHd2]; exact Hschema.
Qed.

Definition phvf_fmt_frame_schema_valid (H : phvf_hilbert nat)
    (C : fmt_frame -> Prop) : Prop :=
  forall p, phvf_schema H p -> fmt_frame_class_valid C p.

Definition phvf_fmt_model_schema_valid (H : phvf_hilbert nat)
    (C : fmt_model -> Prop) : Prop :=
  forall p, phvf_schema H p -> fmt_model_class_valid C p.

Definition phvf_fmt_frame_sound (H : phvf_hilbert nat)
    (C : fmt_frame -> Prop) : Prop :=
  forall p, phvf_provable H p -> fmt_frame_class_valid C p.

Definition phvf_fmt_frame_complete (H : phvf_hilbert nat)
    (C : fmt_frame -> Prop) : Prop :=
  forall p, fmt_frame_class_valid C p -> phvf_provable H p.

Definition phvf_fmt_model_sound (H : phvf_hilbert nat)
    (C : fmt_model -> Prop) : Prop :=
  forall p, phvf_provable H p -> fmt_model_class_valid C p.

Theorem phvf_fmt_frame_sound_of_schema :
  forall H C,
    phvf_fmt_frame_schema_valid H C -> phvf_fmt_frame_sound H C.
Proof.
  intros H C Hschema p [d] F HF V.
  eapply phvf_proof_fmt_model_sound; [exact d |].
  intros q Hq w. exact (Hschema q Hq F HF V w).
Qed.

Theorem phvf_fmt_model_sound_of_schema :
  forall H C,
    phvf_fmt_model_schema_valid H C -> phvf_fmt_model_sound H C.
Proof.
  intros H C Hschema p [d] M HM.
  eapply phvf_proof_fmt_model_sound; [exact d |].
  intros q Hq. exact (Hschema q Hq M HM).
Qed.

Theorem phvf_consistent_of_fmt_frame_sound :
  forall H C,
    phvf_fmt_frame_sound H C ->
    (exists F, C F) -> phvf_consistent H.
Proof.
  intros H C Hsound [F HF] Hbot.
  exact (@fmt_frame_not_valid_bottom F (Hsound PFalsum Hbot F HF)).
Qed.

Theorem phvf_consistent_of_fmt_model_sound :
  forall H C,
    phvf_fmt_model_sound H C ->
    (exists M, C M) -> phvf_consistent H.
Proof.
  intros H C Hsound [M HM] Hbot.
  exact (@fmt_model_not_valid_bottom M (Hsound PFalsum Hbot M HM)).
Qed.

Theorem phvf_included_of_fmt_frame_class_subset :
  forall H K C D,
    (forall F, D F -> C F) ->
    phvf_fmt_frame_sound H C -> phvf_fmt_frame_complete K D ->
    phvf_logic_included H K.
Proof.
  intros H K C D Hsub Hsound Hcomplete p Hp.
  apply Hcomplete. intros F HF. exact (Hsound p Hp F (Hsub F HF)).
Qed.

(** * Named VF systems and finite separating countermodels *)

Definition phvf_fmt_trivial_frame : fmt_frame :=
  {| fmt_world := unit;
     fmt_access := fun _ _ _ => True;
     fmt_root := tt;
     fmt_root_access := fun _ _ => I |}.

Lemma phvf_fmt_trivial_nt_serial : fmt_nt_serial phvf_fmt_trivial_frame.
Proof. intros []; now exists tt. Qed.

Theorem phvf_VF_fmt_sound :
  phvf_fmt_frame_sound (phvf_hilbert_VF nat) (fun _ => True).
Proof.
  apply phvf_fmt_frame_sound_of_schema.
  intros p H; contradiction.
Qed.

Theorem phvf_VF_consistent : phvf_consistent (phvf_hilbert_VF nat).
Proof.
  eapply phvf_consistent_of_fmt_frame_sound.
  - exact phvf_VF_fmt_sound.
  - now exists phvf_fmt_trivial_frame.
Qed.

Theorem phvf_VF_Ser_fmt_sound :
  phvf_fmt_frame_sound (phvf_hilbert_VF_Ser nat) fmt_nt_serial.
Proof.
  apply phvf_fmt_frame_sound_of_schema.
  intros p -> F Hserial. now apply fmt_valid_ser_of_nt_serial.
Qed.

Theorem phvf_VF_Ser_consistent :
  phvf_consistent (phvf_hilbert_VF_Ser nat).
Proof.
  eapply phvf_consistent_of_fmt_frame_sound.
  - exact phvf_VF_Ser_fmt_sound.
  - exists phvf_fmt_trivial_frame. exact phvf_fmt_trivial_nt_serial.
Qed.

Definition phvf_fmt_ser_counter_frame : fmt_frame :=
  {| fmt_world := bool;
     fmt_access := fun _ x _ => x = true;
     fmt_root := true;
     fmt_root_access := fun _ _ => eq_refl |}.

Definition phvf_fmt_ser_counter_model : fmt_model :=
  {| fmt_model_frame := phvf_fmt_ser_counter_frame;
     fmt_model_valuation := fun _ _ => True |}.

Lemma phvf_fmt_ser_counter_not_forces_ser :
  ~ fmt_forces phvf_fmt_ser_counter_model true phvf_axiom_ser.
Proof.
  intro Hser. apply (Hser false eq_refl).
  intros z R _. discriminate R.
Qed.

Theorem phvf_VF_unprovable_ser :
  ~ phvf_provable (phvf_hilbert_VF nat) phvf_axiom_ser.
Proof.
  intro Hp. apply phvf_fmt_ser_counter_not_forces_ser.
  exact (@phvf_VF_fmt_sound phvf_axiom_ser Hp phvf_fmt_ser_counter_frame I
    (fun _ _ => True) true).
Qed.

Theorem phvf_VF_strictly_included_VF_Ser :
  phvf_logic_strictly_included
    (phvf_hilbert_VF nat) (phvf_hilbert_VF_Ser nat).
Proof.
  split.
  - intros p Hp. now apply phvf_provable_of_schema_inclusion with
      (H := phvf_hilbert_VF nat).
  - exists phvf_axiom_ser. split.
    + apply phvf_VF_Ser_provable_ser.
    + exact phvf_VF_unprovable_ser.
Qed.

Definition phvf_fmt_iff_counter_frame : fmt_frame :=
  {| fmt_world := bool;
     fmt_access := fun p x _ =>
       x = true \/ (x = false /\ p = phvf_axiom_ser);
     fmt_root := true;
     fmt_root_access := fun _ _ => or_introl eq_refl |}.

Definition phvf_fmt_iff_counter_model : fmt_model :=
  {| fmt_model_frame := phvf_fmt_iff_counter_frame;
     fmt_model_valuation := fun _ _ => True |}.

Lemma phvf_fmt_iff_counter_forces_neg_top :
  fmt_forces phvf_fmt_iff_counter_model false (pneg ptop).
Proof.
  intros z [Hroot | [_ Hformula]] _.
  - discriminate Hroot.
  - unfold phvf_axiom_ser, pneg, ptop in Hformula.
    discriminate Hformula.
Qed.

Lemma phvf_fmt_iff_counter_not_forces_ser :
  ~ fmt_forces phvf_fmt_iff_counter_model false phvf_axiom_ser.
Proof.
  intro Hser. apply (Hser false (or_intror (conj eq_refl eq_refl))).
  exact phvf_fmt_iff_counter_forces_neg_top.
Qed.

Lemma phvf_fmt_iff_counter_not_forces_top_iff_ser :
  ~ fmt_forces phvf_fmt_iff_counter_model true
      (fmt_iff ptop phvf_axiom_ser).
Proof.
  intros [Hforward _]. apply phvf_fmt_iff_counter_not_forces_ser.
  apply (Hforward false (or_introl eq_refl)). apply fmt_forces_top.
Qed.

Theorem phvf_VF_unprovable_top_iff_ser :
  ~ phvf_provable (phvf_hilbert_VF nat)
      (fmt_iff ptop phvf_axiom_ser).
Proof.
  intro Hp. apply phvf_fmt_iff_counter_not_forces_top_iff_ser.
  exact (@phvf_VF_fmt_sound (fmt_iff ptop phvf_axiom_ser) Hp
    phvf_fmt_iff_counter_frame I (fun _ _ => True) true).
Qed.
