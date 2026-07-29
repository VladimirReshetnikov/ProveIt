(** Hilbert F calculi and their rooted arbitrary-relation semantics.

    This ports Foundation/Propositional/Hilbert/F/Basic together with the
    active, independently proved surface of
    Foundation/Propositional/Kripke2/Hilbert.  The calculus is deliberately
    separate from [ph_hilbert]: a-fortiori is a rule on global theorems here,
    not the locally invalid K schema.  One proof recursor factors schema
    weakening, substitution, frame/model soundness, and every named-system
    result.

    The source admits reflexive completeness with [sorry].  We do not import
    that assumption.  Reflexive soundness, consistency, and the strict
    semantic separation from serial frames are checked; the completeness-
    dependent inclusion is conservatively left outside the theorem surface. *)

From FoundationModal Require Import
  PropositionalFormula PropositionalLogic PropositionalHilbert PropositionalKripke2
  PropositionalKripke2Correspondence.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Substitution-closed optional axiom schemata *)

Record phf_hilbert (Atom : Type) : Type := {
  phf_schema : pformula Atom -> Prop;
  phf_schema_substitute : forall p,
    phf_schema p -> forall sigma : psubstitution Atom Atom,
    phf_schema (pformula_substitute sigma p)
}.

Arguments phf_schema {Atom} _ _.
Arguments phf_schema_substitute {Atom} _ _ _ _.

Definition phf_hilbert_F (Atom : Type) : phf_hilbert Atom.
Proof.
  refine {| phf_schema := fun _ => False |}.
  intros p H; contradiction.
Defined.

Definition phf_hilbert_F_Ser (Atom : Type) : phf_hilbert Atom.
Proof.
  refine {| phf_schema := fun p => p = @pk2_axiom_ser Atom |}.
  intros p -> sigma. reflexivity.
Defined.

Definition phf_hilbert_F_Rfl (Atom : Type) : phf_hilbert Atom.
Proof.
  refine {| phf_schema := fun r =>
    exists p q, r = pk2_axiom_rfl p q |}.
  intros r [p [q ->]] sigma.
  exists (pformula_substitute sigma p), (pformula_substitute sigma q).
  reflexivity.
Defined.

Definition phf_hilbert_F_Sym (Atom : Type) : phf_hilbert Atom.
Proof.
  refine {| phf_schema := fun r =>
    exists p q, r = pk2_axiom_sym p q |}.
  intros r [p [q ->]] sigma.
  exists (pformula_substitute sigma p), (pformula_substitute sigma q).
  reflexivity.
Defined.

Definition phf_hilbert_F_Rfl_Sym (Atom : Type) : phf_hilbert Atom.
Proof.
  refine {| phf_schema := fun r =>
    (exists p q, r = pk2_axiom_rfl p q) \/
    (exists p q, r = pk2_axiom_sym p q) |}.
  intros r [[p [q ->]] | [p [q ->]]] sigma.
  - left. exists (pformula_substitute sigma p),
      (pformula_substitute sigma q). reflexivity.
  - right. exists (pformula_substitute sigma p),
      (pformula_substitute sigma q). reflexivity.
Defined.

Definition phf_hilbert_F_Tra1 (Atom : Type) : phf_hilbert Atom.
Proof.
  refine {| phf_schema := fun s =>
    exists p q r, s = pk2_axiom_tra1 p q r |}.
  intros s [p [q [r ->]]] sigma.
  exists (pformula_substitute sigma p),
    (pformula_substitute sigma q), (pformula_substitute sigma r).
  reflexivity.
Defined.

Definition phf_hilbert_F_Rfl_Tra1 (Atom : Type) : phf_hilbert Atom.
Proof.
  refine {| phf_schema := fun s =>
    (exists p q, s = pk2_axiom_rfl p q) \/
    (exists p q r, s = pk2_axiom_tra1 p q r) |}.
  intros s [[p [q ->]] | [p [q [r ->]]]] sigma.
  - left. exists (pformula_substitute sigma p),
      (pformula_substitute sigma q). reflexivity.
  - right. exists (pformula_substitute sigma p),
      (pformula_substitute sigma q), (pformula_substitute sigma r).
    reflexivity.
Defined.

Lemma phf_F_schema_in_F_Ser :
  forall (Atom : Type) p,
    phf_schema (phf_hilbert_F Atom) p ->
    phf_schema (phf_hilbert_F_Ser Atom) p.
Proof. intros Atom p H; contradiction. Qed.

Lemma phf_F_schema_in_F_Rfl :
  forall (Atom : Type) p,
    phf_schema (phf_hilbert_F Atom) p ->
    phf_schema (phf_hilbert_F_Rfl Atom) p.
Proof. intros Atom p H; contradiction. Qed.

Lemma phf_F_schema_in_F_Sym :
  forall (Atom : Type) p,
    phf_schema (phf_hilbert_F Atom) p ->
    phf_schema (phf_hilbert_F_Sym Atom) p.
Proof. intros Atom p H; contradiction. Qed.

Lemma phf_F_schema_in_F_Tra1 :
  forall (Atom : Type) p,
    phf_schema (phf_hilbert_F Atom) p ->
    phf_schema (phf_hilbert_F_Tra1 Atom) p.
Proof. intros Atom p H; contradiction. Qed.

Lemma phf_F_Rfl_schema_in_F_Rfl_Sym :
  forall (Atom : Type) p,
    phf_schema (phf_hilbert_F_Rfl Atom) p ->
    phf_schema (phf_hilbert_F_Rfl_Sym Atom) p.
Proof. intros Atom p H; now left. Qed.

Lemma phf_F_Sym_schema_in_F_Rfl_Sym :
  forall (Atom : Type) p,
    phf_schema (phf_hilbert_F_Sym Atom) p ->
    phf_schema (phf_hilbert_F_Rfl_Sym Atom) p.
Proof. intros Atom p H; now right. Qed.

Lemma phf_F_Rfl_schema_in_F_Rfl_Tra1 :
  forall (Atom : Type) p,
    phf_schema (phf_hilbert_F_Rfl Atom) p ->
    phf_schema (phf_hilbert_F_Rfl_Tra1 Atom) p.
Proof. intros Atom p H; now left. Qed.

Lemma phf_F_Tra1_schema_in_F_Rfl_Tra1 :
  forall (Atom : Type) p,
    phf_schema (phf_hilbert_F_Tra1 Atom) p ->
    phf_schema (phf_hilbert_F_Rfl_Tra1 Atom) p.
Proof. intros Atom p H; now right. Qed.

(** * One proof datatype and its structural recursors *)

Inductive phf_proof {Atom : Type} (H : phf_hilbert Atom) :
    pformula Atom -> Type :=
| PHFPAxiom : forall p, phf_schema H p -> phf_proof H p
| PHFPAndElimL : forall p q, phf_proof H (ph_axiom_and1 p q)
| PHFPAndElimR : forall p q, phf_proof H (ph_axiom_and2 p q)
| PHFPOrIntroL : forall p q, phf_proof H (ph_axiom_or1 p q)
| PHFPOrIntroR : forall p q, phf_proof H (ph_axiom_or2 p q)
| PHFPDistributeAndOr : forall p q r,
    phf_proof H (pk2_distribute_and_or p q r)
| PHFPAxiomC : forall p q r, phf_proof H (pk2_axiom_C p q r)
| PHFPAxiomD : forall p q r, phf_proof H (pk2_axiom_D p q r)
| PHFPAxiomI : forall p q r, phf_proof H (pk2_axiom_I p q r)
| PHFPIdentity : forall p, phf_proof H (PImp p p)
| PHFPEfq : forall p, phf_proof H (ph_axiom_efq p)
| PHFPModusPonens : forall p q,
    phf_proof H (PImp p q) -> phf_proof H p -> phf_proof H q
| PHFPAFortiori : forall p q,
    phf_proof H p -> phf_proof H (PImp q p)
| PHFPAndRule : forall p q,
    phf_proof H p -> phf_proof H q -> phf_proof H (PAnd p q).

Arguments PHFPAxiom {Atom H p} _.
Arguments PHFPAndElimL {Atom H} p q.
Arguments PHFPAndElimR {Atom H} p q.
Arguments PHFPOrIntroL {Atom H} p q.
Arguments PHFPOrIntroR {Atom H} p q.
Arguments PHFPDistributeAndOr {Atom H} p q r.
Arguments PHFPAxiomC {Atom H} p q r.
Arguments PHFPAxiomD {Atom H} p q r.
Arguments PHFPAxiomI {Atom H} p q r.
Arguments PHFPIdentity {Atom H} p.
Arguments PHFPEfq {Atom H} p.
Arguments PHFPModusPonens {Atom H p q} _ _.
Arguments PHFPAFortiori {Atom H p} q _.
Arguments PHFPAndRule {Atom H p q} _ _.

Definition phf_provable {Atom : Type}
    (H : phf_hilbert Atom) (p : pformula Atom) : Prop :=
  inhabited (phf_proof H p).

Lemma phf_provable_of_schema :
  forall (Atom : Type) (H : phf_hilbert Atom) p,
    phf_schema H p -> phf_provable H p.
Proof. intros Atom H p Hp; constructor; now apply PHFPAxiom. Qed.

Fixpoint phf_proof_of_schema_inclusion {Atom : Type}
    {H K : phf_hilbert Atom}
    (Hinc : forall p, phf_schema H p -> phf_schema K p)
    {p} (d : phf_proof H p) : phf_proof K p.
Proof.
  destruct d.
  - apply PHFPAxiom, Hinc; assumption.
  - apply PHFPAndElimL.
  - apply PHFPAndElimR.
  - apply PHFPOrIntroL.
  - apply PHFPOrIntroR.
  - apply PHFPDistributeAndOr.
  - apply PHFPAxiomC.
  - apply PHFPAxiomD.
  - apply PHFPAxiomI.
  - apply PHFPIdentity.
  - apply PHFPEfq.
  - eapply PHFPModusPonens;
      [apply phf_proof_of_schema_inclusion with (H := H) |
       apply phf_proof_of_schema_inclusion with (H := H)]; eauto.
  - apply PHFPAFortiori.
    now apply phf_proof_of_schema_inclusion with (H := H).
  - apply PHFPAndRule;
      now apply phf_proof_of_schema_inclusion with (H := H).
Defined.

Lemma phf_provable_of_schema_inclusion :
  forall (Atom : Type) (H K : phf_hilbert Atom),
    (forall p, phf_schema H p -> phf_schema K p) ->
    forall p, phf_provable H p -> phf_provable K p.
Proof.
  intros Atom H K Hinc p [d]. constructor.
  exact (phf_proof_of_schema_inclusion Hinc d).
Qed.

Fixpoint phf_proof_substitute {Atom : Type} {H : phf_hilbert Atom}
    (sigma : psubstitution Atom Atom) {p}
    (d : phf_proof H p) :
    phf_proof H (pformula_substitute sigma p).
Proof.
  destruct d; cbn [ph_axiom_and1 ph_axiom_and2 ph_axiom_or1
    ph_axiom_or2 pk2_distribute_and_or pk2_axiom_C
    pk2_axiom_D pk2_axiom_I ph_axiom_efq].
  - apply PHFPAxiom. now apply phf_schema_substitute.
  - apply PHFPAndElimL.
  - apply PHFPAndElimR.
  - apply PHFPOrIntroL.
  - apply PHFPOrIntroR.
  - apply PHFPDistributeAndOr.
  - apply PHFPAxiomC.
  - apply PHFPAxiomD.
  - apply PHFPAxiomI.
  - apply PHFPIdentity.
  - apply PHFPEfq.
  - exact (PHFPModusPonens
      (@phf_proof_substitute Atom H sigma _ d1)
      (@phf_proof_substitute Atom H sigma _ d2)).
  - exact (PHFPAFortiori _
      (@phf_proof_substitute Atom H sigma _ d)).
  - exact (PHFPAndRule
      (@phf_proof_substitute Atom H sigma _ d1)
      (@phf_proof_substitute Atom H sigma _ d2)).
Defined.

Lemma phf_provable_substitute :
  forall (Atom : Type) (H : phf_hilbert Atom)
         (sigma : psubstitution Atom Atom) p,
    phf_provable H p ->
    phf_provable H (pformula_substitute sigma p).
Proof.
  intros Atom H sigma p [d]. constructor.
  exact (phf_proof_substitute sigma d).
Qed.

Fixpoint phf_proof_of_provable_schema {Atom : Type}
    {H K : phf_hilbert Atom}
    (Hschema : forall p, phf_schema H p -> phf_proof K p)
    {p} (d : phf_proof H p) : phf_proof K p.
Proof.
  destruct d.
  - now apply Hschema.
  - apply PHFPAndElimL.
  - apply PHFPAndElimR.
  - apply PHFPOrIntroL.
  - apply PHFPOrIntroR.
  - apply PHFPDistributeAndOr.
  - apply PHFPAxiomC.
  - apply PHFPAxiomD.
  - apply PHFPAxiomI.
  - apply PHFPIdentity.
  - apply PHFPEfq.
  - eapply PHFPModusPonens;
      [apply phf_proof_of_provable_schema with (H := H) |
       apply phf_proof_of_provable_schema with (H := H)]; eauto.
  - apply PHFPAFortiori.
    now apply phf_proof_of_provable_schema with (H := H).
  - apply PHFPAndRule;
      now apply phf_proof_of_provable_schema with (H := H).
Defined.

Lemma phf_provable_of_provable_schema :
  forall (Atom : Type) (H K : phf_hilbert Atom),
    (forall p, phf_schema H p -> phf_provable K p) ->
    forall p, phf_provable H p -> phf_provable K p.
Proof.
  intros Atom H K Hschema p [d]. constructor.
  refine (@phf_proof_of_provable_schema Atom H K
    (fun q Hq => ph_inhabited_get (Hschema q Hq)) p d).
Qed.

Definition phf_logic_included {Atom : Type}
    (H K : phf_hilbert Atom) : Prop :=
  forall p, phf_provable H p -> phf_provable K p.

Definition phf_logic_strictly_included {Atom : Type}
    (H K : phf_hilbert Atom) : Prop :=
  phf_logic_included H K /\
  exists p, phf_provable K p /\ ~ phf_provable H p.

Definition phf_consistent {Atom : Type} (H : phf_hilbert Atom) : Prop :=
  ~ phf_provable H PFalsum.

Definition phf_hilbert_logic {Atom : Type}
    (H : phf_hilbert Atom) : pformula_logic Atom.
Proof.
  refine {| pformula_logic_theorems := phf_provable H |}.
  - intros sigma p Hp.
    exact (@phf_provable_substitute Atom H sigma p Hp).
  - intros p q [Hpq] [Hp]. constructor.
    exact (PHFPModusPonens Hpq Hp).
Defined.

Lemma phf_hilbert_logic_iff_provable :
  forall (Atom : Type) (H : phf_hilbert Atom) p,
    pformula_logic_theorems (phf_hilbert_logic H) p <->
    phf_provable H p.
Proof. reflexivity. Qed.

Lemma phf_hilbert_logic_subset_of_schema_inclusion :
  forall (Atom : Type) (H K : phf_hilbert Atom),
    (forall p, phf_schema H p -> phf_schema K p) ->
    pformula_logic_subset (phf_hilbert_logic H) (phf_hilbert_logic K).
Proof.
  intros Atom H K Hinc p Hp.
  exact (@phf_provable_of_schema_inclusion Atom H K Hinc p Hp).
Qed.

Lemma phf_hilbert_logic_subset_of_provable_schema :
  forall (Atom : Type) (H K : phf_hilbert Atom),
    (forall p, phf_schema H p -> phf_provable K p) ->
    pformula_logic_subset (phf_hilbert_logic H) (phf_hilbert_logic K).
Proof.
  intros Atom H K Hschema p Hp.
  exact (@phf_provable_of_provable_schema Atom H K Hschema p Hp).
Qed.

Definition phf_logic_F (Atom : Type) : pformula_logic Atom :=
  phf_hilbert_logic (phf_hilbert_F Atom).

Definition phf_logic_F_Ser (Atom : Type) : pformula_logic Atom :=
  phf_hilbert_logic (phf_hilbert_F_Ser Atom).

Definition phf_logic_F_Rfl (Atom : Type) : pformula_logic Atom :=
  phf_hilbert_logic (phf_hilbert_F_Rfl Atom).

Definition phf_logic_F_Sym (Atom : Type) : pformula_logic Atom :=
  phf_hilbert_logic (phf_hilbert_F_Sym Atom).

Definition phf_logic_F_Rfl_Sym (Atom : Type) : pformula_logic Atom :=
  phf_hilbert_logic (phf_hilbert_F_Rfl_Sym Atom).

Definition phf_logic_F_Tra1 (Atom : Type) : pformula_logic Atom :=
  phf_hilbert_logic (phf_hilbert_F_Tra1 Atom).

Definition phf_logic_F_Rfl_Tra1 (Atom : Type) : pformula_logic Atom :=
  phf_hilbert_logic (phf_hilbert_F_Rfl_Tra1 Atom).

(** * Factored model, frame-class, and model-class soundness *)

Theorem phf_proof_pk2_model_sound :
  forall (Atom : Type) (H : phf_hilbert Atom) p,
    phf_proof H p -> forall M : pk2_model Atom,
    (forall q, phf_schema H q -> pk2_model_valid M q) ->
    pk2_model_valid M p.
Proof.
  intros Atom H p d; induction d; intros M Hschema.
  - now apply Hschema.
  - apply pk2_valid_and1.
  - apply pk2_valid_and2.
  - apply pk2_valid_or1.
  - apply pk2_valid_or2.
  - apply pk2_valid_distribute_and_or.
  - apply pk2_valid_axiom_C.
  - apply pk2_valid_axiom_D.
  - apply pk2_valid_axiom_I.
  - apply pk2_valid_identity.
  - apply pk2_valid_efq.
  - eapply pk2_valid_modus_ponens; [apply IHd1 | apply IHd2]; exact Hschema.
  - apply pk2_valid_afortiori. now apply IHd.
  - apply pk2_valid_conjunction_rule; [apply IHd1 | apply IHd2]; exact Hschema.
Qed.

Definition phf_pk2_frame_sound {Atom : Type}
    (H : phf_hilbert Atom) (C : pk2_frame -> Prop) : Prop :=
  forall p, phf_provable H p -> pk2_frame_class_valid C p.

Definition phf_pk2_frame_complete {Atom : Type}
    (H : phf_hilbert Atom) (C : pk2_frame -> Prop) : Prop :=
  forall p, pk2_frame_class_valid C p -> phf_provable H p.

Definition phf_pk2_model_sound {Atom : Type}
    (H : phf_hilbert Atom) (C : pk2_model Atom -> Prop) : Prop :=
  forall p, phf_provable H p -> pk2_model_class_valid C p.

Theorem phf_pk2_frame_sound_of_schema :
  forall (Atom : Type) (H : phf_hilbert Atom)
         (C : pk2_frame -> Prop),
    (forall p, phf_schema H p -> pk2_frame_class_valid C p) ->
    phf_pk2_frame_sound H C.
Proof.
  intros Atom H C Hschema p [d] F HF V.
  eapply phf_proof_pk2_model_sound; [exact d |].
  intros q Hq. exact (Hschema q Hq F HF V).
Qed.

Theorem phf_pk2_model_sound_of_schema :
  forall (Atom : Type) (H : phf_hilbert Atom)
         (C : pk2_model Atom -> Prop),
    (forall p, phf_schema H p -> pk2_model_class_valid C p) ->
    phf_pk2_model_sound H C.
Proof.
  intros Atom H C Hschema p [d] M HM.
  eapply phf_proof_pk2_model_sound; [exact d |].
  intros q Hq. exact (Hschema q Hq M HM).
Qed.

Theorem phf_consistent_of_frame_sound :
  forall (Atom : Type) (H : phf_hilbert Atom)
         (C : pk2_frame -> Prop),
    phf_pk2_frame_sound H C ->
    (exists F, C F) -> phf_consistent H.
Proof.
  intros Atom H C Hsound [F HF] Hbottom.
  exact (Hsound PFalsum Hbottom F HF (fun _ _ => False) (pk2_root F)).
Qed.

Theorem phf_consistent_of_model_sound :
  forall (Atom : Type) (H : phf_hilbert Atom)
         (C : pk2_model Atom -> Prop),
    phf_pk2_model_sound H C ->
    (exists M, C M) -> phf_consistent H.
Proof.
  intros Atom H C Hsound [M HM] Hbottom.
  exact (Hsound PFalsum Hbottom M HM (pk2_root (pk2_model_frame M))).
Qed.

Theorem phf_included_of_pk2_frame_class_subset :
  forall (Atom : Type) (H K : phf_hilbert Atom)
         (C D : pk2_frame -> Prop),
    (forall F, D F -> C F) ->
    phf_pk2_frame_sound H C -> phf_pk2_frame_complete K D ->
    phf_logic_included H K.
Proof.
  intros Atom H K C D Hsub Hsound Hcomplete p Hp.
  apply Hcomplete. intros F HF. exact (Hsound p Hp F (Hsub F HF)).
Qed.

(** * Named frame classes and their sound systems *)

Definition phf_trivial_frame : pk2_frame :=
  {| pk2_world := unit;
     pk2_access := fun _ _ => True;
     pk2_root := tt;
     pk2_root_access := fun _ => I |}.

Lemma phf_trivial_reflexive : pk2_frame_reflexive phf_trivial_frame.
Proof. firstorder. Qed.

Lemma phf_trivial_symmetric : pk2_frame_symmetric phf_trivial_frame.
Proof. firstorder. Qed.

Lemma phf_trivial_transitive : pk2_frame_transitive phf_trivial_frame.
Proof. firstorder. Qed.

Theorem phf_F_pk2_sound :
  forall Atom : Type,
    phf_pk2_frame_sound (phf_hilbert_F Atom) (fun _ => True).
Proof.
  intro Atom. apply phf_pk2_frame_sound_of_schema.
  intros p H; contradiction.
Qed.

Theorem phf_F_Ser_pk2_sound :
  forall Atom : Type,
    phf_pk2_frame_sound (phf_hilbert_F_Ser Atom) pk2_frame_serial.
Proof.
  intro Atom. apply phf_pk2_frame_sound_of_schema.
  intros p -> F HF. now apply pk2_valid_ser_of_serial.
Qed.

Theorem phf_F_Rfl_pk2_sound :
  forall Atom : Type,
    phf_pk2_frame_sound (phf_hilbert_F_Rfl Atom) pk2_frame_reflexive.
Proof.
  intro Atom. apply phf_pk2_frame_sound_of_schema.
  intros s [p [q ->]] F HF. now apply pk2_valid_rfl_of_reflexive.
Qed.

Theorem phf_F_Sym_pk2_sound :
  forall Atom : Type,
    phf_pk2_frame_sound (phf_hilbert_F_Sym Atom) pk2_frame_symmetric.
Proof.
  intro Atom. apply phf_pk2_frame_sound_of_schema.
  intros s [p [q ->]] F HF. now apply pk2_valid_sym_of_symmetric.
Qed.

Theorem phf_F_Rfl_Sym_pk2_sound :
  forall Atom : Type,
    phf_pk2_frame_sound (phf_hilbert_F_Rfl_Sym Atom)
      (fun F => pk2_frame_reflexive F /\ pk2_frame_symmetric F).
Proof.
  intro Atom. apply phf_pk2_frame_sound_of_schema.
  intros s [[p [q ->]] | [p [q ->]]] F [Hrefl Hsym].
  - now apply pk2_valid_rfl_of_reflexive.
  - now apply pk2_valid_sym_of_symmetric.
Qed.

Theorem phf_F_Tra1_pk2_sound :
  forall Atom : Type,
    phf_pk2_frame_sound (phf_hilbert_F_Tra1 Atom) pk2_frame_transitive.
Proof.
  intro Atom. apply phf_pk2_frame_sound_of_schema.
  intros s [p [q [r ->]]] F HF. now apply pk2_valid_tra1_of_transitive.
Qed.

Theorem phf_F_Rfl_Tra1_pk2_sound :
  forall Atom : Type,
    phf_pk2_frame_sound (phf_hilbert_F_Rfl_Tra1 Atom)
      (fun F => pk2_frame_reflexive F /\ pk2_frame_transitive F).
Proof.
  intro Atom. apply phf_pk2_frame_sound_of_schema.
  intros s [[p [q ->]] | [p [q [r ->]]]] F [Hrefl Htrans].
  - now apply pk2_valid_rfl_of_reflexive.
  - now apply pk2_valid_tra1_of_transitive.
Qed.

Corollary phf_F_consistent :
  forall Atom : Type, phf_consistent (phf_hilbert_F Atom).
Proof.
  intro Atom. eapply phf_consistent_of_frame_sound.
  - apply phf_F_pk2_sound.
  - now exists phf_trivial_frame.
Qed.

Corollary phf_F_Ser_consistent :
  forall Atom : Type, phf_consistent (phf_hilbert_F_Ser Atom).
Proof.
  intro Atom. eapply phf_consistent_of_frame_sound.
  - apply phf_F_Ser_pk2_sound.
  - exists phf_trivial_frame. now apply pk2_reflexive_serial,
      phf_trivial_reflexive.
Qed.

Corollary phf_F_Rfl_consistent :
  forall Atom : Type, phf_consistent (phf_hilbert_F_Rfl Atom).
Proof.
  intro Atom. eapply phf_consistent_of_frame_sound.
  - apply phf_F_Rfl_pk2_sound.
  - now exists phf_trivial_frame.
Qed.

Corollary phf_F_Sym_consistent :
  forall Atom : Type, phf_consistent (phf_hilbert_F_Sym Atom).
Proof.
  intro Atom. eapply phf_consistent_of_frame_sound.
  - apply phf_F_Sym_pk2_sound.
  - now exists phf_trivial_frame.
Qed.

Corollary phf_F_Rfl_Sym_consistent :
  forall Atom : Type, phf_consistent (phf_hilbert_F_Rfl_Sym Atom).
Proof.
  intro Atom. eapply phf_consistent_of_frame_sound.
  - apply phf_F_Rfl_Sym_pk2_sound.
  - exists phf_trivial_frame; now split.
Qed.

Corollary phf_F_Tra1_consistent :
  forall Atom : Type, phf_consistent (phf_hilbert_F_Tra1 Atom).
Proof.
  intro Atom. eapply phf_consistent_of_frame_sound.
  - apply phf_F_Tra1_pk2_sound.
  - now exists phf_trivial_frame.
Qed.

Corollary phf_F_Rfl_Tra1_consistent :
  forall Atom : Type, phf_consistent (phf_hilbert_F_Rfl_Tra1 Atom).
Proof.
  intro Atom. eapply phf_consistent_of_frame_sound.
  - apply phf_F_Rfl_Tra1_pk2_sound.
  - exists phf_trivial_frame; now split.
Qed.

(** * Small counterframes used by all strictness proofs *)

Inductive phf_two_world := PHFRoot | PHFLeaf.

Definition phf_serial_nonreflexive_frame : pk2_frame :=
  {| pk2_world := phf_two_world;
     pk2_access := fun x y => x = PHFRoot \/ y = PHFRoot;
     pk2_root := PHFRoot;
     pk2_root_access := fun _ => or_introl eq_refl |}.

Lemma phf_serial_nonreflexive_serial :
  pk2_frame_serial phf_serial_nonreflexive_frame.
Proof. intros x; exists PHFRoot; now right. Qed.

Lemma phf_serial_nonreflexive_symmetric :
  pk2_frame_symmetric phf_serial_nonreflexive_frame.
Proof. intros x y [-> | ->]; [now right | now left]. Qed.

Lemma phf_serial_nonreflexive_not_reflexive :
  ~ pk2_frame_reflexive phf_serial_nonreflexive_frame.
Proof. intro H; specialize (H PHFLeaf); destruct H; discriminate. Qed.

Definition phf_reflexive_nonsymmetric_frame : pk2_frame :=
  {| pk2_world := phf_two_world;
     pk2_access := fun x y => x = PHFRoot \/ x = y;
     pk2_root := PHFRoot;
     pk2_root_access := fun _ => or_introl eq_refl |}.

Lemma phf_reflexive_nonsymmetric_reflexive :
  pk2_frame_reflexive phf_reflexive_nonsymmetric_frame.
Proof. intros x; now right. Qed.

Lemma phf_reflexive_nonsymmetric_not_symmetric :
  ~ pk2_frame_symmetric phf_reflexive_nonsymmetric_frame.
Proof.
  intro H. specialize (H PHFRoot PHFLeaf (or_introl eq_refl)).
  destruct H; discriminate.
Qed.

Inductive phf_four_world :=
| PHFGapRoot | PHFGapOne | PHFGapTwo | PHFGapThree.

Definition phf_gap_access (reflexive : bool)
    (x y : phf_four_world) : Prop :=
  x = PHFGapRoot \/
  (reflexive = true /\ x = y) \/
  (x = PHFGapOne /\ y = PHFGapTwo) \/
  (x = PHFGapTwo /\ y = PHFGapThree).

Definition phf_gap_frame (reflexive : bool) : pk2_frame :=
  {| pk2_world := phf_four_world;
     pk2_access := phf_gap_access reflexive;
     pk2_root := PHFGapRoot;
     pk2_root_access := fun _ => or_introl eq_refl |}.

Lemma phf_gap_true_reflexive : pk2_frame_reflexive (phf_gap_frame true).
Proof. intros x; right; left; auto. Qed.

Lemma phf_gap_not_transitive :
  forall b, ~ pk2_frame_transitive (phf_gap_frame b).
Proof.
  intros b H.
  specialize (H PHFGapOne PHFGapTwo PHFGapThree
    (or_intror (or_intror (or_introl (conj eq_refl eq_refl))))
    (or_intror (or_intror (or_intror (conj eq_refl eq_refl))))).
  change (phf_gap_access b PHFGapOne PHFGapThree) in H.
  unfold phf_gap_access in H.
  destruct H as [Hroot | [Href | [H12 | H23]]].
  - discriminate Hroot.
  - destruct Href as [_ Heq]. discriminate Heq.
  - destruct H12 as [_ Heq]. discriminate Heq.
  - destruct H23 as [Heq _]. discriminate Heq.
Qed.

Lemma pk2_K_counter_not_serial :
  ~ pk2_frame_serial pk2_K_counter_frame.
Proof.
  intro H. destruct (H PK2KTwo) as [y Hy].
  destruct Hy as [Hy | [Hy _]]; discriminate.
Qed.

Lemma pk2_K_counter_transitive :
  pk2_frame_transitive pk2_K_counter_frame.
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy as [-> | [-> ->]]; [now left |].
  destruct Hyz as [H | [H _]]; discriminate.
Qed.

(** * Nonprovability and strict hierarchy *)

Theorem phf_F_unprovable_noncontradiction :
  ~ phf_provable (phf_hilbert_F nat)
      (pneg (PAnd (PAtom 0) (pneg (PAtom 0)))).
Proof.
  intro Hproof.
  pose proof (@phf_F_pk2_sound nat _ Hproof pk2_K_counter_frame I
    pk2_K_counter_valuation PK2KRoot) as Hvalid.
  apply (Hvalid PK2KOne (or_introl eq_refl)). split; [reflexivity |].
  intros z R1z Hz.
  destruct R1z as [H | [_ Hz2]]; [discriminate H |].
  rewrite Hz2 in Hz. discriminate Hz.
Qed.

Theorem phf_F_strictly_included_F_Ser :
  phf_logic_strictly_included
    (phf_hilbert_F nat) (phf_hilbert_F_Ser nat).
Proof.
  split.
  - intros p. now apply phf_provable_of_schema_inclusion,
      phf_F_schema_in_F_Ser.
  - exists (@pk2_axiom_ser nat); split.
    + apply phf_provable_of_schema. reflexivity.
    + intro Hproof.
      pose proof (@phf_F_pk2_sound nat _ Hproof pk2_K_counter_frame I)
        as Hvalid.
      specialize (Hvalid (fun _ _ => False) PK2KRoot).
      apply (Hvalid PK2KTwo (or_introl eq_refl)).
      intros y R2y _. destruct R2y as [H | [H _]]; discriminate.
Qed.

Theorem phf_F_strictly_included_F_Sym :
  phf_logic_strictly_included
    (phf_hilbert_F nat) (phf_hilbert_F_Sym nat).
Proof.
  split.
  - intros p. now apply phf_provable_of_schema_inclusion,
      phf_F_schema_in_F_Sym.
  - exists (pk2_axiom_sym (PAtom 0) (PAtom 1)); split.
    + apply phf_provable_of_schema. now exists (PAtom 0), (PAtom 1).
    + intro Hproof.
      pose proof (@phf_F_pk2_sound nat _ Hproof
        phf_reflexive_nonsymmetric_frame I) as Hvalid.
      apply pk2_symmetric_of_valid_sym in Hvalid.
      exact (phf_reflexive_nonsymmetric_not_symmetric Hvalid).
Qed.

Theorem phf_F_strictly_included_F_Tra1 :
  phf_logic_strictly_included
    (phf_hilbert_F nat) (phf_hilbert_F_Tra1 nat).
Proof.
  split.
  - intros p. now apply phf_provable_of_schema_inclusion,
      phf_F_schema_in_F_Tra1.
  - exists (pk2_axiom_tra1 (PAtom 0) (PAtom 1) (PAtom 2)); split.
    + apply phf_provable_of_schema.
      now exists (PAtom 0), (PAtom 1), (PAtom 2).
    + intro Hproof.
      pose proof (@phf_F_pk2_sound nat _ Hproof (phf_gap_frame false) I)
        as Hvalid.
      apply pk2_transitive_of_valid_tra1 in Hvalid.
      exact (@phf_gap_not_transitive false Hvalid).
Qed.

Theorem phf_F_Rfl_not_included_F_Ser :
  ~ phf_logic_included
      (phf_hilbert_F_Rfl nat) (phf_hilbert_F_Ser nat).
Proof.
  intro Hinc.
  specialize (Hinc (pk2_axiom_rfl (PAtom 0) (PAtom 1))).
  assert (Hrfl : phf_provable (phf_hilbert_F_Rfl nat)
      (pk2_axiom_rfl (PAtom 0) (PAtom 1))).
  { apply phf_provable_of_schema. now exists (PAtom 0), (PAtom 1). }
  specialize (Hinc Hrfl).
  pose proof (@phf_F_Ser_pk2_sound nat _ Hinc
    phf_serial_nonreflexive_frame phf_serial_nonreflexive_serial) as Hvalid.
  apply pk2_reflexive_of_valid_rfl in Hvalid.
  exact (phf_serial_nonreflexive_not_reflexive Hvalid).
Qed.

Theorem phf_F_Rfl_strictly_included_F_Rfl_Sym :
  phf_logic_strictly_included
    (phf_hilbert_F_Rfl nat) (phf_hilbert_F_Rfl_Sym nat).
Proof.
  split.
  - intros p. now apply phf_provable_of_schema_inclusion,
      phf_F_Rfl_schema_in_F_Rfl_Sym.
  - exists (pk2_axiom_sym (PAtom 0) (PAtom 1)); split.
    + apply phf_provable_of_schema. right.
      now exists (PAtom 0), (PAtom 1).
    + intro Hproof.
      pose proof (@phf_F_Rfl_pk2_sound nat _ Hproof
        phf_reflexive_nonsymmetric_frame
        phf_reflexive_nonsymmetric_reflexive) as Hvalid.
      apply pk2_symmetric_of_valid_sym in Hvalid.
      exact (phf_reflexive_nonsymmetric_not_symmetric Hvalid).
Qed.

Theorem phf_F_Sym_strictly_included_F_Rfl_Sym :
  phf_logic_strictly_included
    (phf_hilbert_F_Sym nat) (phf_hilbert_F_Rfl_Sym nat).
Proof.
  split.
  - intros p. now apply phf_provable_of_schema_inclusion,
      phf_F_Sym_schema_in_F_Rfl_Sym.
  - exists (pk2_axiom_rfl (PAtom 0) (PAtom 1)); split.
    + apply phf_provable_of_schema. left.
      now exists (PAtom 0), (PAtom 1).
    + intro Hproof.
      pose proof (@phf_F_Sym_pk2_sound nat _ Hproof
        phf_serial_nonreflexive_frame
        phf_serial_nonreflexive_symmetric) as Hvalid.
      apply pk2_reflexive_of_valid_rfl in Hvalid.
      exact (phf_serial_nonreflexive_not_reflexive Hvalid).
Qed.

Theorem phf_F_Rfl_strictly_included_F_Rfl_Tra1 :
  phf_logic_strictly_included
    (phf_hilbert_F_Rfl nat) (phf_hilbert_F_Rfl_Tra1 nat).
Proof.
  split.
  - intros p. now apply phf_provable_of_schema_inclusion,
      phf_F_Rfl_schema_in_F_Rfl_Tra1.
  - exists (pk2_axiom_tra1 (PAtom 0) (PAtom 1) (PAtom 2)); split.
    + apply phf_provable_of_schema. right.
      now exists (PAtom 0), (PAtom 1), (PAtom 2).
    + intro Hproof.
      pose proof (@phf_F_Rfl_pk2_sound nat _ Hproof (phf_gap_frame true)
        phf_gap_true_reflexive) as Hvalid.
      apply pk2_transitive_of_valid_tra1 in Hvalid.
      exact (@phf_gap_not_transitive true Hvalid).
Qed.

Theorem phf_F_Tra1_strictly_included_F_Rfl_Tra1 :
  phf_logic_strictly_included
    (phf_hilbert_F_Tra1 nat) (phf_hilbert_F_Rfl_Tra1 nat).
Proof.
  split.
  - intros p. now apply phf_provable_of_schema_inclusion,
      phf_F_Tra1_schema_in_F_Rfl_Tra1.
  - exists (pk2_axiom_rfl (PAtom 0) (PAtom 1)); split.
    + apply phf_provable_of_schema. left.
      now exists (PAtom 0), (PAtom 1).
    + intro Hproof.
      pose proof (@phf_F_Tra1_pk2_sound nat _ Hproof pk2_K_counter_frame
        pk2_K_counter_transitive) as Hvalid.
      apply pk2_reflexive_of_valid_rfl in Hvalid.
      apply pk2_K_counter_not_serial.
      now apply pk2_reflexive_serial.
Qed.
