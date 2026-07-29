(** Hilbert WF as Hilbert VF extended by replacement of equivalents.

    This ports Foundation/Propositional/Hilbert/WF/Basic and
    Foundation/Propositional/Hilbert/WF_VF.  WF and VF have exactly the same
    substitution-closed schema structure, so that representation is shared;
    the faithful WF proof type adds only Rule E.  Structural transports are
    nevertheless defined directly over WF proofs, allowing translated schema
    proofs themselves to use Rule E. *)

From Stdlib Require Import Arith.PeanoNat Lia.
From FoundationModal Require Import
  PropositionalFormula PropositionalLogic PropositionalHilbert
  PropositionalHilbertVF PropositionalKripke2Hilbert
  PropositionalHilbertFExtensions PropositionalFMT
  PropositionalFMTCompleteness.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Shared schema representation *)

Definition phwf_hilbert (Atom : Type) : Type := phvf_hilbert Atom.

Definition phwf_schema {Atom : Type}
    (H : phwf_hilbert Atom) (p : pformula Atom) : Prop :=
  phvf_schema H p.

Lemma phwf_schema_substitute :
  forall (Atom : Type) (H : phwf_hilbert Atom) p,
    phwf_schema H p -> forall sigma : psubstitution Atom Atom,
    phwf_schema H (pformula_substitute sigma p).
Proof. intros Atom H p Hp sigma; exact (phvf_schema_substitute H p Hp sigma). Qed.

Definition phwf_hilbert_WF (Atom : Type) : phwf_hilbert Atom :=
  phvf_hilbert_VF Atom.

Definition phwf_iff {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  phf_iff p q.

(** * Faithful WF proofs *)

Inductive phwf_proof {Atom : Type} (H : phwf_hilbert Atom) :
    pformula Atom -> Type :=
| PHWFPAxiom : forall p, phwf_schema H p -> phwf_proof H p
| PHWFPAndElimL : forall p q, phwf_proof H (ph_axiom_and1 p q)
| PHWFPAndElimR : forall p q, phwf_proof H (ph_axiom_and2 p q)
| PHWFPOrIntroL : forall p q, phwf_proof H (ph_axiom_or1 p q)
| PHWFPOrIntroR : forall p q, phwf_proof H (ph_axiom_or2 p q)
| PHWFPDistributeAndOr : forall p q r,
    phwf_proof H (phvf_distribute_and_or p q r)
| PHWFPIdentity : forall p, phwf_proof H (PImp p p)
| PHWFPEfq : forall p, phwf_proof H (ph_axiom_efq p)
| PHWFPModusPonens : forall p q,
    phwf_proof H (PImp p q) -> phwf_proof H p -> phwf_proof H q
| PHWFPFortiori : forall p q,
    phwf_proof H p -> phwf_proof H (PImp q p)
| PHWFPAndRule : forall p q,
    phwf_proof H p -> phwf_proof H q -> phwf_proof H (PAnd p q)
| PHWFPRuleC : forall p q r,
    phwf_proof H (PImp p q) -> phwf_proof H (PImp p r) ->
    phwf_proof H (PImp p (PAnd q r))
| PHWFPRuleD : forall p q r,
    phwf_proof H (PImp p r) -> phwf_proof H (PImp q r) ->
    phwf_proof H (PImp (POr p q) r)
| PHWFPRuleI : forall p q r,
    phwf_proof H (PImp p q) -> phwf_proof H (PImp q r) ->
    phwf_proof H (PImp p r)
| PHWFPRuleE : forall p q r s,
    phwf_proof H (phwf_iff p q) -> phwf_proof H (phwf_iff r s) ->
    phwf_proof H (phwf_iff (PImp p r) (PImp q s)).

Arguments PHWFPAxiom {Atom H p} _.
Arguments PHWFPAndElimL {Atom H} p q.
Arguments PHWFPAndElimR {Atom H} p q.
Arguments PHWFPOrIntroL {Atom H} p q.
Arguments PHWFPOrIntroR {Atom H} p q.
Arguments PHWFPDistributeAndOr {Atom H} p q r.
Arguments PHWFPIdentity {Atom H} p.
Arguments PHWFPEfq {Atom H} p.
Arguments PHWFPModusPonens {Atom H p q} _ _.
Arguments PHWFPFortiori {Atom H p} q _.
Arguments PHWFPAndRule {Atom H p q} _ _.
Arguments PHWFPRuleC {Atom H p q r} _ _.
Arguments PHWFPRuleD {Atom H p q r} _ _.
Arguments PHWFPRuleI {Atom H p q r} _ _.
Arguments PHWFPRuleE {Atom H p q r s} _ _.

Definition phwf_provable {Atom : Type}
    (H : phwf_hilbert Atom) (p : pformula Atom) : Prop :=
  inhabited (phwf_proof H p).

Lemma phwf_provable_of_schema :
  forall (Atom : Type) (H : phwf_hilbert Atom) p,
    phwf_schema H p -> phwf_provable H p.
Proof. intros Atom H p Hp; constructor; now apply PHWFPAxiom. Qed.

(** One map over raw proofs factors schema weakening. *)
Fixpoint phwf_proof_of_schema_inclusion {Atom : Type}
    {H K : phwf_hilbert Atom}
    (Hinc : forall p, phwf_schema H p -> phwf_schema K p)
    {p} (d : phwf_proof H p) : phwf_proof K p.
Proof.
  destruct d.
  - apply PHWFPAxiom, Hinc; assumption.
  - apply PHWFPAndElimL.
  - apply PHWFPAndElimR.
  - apply PHWFPOrIntroL.
  - apply PHWFPOrIntroR.
  - apply PHWFPDistributeAndOr.
  - apply PHWFPIdentity.
  - apply PHWFPEfq.
  - exact (PHWFPModusPonens
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHWFPFortiori _
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d)).
  - exact (PHWFPAndRule
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHWFPRuleC
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHWFPRuleD
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHWFPRuleI
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
  - exact (PHWFPRuleE
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d1)
      (@phwf_proof_of_schema_inclusion Atom H K Hinc _ d2)).
Defined.

Lemma phwf_provable_of_schema_inclusion :
  forall (Atom : Type) (H K : phwf_hilbert Atom),
    (forall p, phwf_schema H p -> phwf_schema K p) ->
    forall p, phwf_provable H p -> phwf_provable K p.
Proof.
  intros Atom H K Hinc p [d]. constructor.
  exact (@phwf_proof_of_schema_inclusion Atom H K Hinc p d).
Qed.

(** Substitution is proved once over all fifteen constructors. *)
Fixpoint phwf_proof_substitute {Atom : Type} {H : phwf_hilbert Atom}
    (sigma : psubstitution Atom Atom) {p} (d : phwf_proof H p) :
    phwf_proof H (pformula_substitute sigma p).
Proof.
  destruct d; cbn [ph_axiom_and1 ph_axiom_and2 ph_axiom_or1 ph_axiom_or2
    phvf_distribute_and_or ph_axiom_efq phwf_iff].
  - apply PHWFPAxiom. now apply phwf_schema_substitute.
  - apply PHWFPAndElimL.
  - apply PHWFPAndElimR.
  - apply PHWFPOrIntroL.
  - apply PHWFPOrIntroR.
  - apply PHWFPDistributeAndOr.
  - apply PHWFPIdentity.
  - apply PHWFPEfq.
  - exact (PHWFPModusPonens (@phwf_proof_substitute Atom H sigma _ d1)
      (@phwf_proof_substitute Atom H sigma _ d2)).
  - exact (PHWFPFortiori _ (@phwf_proof_substitute Atom H sigma _ d)).
  - exact (PHWFPAndRule (@phwf_proof_substitute Atom H sigma _ d1)
      (@phwf_proof_substitute Atom H sigma _ d2)).
  - exact (PHWFPRuleC (@phwf_proof_substitute Atom H sigma _ d1)
      (@phwf_proof_substitute Atom H sigma _ d2)).
  - exact (PHWFPRuleD (@phwf_proof_substitute Atom H sigma _ d1)
      (@phwf_proof_substitute Atom H sigma _ d2)).
  - exact (PHWFPRuleI (@phwf_proof_substitute Atom H sigma _ d1)
      (@phwf_proof_substitute Atom H sigma _ d2)).
  - exact (PHWFPRuleE (@phwf_proof_substitute Atom H sigma _ d1)
      (@phwf_proof_substitute Atom H sigma _ d2)).
Defined.

Lemma phwf_provable_substitute :
  forall (Atom : Type) (H : phwf_hilbert Atom)
      (sigma : psubstitution Atom Atom) p,
    phwf_provable H p ->
    phwf_provable H (pformula_substitute sigma p).
Proof.
  intros Atom H sigma p [d]. constructor.
  exact (@phwf_proof_substitute Atom H sigma p d).
Qed.

(** Provable-schema transport permits Rule E inside translated axioms. *)
Fixpoint phwf_proof_of_proof_schema {Atom : Type}
    {H K : phwf_hilbert Atom}
    (Hschema : forall p, phwf_schema H p -> phwf_proof K p)
    {p} (d : phwf_proof H p) : phwf_proof K p.
Proof.
  destruct d.
  - now apply Hschema.
  - apply PHWFPAndElimL.
  - apply PHWFPAndElimR.
  - apply PHWFPOrIntroL.
  - apply PHWFPOrIntroR.
  - apply PHWFPDistributeAndOr.
  - apply PHWFPIdentity.
  - apply PHWFPEfq.
  - exact (PHWFPModusPonens
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHWFPFortiori _
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d)).
  - exact (PHWFPAndRule
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHWFPRuleC
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHWFPRuleD
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHWFPRuleI
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d2)).
  - exact (PHWFPRuleE
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d1)
      (@phwf_proof_of_proof_schema Atom H K Hschema _ d2)).
Defined.

Lemma phwf_provable_of_provable_schema :
  forall (Atom : Type) (H K : phwf_hilbert Atom),
    (forall p, phwf_schema H p -> phwf_provable K p) ->
    forall p, phwf_provable H p -> phwf_provable K p.
Proof.
  intros Atom H K Hschema p [d]. constructor.
  exact (@phwf_proof_of_proof_schema Atom H K
    (fun q Hq => ph_inhabited_get (Hschema q Hq)) p d).
Qed.

(** * Logic packaging *)

Definition phwf_logic_included {Atom : Type}
    (H K : phwf_hilbert Atom) : Prop :=
  forall p, phwf_provable H p -> phwf_provable K p.

Definition phwf_hilbert_logic {Atom : Type}
    (H : phwf_hilbert Atom) : pformula_logic Atom.
Proof.
  refine {| pformula_logic_theorems := phwf_provable H |}.
  - intros sigma p Hp. exact (phwf_provable_substitute sigma Hp).
  - intros p q [Hpq] [Hp]. constructor. exact (PHWFPModusPonens Hpq Hp).
Defined.

Lemma phwf_hilbert_logic_iff_provable :
  forall (Atom : Type) (H : phwf_hilbert Atom) p,
    pformula_logic_theorems (phwf_hilbert_logic H) p <->
    phwf_provable H p.
Proof. reflexivity. Qed.

Lemma phwf_hilbert_logic_subset_of_schema_inclusion :
  forall (Atom : Type) (H K : phwf_hilbert Atom),
    (forall p, phwf_schema H p -> phwf_schema K p) ->
    pformula_logic_subset (phwf_hilbert_logic H) (phwf_hilbert_logic K).
Proof. intros Atom H K Hinc p Hp; now apply phwf_provable_of_schema_inclusion with H. Qed.

Lemma phwf_hilbert_logic_subset_of_provable_schema :
  forall (Atom : Type) (H K : phwf_hilbert Atom),
    (forall p, phwf_schema H p -> phwf_provable K p) ->
    pformula_logic_subset (phwf_hilbert_logic H) (phwf_hilbert_logic K).
Proof. intros Atom H K Hschema p Hp; now apply phwf_provable_of_provable_schema with H. Qed.

Definition phwf_logic_WF (Atom : Type) : pformula_logic Atom :=
  phwf_hilbert_logic (phwf_hilbert_WF Atom).

(** * VF-to-WF transport *)

Fixpoint phvf_proof_to_phwf {Atom : Type}
    {Hv : phvf_hilbert Atom} {Hw : phwf_hilbert Atom}
    (Hschema : forall p, phvf_schema Hv p -> phwf_proof Hw p)
    {p} (d : phvf_proof Hv p) : phwf_proof Hw p.
Proof.
  destruct d.
  - now apply Hschema.
  - apply PHWFPAndElimL.
  - apply PHWFPAndElimR.
  - apply PHWFPOrIntroL.
  - apply PHWFPOrIntroR.
  - apply PHWFPDistributeAndOr.
  - apply PHWFPIdentity.
  - apply PHWFPEfq.
  - exact (PHWFPModusPonens
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d1)
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d2)).
  - exact (PHWFPFortiori _
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d)).
  - exact (PHWFPAndRule
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d1)
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d2)).
  - exact (PHWFPRuleC
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d1)
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d2)).
  - exact (PHWFPRuleD
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d1)
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d2)).
  - exact (PHWFPRuleI
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d1)
      (@phvf_proof_to_phwf Atom Hv Hw Hschema _ d2)).
Defined.

Definition phvf_phwf_included {Atom : Type}
    (Hv : phvf_hilbert Atom) (Hw : phwf_hilbert Atom) : Prop :=
  forall p, phvf_provable Hv p -> phwf_provable Hw p.

Theorem phvf_phwf_included_of_provable_schema :
  forall (Atom : Type) (Hv : phvf_hilbert Atom) (Hw : phwf_hilbert Atom),
    (forall p, phvf_schema Hv p -> phwf_provable Hw p) ->
    phvf_phwf_included Hv Hw.
Proof.
  intros Atom Hv Hw Hschema p [d]. constructor.
  exact (@phvf_proof_to_phwf Atom Hv Hw
    (fun q Hq => ph_inhabited_get (Hschema q Hq)) p d).
Qed.

Corollary phvf_VF_included_phwf_WF : forall Atom : Type,
  phvf_phwf_included (phvf_hilbert_VF Atom) (phwf_hilbert_WF Atom).
Proof.
  intro Atom. apply phvf_phwf_included_of_provable_schema.
  intros p H; contradiction.
Qed.

(** * WF-to-F transport *)

Fixpoint phwf_proof_to_phf {Atom : Type}
    {Hw : phwf_hilbert Atom} {Hf : phf_hilbert Atom}
    (Hschema : forall p, phwf_schema Hw p -> phf_proof Hf p)
    {p} (d : phwf_proof Hw p) : phf_proof Hf p.
Proof.
  destruct d.
  - now apply Hschema.
  - apply PHFPAndElimL.
  - apply PHFPAndElimR.
  - apply PHFPOrIntroL.
  - apply PHFPOrIntroR.
  - apply PHFPDistributeAndOr.
  - apply PHFPIdentity.
  - apply PHFPEfq.
  - exact (PHFPModusPonens
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d1)
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d2)).
  - exact (PHFPAFortiori _
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d)).
  - exact (PHFPAndRule
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d1)
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d2)).
  - exact (phf_proof_rule_C
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d1)
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d2)).
  - exact (phf_proof_rule_D
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d1)
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d2)).
  - exact (phf_proof_rule_I
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d1)
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d2)).
  - exact (phf_proof_rule_E
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d1)
      (@phwf_proof_to_phf Atom Hw Hf Hschema _ d2)).
Defined.

Definition phwf_phf_included {Atom : Type}
    (Hw : phwf_hilbert Atom) (Hf : phf_hilbert Atom) : Prop :=
  forall p, phwf_provable Hw p -> phf_provable Hf p.

Theorem phwf_phf_included_of_provable_schema :
  forall (Atom : Type) (Hw : phwf_hilbert Atom) (Hf : phf_hilbert Atom),
    (forall p, phwf_schema Hw p -> phf_provable Hf p) ->
    phwf_phf_included Hw Hf.
Proof.
  intros Atom Hw Hf Hschema p [d]. constructor.
  exact (@phwf_proof_to_phf Atom Hw Hf
    (fun q Hq => ph_inhabited_get (Hschema q Hq)) p d).
Qed.

Corollary phwf_WF_included_phf_F : forall Atom : Type,
  phwf_phf_included (phwf_hilbert_WF Atom) (phf_hilbert_F Atom).
Proof.
  intro Atom. apply phwf_phf_included_of_provable_schema.
  intros p H; contradiction.
Qed.

(** * Strict VF-below-WF separation *)

Definition phwf_separation_left : pformula nat :=
  PImp ptop (PAnd (PAtom 0) (PAtom 1)).

Definition phwf_separation_right : pformula nat :=
  PImp ptop (PAnd (PAtom 1) (PAtom 0)).

Definition phwf_separation_formula : pformula nat :=
  phwf_iff phwf_separation_left phwf_separation_right.

Definition phwf_proof_separation :
  phwf_proof (phwf_hilbert_WF nat) phwf_separation_formula.
Proof.
  apply PHWFPRuleE.
  - apply PHWFPAndRule; apply PHWFPIdentity.
  - apply PHWFPAndRule.
    + exact (PHWFPRuleC
        (PHWFPAndElimR (PAtom 0) (PAtom 1))
        (PHWFPAndElimL (PAtom 0) (PAtom 1))).
    + exact (PHWFPRuleC
        (PHWFPAndElimR (PAtom 1) (PAtom 0))
        (PHWFPAndElimL (PAtom 1) (PAtom 0))).
Defined.

Theorem phwf_WF_provable_separation :
  phwf_provable (phwf_hilbert_WF nat) phwf_separation_formula.
Proof. constructor; exact phwf_proof_separation. Qed.

Inductive phwf_separation_world : Type :=
| PHWFSRoot | PHWFSGap | PHWFSEnd.

Lemma phwf_separation_left_neq_right :
  phwf_separation_left <> phwf_separation_right.
Proof. unfold phwf_separation_left, phwf_separation_right; congruence. Qed.

Definition phwf_separation_access (indexed : pformula nat)
    (x y : phwf_separation_world) : Prop :=
  if pformula_eq_dec Nat.eq_dec indexed phwf_separation_right
  then x = PHWFSRoot \/ (x = PHWFSGap /\ y = PHWFSEnd)
  else if pformula_eq_dec Nat.eq_dec indexed phwf_separation_left
  then x = PHWFSRoot
  else True.

Lemma phwf_separation_root_access : forall indexed y,
  phwf_separation_access indexed PHWFSRoot y.
Proof.
  intros indexed y. unfold phwf_separation_access.
  destruct (pformula_eq_dec Nat.eq_dec indexed phwf_separation_right);
    [now left |].
  destruct (pformula_eq_dec Nat.eq_dec indexed phwf_separation_left);
    [reflexivity | exact I].
Qed.

Definition phwf_separation_frame : fmt_frame :=
  {| fmt_world := phwf_separation_world;
     fmt_access := phwf_separation_access;
     fmt_root := PHWFSRoot;
     fmt_root_access := phwf_separation_root_access |}.

Definition phwf_separation_model : fmt_model :=
  {| fmt_model_frame := phwf_separation_frame;
     fmt_model_valuation := fun a x => x = PHWFSEnd /\ a = 0 |}.

Lemma phwf_separation_no_left_from_gap : forall y,
  ~ phwf_separation_access phwf_separation_left PHWFSGap y.
Proof.
  intro y. unfold phwf_separation_access.
  destruct (pformula_eq_dec Nat.eq_dec
    phwf_separation_left phwf_separation_right) as [Heq | Hne].
  - contradiction phwf_separation_left_neq_right.
  - destruct (pformula_eq_dec Nat.eq_dec
      phwf_separation_left phwf_separation_left) as [_ | Hfalse].
    + discriminate.
    + contradiction Hfalse; reflexivity.
Qed.

Lemma phwf_separation_right_gap_end :
  phwf_separation_access phwf_separation_right PHWFSGap PHWFSEnd.
Proof.
  unfold phwf_separation_access.
  destruct (pformula_eq_dec Nat.eq_dec
    phwf_separation_right phwf_separation_right) as [_ | Hfalse].
  - now right.
  - contradiction Hfalse; reflexivity.
Qed.

Lemma phwf_separation_forces_left_gap :
  fmt_forces phwf_separation_model PHWFSGap phwf_separation_left.
Proof.
  intros y Haccess _. exfalso.
  change phwf_separation_world in y.
  change (phwf_separation_access
    phwf_separation_left PHWFSGap y) in Haccess.
  exact (@phwf_separation_no_left_from_gap y Haccess).
Qed.

Lemma phwf_separation_not_forces_right_gap :
  ~ fmt_forces phwf_separation_model PHWFSGap phwf_separation_right.
Proof.
  intro Hright.
  specialize (Hright PHWFSEnd phwf_separation_right_gap_end
    (@fmt_forces_top phwf_separation_model PHWFSEnd)).
  destruct Hright as [Hatom1 _]. cbn in Hatom1. lia.
Qed.

Theorem phwf_separation_countermodel :
  ~ fmt_forces phwf_separation_model PHWFSRoot phwf_separation_formula.
Proof.
  unfold phwf_separation_formula, phwf_iff, phf_iff.
  intros [Hforward _]. apply phwf_separation_not_forces_right_gap.
  exact (Hforward PHWFSGap
    (phwf_separation_root_access
      (PImp phwf_separation_left phwf_separation_right) PHWFSGap)
    phwf_separation_forces_left_gap).
Qed.

Theorem phvf_VF_unprovable_phwf_separation :
  ~ phvf_provable (phvf_hilbert_VF nat) phwf_separation_formula.
Proof.
  intro Hprov. apply phwf_separation_countermodel.
  exact (@phvf_VF_fmt_sound phwf_separation_formula Hprov
    phwf_separation_frame I
    (@fmt_model_valuation phwf_separation_model) PHWFSRoot).
Qed.

Definition phvf_phwf_strictly_included {Atom : Type}
    (Hv : phvf_hilbert Atom) (Hw : phwf_hilbert Atom) : Prop :=
  phvf_phwf_included Hv Hw /\
  exists p, phwf_provable Hw p /\ ~ phvf_provable Hv p.

Theorem phvf_VF_strictly_included_phwf_WF :
  phvf_phwf_strictly_included
    (phvf_hilbert_VF nat) (phwf_hilbert_WF nat).
Proof.
  split.
  - apply phvf_VF_included_phwf_WF.
  - exists phwf_separation_formula. split.
    + apply phwf_WF_provable_separation.
    + apply phvf_VF_unprovable_phwf_separation.
Qed.
