(** Hilbert WF as Hilbert VF extended by replacement of equivalents.

    This ports Foundation/Propositional/Hilbert/WF/Basic and
    Foundation/Propositional/Hilbert/WF_VF.  WF and VF have exactly the same
    substitution-closed schema structure, so that representation is shared;
    the faithful WF proof type adds only Rule E.  Structural transports are
    nevertheless defined directly over WF proofs, allowing translated schema
    proofs themselves to use Rule E. *)

From FoundationModal Require Import
  PropositionalFormula PropositionalLogic PropositionalHilbert
  PropositionalHilbertVF.

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
  PAnd (PImp p q) (PImp q p).

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
