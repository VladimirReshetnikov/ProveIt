(**
  Schema-generated Minimal and intermediate propositional Hilbert systems.

  This module ports [Propositional/Hilbert/Minimal/Basic.lean].  All systems
  share one Type-valued proof datatype.  A single proof-map recursor factors
  both schema inclusion and translation by provable schemata; substitution
  has its own dependent structural recursor because it changes the conclusion.
*)

From Stdlib Require Import Logic.ClassicalEpsilon.
From FoundationModal Require Import
  GenericSemantics GenericLogicSymbol GenericEntailment GenericCalculus
  PropositionalEntailmentAxioms PropositionalEntailmentMinimal
  PropositionalFormula PropositionalLogic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Named propositional schemata *)

Definition ph_axiom_K {Atom : Type} (p q : pformula Atom) : pformula Atom :=
  generic_axiom_K (pformula_connectives Atom) p q.

Definition ph_axiom_S {Atom : Type}
    (p q r : pformula Atom) : pformula Atom :=
  generic_axiom_S (pformula_connectives Atom) p q r.

Definition ph_axiom_and1 {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  generic_axiom_and1 (pformula_connectives Atom) p q.

Definition ph_axiom_and2 {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  generic_axiom_and2 (pformula_connectives Atom) p q.

Definition ph_axiom_and3 {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  generic_axiom_and3 (pformula_connectives Atom) p q.

Definition ph_axiom_or1 {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  generic_axiom_or1 (pformula_connectives Atom) p q.

Definition ph_axiom_or2 {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  generic_axiom_or2 (pformula_connectives Atom) p q.

Definition ph_axiom_or3 {Atom : Type}
    (p q r : pformula Atom) : pformula Atom :=
  generic_axiom_or3 (pformula_connectives Atom) p q r.

Definition ph_axiom_efq {Atom : Type} (p : pformula Atom) : pformula Atom :=
  PImp PFalsum p.

Definition ph_axiom_wlem {Atom : Type} (p : pformula Atom) : pformula Atom :=
  POr (pneg p) (pneg (pneg p)).

Definition ph_axiom_dummett {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  POr (PImp p q) (PImp q p).

Definition ph_axiom_kreisel_putnam {Atom : Type}
    (p q r : pformula Atom) : pformula Atom :=
  PImp (PImp (pneg p) (POr q r))
    (POr (PImp (pneg p) q) (PImp (pneg p) r)).

Definition ph_axiom_lem {Atom : Type} (p : pformula Atom) : pformula Atom :=
  POr p (pneg p).

(** * Substitution-closed schema systems *)

Record ph_hilbert (Atom : Type) : Type := {
  ph_hilbert_schema : pformula Atom -> Prop;
  ph_hilbert_schema_substitute :
    forall p, ph_hilbert_schema p ->
    forall sigma : psubstitution Atom Atom,
      ph_hilbert_schema (pformula_substitute sigma p)
}.

Arguments ph_hilbert_schema {Atom} _ _.
Arguments ph_hilbert_schema_substitute {Atom} _ _ _ _.

Inductive ph_int_schema {Atom : Type} : pformula Atom -> Prop :=
| PHIntEFQ : forall p, ph_int_schema (ph_axiom_efq p).

Inductive ph_kc_schema {Atom : Type} : pformula Atom -> Prop :=
| PHKCEfq : forall p, ph_kc_schema (ph_axiom_efq p)
| PHKCWlem : forall p, ph_kc_schema (ph_axiom_wlem p).

Inductive ph_lc_schema {Atom : Type} : pformula Atom -> Prop :=
| PHLCEfq : forall p, ph_lc_schema (ph_axiom_efq p)
| PHLCDummett : forall p q, ph_lc_schema (ph_axiom_dummett p q).

Inductive ph_kp_schema {Atom : Type} : pformula Atom -> Prop :=
| PHKPEfq : forall p, ph_kp_schema (ph_axiom_efq p)
| PHKPKreiselPutnam : forall p q r,
    ph_kp_schema (ph_axiom_kreisel_putnam p q r).

Inductive ph_cl_schema {Atom : Type} : pformula Atom -> Prop :=
| PHClEfq : forall p, ph_cl_schema (ph_axiom_efq p)
| PHClLem : forall p, ph_cl_schema (ph_axiom_lem p).

Definition ph_hilbert_min (Atom : Type) : ph_hilbert Atom.
Proof.
  refine {| ph_hilbert_schema := fun _ => False |}.
  intros p H. contradiction.
Defined.

Definition ph_hilbert_int (Atom : Type) : ph_hilbert Atom.
Proof.
  refine {| ph_hilbert_schema := ph_int_schema |}.
  intros p H sigma. destruct H. constructor.
Defined.

Definition ph_hilbert_kc (Atom : Type) : ph_hilbert Atom.
Proof.
  refine {| ph_hilbert_schema := ph_kc_schema |}.
  intros p H sigma. destruct H; constructor.
Defined.

Definition ph_hilbert_lc (Atom : Type) : ph_hilbert Atom.
Proof.
  refine {| ph_hilbert_schema := ph_lc_schema |}.
  intros p H sigma. destruct H; constructor.
Defined.

Definition ph_hilbert_kp (Atom : Type) : ph_hilbert Atom.
Proof.
  refine {| ph_hilbert_schema := ph_kp_schema |}.
  intros p H sigma. destruct H; constructor.
Defined.

Definition ph_hilbert_cl (Atom : Type) : ph_hilbert Atom.
Proof.
  refine {| ph_hilbert_schema := ph_cl_schema |}.
  intros p H sigma. destruct H; constructor.
Defined.

Lemma ph_hilbert_int_le_kc :
  forall (Atom : Type) p,
    ph_hilbert_schema (ph_hilbert_int Atom) p ->
    ph_hilbert_schema (ph_hilbert_kc Atom) p.
Proof. intros Atom p H; destruct H; constructor. Qed.

Lemma ph_hilbert_int_le_lc :
  forall (Atom : Type) p,
    ph_hilbert_schema (ph_hilbert_int Atom) p ->
    ph_hilbert_schema (ph_hilbert_lc Atom) p.
Proof. intros Atom p H; destruct H; constructor. Qed.

Lemma ph_hilbert_int_le_kp :
  forall (Atom : Type) p,
    ph_hilbert_schema (ph_hilbert_int Atom) p ->
    ph_hilbert_schema (ph_hilbert_kp Atom) p.
Proof. intros Atom p H; destruct H; constructor. Qed.

Lemma ph_hilbert_int_le_cl :
  forall (Atom : Type) p,
    ph_hilbert_schema (ph_hilbert_int Atom) p ->
    ph_hilbert_schema (ph_hilbert_cl Atom) p.
Proof. intros Atom p H; destruct H; constructor. Qed.

(** * One shared raw proof datatype *)

Inductive ph_hilbert_proof {Atom : Type} (H : ph_hilbert Atom) :
    pformula Atom -> Type :=
| PHPAxiom : forall p, ph_hilbert_schema H p -> ph_hilbert_proof H p
| PHPModusPonens : forall p q,
    ph_hilbert_proof H (PImp p q) ->
    ph_hilbert_proof H p -> ph_hilbert_proof H q
| PHPVerum : ph_hilbert_proof H ptop
| PHPImplyS : forall p q r, ph_hilbert_proof H (ph_axiom_S p q r)
| PHPImplyK : forall p q, ph_hilbert_proof H (ph_axiom_K p q)
| PHPAndElimL : forall p q, ph_hilbert_proof H (ph_axiom_and1 p q)
| PHPAndElimR : forall p q, ph_hilbert_proof H (ph_axiom_and2 p q)
| PHPAndIntro : forall p q, ph_hilbert_proof H (ph_axiom_and3 p q)
| PHPOrIntroL : forall p q, ph_hilbert_proof H (ph_axiom_or1 p q)
| PHPOrIntroR : forall p q, ph_hilbert_proof H (ph_axiom_or2 p q)
| PHPOrElim : forall p q r, ph_hilbert_proof H (ph_axiom_or3 p q r).

Arguments PHPAxiom {Atom H p} _.
Arguments PHPModusPonens {Atom H p q} _ _.
Arguments PHPVerum {Atom H}.
Arguments PHPImplyS {Atom H} p q r.
Arguments PHPImplyK {Atom H} p q.
Arguments PHPAndElimL {Atom H} p q.
Arguments PHPAndElimR {Atom H} p q.
Arguments PHPAndIntro {Atom H} p q.
Arguments PHPOrIntroL {Atom H} p q.
Arguments PHPOrIntroR {Atom H} p q.
Arguments PHPOrElim {Atom H} p q r.

Definition ph_hilbert_entailment (Atom : Type) :
    generic_entailment (ph_hilbert Atom) (pformula Atom) :=
  {| generic_proof := ph_hilbert_proof |}.

Definition ph_hilbert_provable {Atom : Type}
    (H : ph_hilbert Atom) (p : pformula Atom) : Prop :=
  inhabited (ph_hilbert_proof H p).

Lemma ph_hilbert_of_schema :
  forall (Atom : Type) (H : ph_hilbert Atom) (p : pformula Atom),
    ph_hilbert_schema H p -> ph_hilbert_provable H p.
Proof. intros Atom H p Hp. constructor. exact (PHPAxiom Hp). Qed.

Definition ph_hilbert_modus_ponens {Atom : Type} (H : ph_hilbert Atom) :
    generic_modus_ponens
      (ph_hilbert_entailment Atom) (pformula_connectives Atom) H.
Proof. constructor. intros p q. exact (@PHPModusPonens Atom H p q). Defined.

(** Shared implicational combinators.  These small raw-proof lemmas are used
    both by negation equivalence and by the derived classical DNE proof. *)
Definition ph_hilbert_identity {Atom : Type}
    (H : ph_hilbert Atom) (p : pformula Atom) :
    ph_hilbert_proof H (PImp p p) :=
  @generic_imp_identity_raw (ph_hilbert Atom) (pformula Atom)
    (ph_hilbert_entailment Atom) (pformula_connectives Atom) H
    (ph_hilbert_modus_ponens H)
    (fun a b => PHPImplyK a b)
    (fun a b c => PHPImplyS a b c) p.

Definition ph_hilbert_dhyp {Atom : Type}
    (H : ph_hilbert Atom) (p q : pformula Atom)
    (d : ph_hilbert_proof H p) :
    ph_hilbert_proof H (PImp q p) :=
  @generic_dhyp_raw (ph_hilbert Atom) (pformula Atom)
    (ph_hilbert_entailment Atom) (pformula_connectives Atom) H
    (ph_hilbert_modus_ponens H) (fun a b => PHPImplyK a b) p q d.

Definition ph_hilbert_under_apply {Atom : Type}
    (H : ph_hilbert Atom) (a b c : pformula Atom)
    (df : ph_hilbert_proof H (PImp a (PImp b c)))
    (dx : ph_hilbert_proof H (PImp a b)) :
    ph_hilbert_proof H (PImp a c) :=
  @generic_under_apply_raw (ph_hilbert Atom) (pformula Atom)
    (ph_hilbert_entailment Atom) (pformula_connectives Atom) H
    (ph_hilbert_modus_ponens H)
    (fun x y z => PHPImplyS x y z) a b c df dx.

Definition ph_hilbert_imp_trans {Atom : Type}
    (H : ph_hilbert Atom) (a b c : pformula Atom)
    (dab : ph_hilbert_proof H (PImp a b))
    (dbc : ph_hilbert_proof H (PImp b c)) :
    ph_hilbert_proof H (PImp a c) :=
  @generic_imp_trans_raw (ph_hilbert Atom) (pformula Atom)
    (ph_hilbert_entailment Atom) (pformula_connectives Atom) H
    (ph_hilbert_modus_ponens H) (fun x y => PHPImplyK x y)
    (fun x y z => PHPImplyS x y z) a b c dab dbc.

Definition ph_hilbert_and_intro_raw {Atom : Type}
    (H : ph_hilbert Atom) (p q : pformula Atom)
    (dp : ph_hilbert_proof H p) (dq : ph_hilbert_proof H q) :
    ph_hilbert_proof H (PAnd p q) :=
  PHPModusPonens (PHPModusPonens (PHPAndIntro p q) dp) dq.

Definition ph_hilbert_neg_equiv {Atom : Type}
    (H : ph_hilbert Atom) (p : pformula Atom) :
    ph_hilbert_proof H
      (generic_axiom_neg_equiv (pformula_connectives Atom) p).
Proof.
  unfold generic_axiom_neg_equiv, generic_formula_iff.
  change (ph_hilbert_proof H
    (PAnd (PImp (pneg p) (pneg p)) (PImp (pneg p) (pneg p)))).
  exact (@ph_hilbert_and_intro_raw Atom H _ _
    (@ph_hilbert_identity Atom H (pneg p))
    (@ph_hilbert_identity Atom H (pneg p))).
Defined.

Record ph_hilbert_minimal_capabilities {Atom : Type}
    (H : ph_hilbert Atom) : Type := {
  ph_hilbert_minimal_mdp :
    generic_modus_ponens
      (ph_hilbert_entailment Atom) (pformula_connectives Atom) H;
  ph_hilbert_minimal_neg_equiv : forall p,
    ph_hilbert_proof H
      (generic_axiom_neg_equiv (pformula_connectives Atom) p);
  ph_hilbert_minimal_verum : ph_hilbert_proof H ptop;
  ph_hilbert_minimal_K : forall p q, ph_hilbert_proof H (ph_axiom_K p q);
  ph_hilbert_minimal_S : forall p q r, ph_hilbert_proof H (ph_axiom_S p q r);
  ph_hilbert_minimal_and1 : forall p q, ph_hilbert_proof H (ph_axiom_and1 p q);
  ph_hilbert_minimal_and2 : forall p q, ph_hilbert_proof H (ph_axiom_and2 p q);
  ph_hilbert_minimal_and3 : forall p q, ph_hilbert_proof H (ph_axiom_and3 p q);
  ph_hilbert_minimal_or1 : forall p q, ph_hilbert_proof H (ph_axiom_or1 p q);
  ph_hilbert_minimal_or2 : forall p q, ph_hilbert_proof H (ph_axiom_or2 p q);
  ph_hilbert_minimal_or3 : forall p q r, ph_hilbert_proof H (ph_axiom_or3 p q r)
}.

Definition ph_hilbert_minimal {Atom : Type} (H : ph_hilbert Atom) :
    ph_hilbert_minimal_capabilities H.
Proof.
  constructor.
  - apply ph_hilbert_modus_ponens.
  - apply ph_hilbert_neg_equiv.
  - exact PHPVerum.
  - exact PHPImplyK.
  - exact PHPImplyS.
  - exact PHPAndElimL.
  - exact PHPAndElimR.
  - exact PHPAndIntro.
  - exact PHPOrIntroL.
  - exact PHPOrIntroR.
  - exact PHPOrElim.
Defined.

(** The system-specific compatibility record predates the generic minimal
    layer.  This transparent adapter keeps that API stable while making every
    Hilbert system an immediate client of the shared derived-rule library. *)
Definition ph_hilbert_generic_minimal {Atom : Type} (H : ph_hilbert Atom) :
    generic_minimal_entailment
      (ph_hilbert_entailment Atom) (pformula_connectives Atom) H.
Proof.
  destruct (ph_hilbert_minimal H) as
    [Hmp Hneg Htop HK HS Hand1 Hand2 Hand3 Hor1 Hor2 Hor3].
  constructor; assumption.
Defined.

(** Representative generic consequences are available in every concrete
    schema system, independently of which optional intermediate axiom schema
    it carries. *)
Definition ph_hilbert_dni {Atom : Type} (H : ph_hilbert Atom)
    (p : pformula Atom) :
    ph_hilbert_proof H (PImp p (pneg (pneg p))) :=
  generic_minimal_dni_raw (ph_hilbert_generic_minimal H) p.

Definition ph_hilbert_contraposition {Atom : Type} (H : ph_hilbert Atom)
    (p q : pformula Atom)
    (d : ph_hilbert_proof H (PImp p q)) :
    ph_hilbert_proof H (PImp (pneg q) (pneg p)) :=
  generic_minimal_contraposition_raw
    (ph_hilbert_generic_minimal H) p q d.

Definition ph_hilbert_neg_or_iff_and_neg {Atom : Type}
    (H : ph_hilbert Atom) (p q : pformula Atom) :
    ph_hilbert_proof H
      (generic_formula_iff (pformula_connectives Atom)
        (pneg (POr p q)) (PAnd (pneg p) (pneg q))) :=
  generic_minimal_neg_or_iff_and_neg_raw
    (ph_hilbert_generic_minimal H) p q.

Definition ph_hilbert_or_assoc_iff {Atom : Type}
    (H : ph_hilbert Atom) (p q r : pformula Atom) :
    ph_hilbert_proof H
      (generic_formula_iff (pformula_connectives Atom)
        (POr p (POr q r)) (POr (POr p q) r)) :=
  generic_minimal_or_assoc_iff_raw
    (ph_hilbert_generic_minimal H) p q r.

Definition ph_hilbert_and_assoc_iff {Atom : Type}
    (H : ph_hilbert Atom) (p q r : pformula Atom) :
    ph_hilbert_proof H
      (generic_formula_iff (pformula_connectives Atom)
        (PAnd (PAnd p q) r) (PAnd p (PAnd q r))) :=
  generic_minimal_and_assoc_iff_raw
    (ph_hilbert_generic_minimal H) p q r.

(** Concrete views of the generic finite-fold rules.  Positional membership
    records the selected occurrence, so repeated formulas need no equality
    decision procedure. *)
Definition ph_hilbert_list_conj2_elim {Atom : Type}
    (H : ph_hilbert Atom) {p : pformula Atom}
    {gamma : list (pformula Atom)}
    (h : generic_raw_list_member p gamma) :
    ph_hilbert_proof H
      (PImp (generic_list_conj2 (pformula_connectives Atom) gamma) p) :=
  generic_minimal_list_conj2_elim_raw
    (ph_hilbert_generic_minimal H) h.

Definition ph_hilbert_list_disj2_intro {Atom : Type}
    (H : ph_hilbert Atom) {p : pformula Atom}
    {gamma : list (pformula Atom)}
    (h : generic_raw_list_member p gamma) :
    ph_hilbert_proof H
      (PImp p (generic_list_disj2 (pformula_connectives Atom) gamma)) :=
  generic_minimal_list_disj2_intro_raw
    (ph_hilbert_generic_minimal H) h.

(** Finite Hilbert contexts are represented by the same Type-valued raw
    derivations as the generic layer.  The two conversions below show that
    this structural presentation is exactly implication from the normalized
    conjunction of the context. *)
Definition ph_hilbert_context_proof {Atom : Type}
    (H : ph_hilbert Atom) (gamma : list (pformula Atom))
    (p : pformula Atom) : Type :=
  generic_list_derivation (ph_hilbert_entailment Atom) H
    (pformula_connectives Atom) gamma p.

Definition ph_hilbert_context_to_conj2 {Atom : Type}
    (H : ph_hilbert Atom) {gamma : list (pformula Atom)}
    {p : pformula Atom} (d : ph_hilbert_context_proof H gamma p) :
    ph_hilbert_proof H
      (PImp (generic_list_conj2 (pformula_connectives Atom) gamma) p) :=
  generic_minimal_list_derivation_to_conj2_raw
    (ph_hilbert_generic_minimal H) d.

Definition ph_hilbert_context_of_conj2 {Atom : Type}
    (H : ph_hilbert Atom) (gamma : list (pformula Atom))
    (p : pformula Atom)
    (d : ph_hilbert_proof H
      (PImp (generic_list_conj2 (pformula_connectives Atom) gamma) p)) :
    ph_hilbert_context_proof H gamma p :=
  generic_minimal_list_derivation_of_conj2_raw
    (ph_hilbert_generic_minimal H) gamma p d.

Definition ph_hilbert_type_context_proof {Atom : Type}
    (H : ph_hilbert Atom) (T : pformula Atom -> Type)
    (p : pformula Atom) : Type :=
  generic_type_context_derivation (ph_hilbert_entailment Atom) H
    (pformula_connectives Atom) T p.

Definition ph_hilbert_type_context_deduction {Atom : Type}
    (H : ph_hilbert Atom) {T : pformula Atom -> Type}
    {a p : pformula Atom}
    (d : ph_hilbert_type_context_proof H
      (generic_type_context_adjoin a T) p) :
    ph_hilbert_type_context_proof H T (PImp a p) :=
  generic_minimal_type_context_deduction_raw
    (ph_hilbert_generic_minimal H) d.

Definition ph_hilbert_type_context_to_finite {Atom : Type}
    (H : ph_hilbert Atom) {T : pformula Atom -> Type}
    {p : pformula Atom} (d : ph_hilbert_type_context_proof H T p) :
    generic_type_context_finite_witness
      (ph_hilbert_entailment Atom) H (pformula_connectives Atom) T p :=
  generic_type_context_to_finite_witness_raw d.

(** One recursor factors inclusion and arbitrary proof-schema translations. *)
Fixpoint ph_hilbert_proof_map {Atom : Type}
    {H K : ph_hilbert Atom}
    (schema_map : forall p,
      ph_hilbert_schema H p -> ph_hilbert_proof K p)
    {p : pformula Atom} (d : ph_hilbert_proof H p) :
    ph_hilbert_proof K p :=
  match d with
  | PHPAxiom h => schema_map _ h
  | PHPModusPonens dpq dp =>
      PHPModusPonens (ph_hilbert_proof_map schema_map dpq)
                      (ph_hilbert_proof_map schema_map dp)
  | PHPVerum => PHPVerum
  | PHPImplyS p q r => PHPImplyS p q r
  | PHPImplyK p q => PHPImplyK p q
  | PHPAndElimL p q => PHPAndElimL p q
  | PHPAndElimR p q => PHPAndElimR p q
  | PHPAndIntro p q => PHPAndIntro p q
  | PHPOrIntroL p q => PHPOrIntroL p q
  | PHPOrIntroR p q => PHPOrIntroR p q
  | PHPOrElim p q r => PHPOrElim p q r
  end.

Definition ph_hilbert_proof_of_schema_inclusion {Atom : Type}
    {H K : ph_hilbert Atom}
    (incl : forall p,
      ph_hilbert_schema H p -> ph_hilbert_schema K p)
    {p : pformula Atom} (d : ph_hilbert_proof H p) :
    ph_hilbert_proof K p :=
  ph_hilbert_proof_map (fun q hq => PHPAxiom (incl q hq)) d.

Lemma ph_hilbert_provable_of_schema_inclusion :
  forall (Atom : Type) (H K : ph_hilbert Atom),
    (forall p, ph_hilbert_schema H p -> ph_hilbert_schema K p) ->
    forall p, ph_hilbert_provable H p -> ph_hilbert_provable K p.
Proof.
  intros Atom H K Hincl p [d]. constructor.
  exact (ph_hilbert_proof_of_schema_inclusion Hincl d).
Qed.

Fixpoint ph_hilbert_proof_substitute {Atom : Type}
    {H : ph_hilbert Atom} (sigma : psubstitution Atom Atom)
    {p : pformula Atom} (d : ph_hilbert_proof H p) :
    ph_hilbert_proof H (pformula_substitute sigma p) :=
  match d with
  | PHPAxiom h => PHPAxiom (ph_hilbert_schema_substitute H _ h sigma)
  | PHPModusPonens dpq dp =>
      PHPModusPonens (ph_hilbert_proof_substitute sigma dpq)
                      (ph_hilbert_proof_substitute sigma dp)
  | PHPVerum => PHPVerum
  | PHPImplyS p q r => PHPImplyS _ _ _
  | PHPImplyK p q => PHPImplyK _ _
  | PHPAndElimL p q => PHPAndElimL _ _
  | PHPAndElimR p q => PHPAndElimR _ _
  | PHPAndIntro p q => PHPAndIntro _ _
  | PHPOrIntroL p q => PHPOrIntroL _ _
  | PHPOrIntroR p q => PHPOrIntroR _ _
  | PHPOrElim p q r => PHPOrElim _ _ _
  end.

Lemma ph_hilbert_provable_substitute :
  forall (Atom : Type) (H : ph_hilbert Atom)
         (sigma : psubstitution Atom Atom) (p : pformula Atom),
    ph_hilbert_provable H p ->
    ph_hilbert_provable H (pformula_substitute sigma p).
Proof.
  intros Atom H sigma p [d]. constructor.
  exact (ph_hilbert_proof_substitute sigma d).
Qed.

Definition ph_hilbert_proof_of_provable_schema {Atom : Type}
    {H K : ph_hilbert Atom}
    (schema_proof : forall p,
      ph_hilbert_schema H p -> ph_hilbert_proof K p)
    {p : pformula Atom} (d : ph_hilbert_proof H p) :
    ph_hilbert_proof K p :=
  ph_hilbert_proof_map schema_proof d.

(** Foundation's source theorem calls [.get] on an inhabited raw proof.
    Coq exposes that noncomputable boundary once, rather than hiding it in
    the proof recursor. *)
Definition ph_inhabited_get {A : Type} (h : inhabited A) : A :=
  proj1_sig
    (constructive_indefinite_description (fun _ : A => True)
      (match h with
       | inhabits a => ex_intro (fun _ : A => True) a I
       end)).

Lemma ph_hilbert_provable_of_provable_schema :
  forall (Atom : Type) (H K : ph_hilbert Atom),
    (forall p, ph_hilbert_schema H p -> ph_hilbert_provable K p) ->
    forall p, ph_hilbert_provable H p -> ph_hilbert_provable K p.
Proof.
  intros Atom H K Hschema p [d]. constructor.
  apply (ph_hilbert_proof_of_provable_schema
    (fun q hq => ph_inhabited_get (Hschema q hq)) d).
Qed.

(** * Direct capabilities of the named systems *)

Definition ph_hilbert_int_efq {Atom : Type} (p : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_int Atom) (ph_axiom_efq p) :=
  @PHPAxiom Atom (ph_hilbert_int Atom) (ph_axiom_efq p) (PHIntEFQ p).

Definition ph_hilbert_kc_efq {Atom : Type} (p : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_kc Atom) (ph_axiom_efq p) :=
  @PHPAxiom Atom (ph_hilbert_kc Atom) (ph_axiom_efq p) (PHKCEfq p).

Definition ph_hilbert_kc_wlem {Atom : Type} (p : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_kc Atom) (ph_axiom_wlem p) :=
  @PHPAxiom Atom (ph_hilbert_kc Atom) (ph_axiom_wlem p) (PHKCWlem p).

Definition ph_hilbert_lc_efq {Atom : Type} (p : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_lc Atom) (ph_axiom_efq p) :=
  @PHPAxiom Atom (ph_hilbert_lc Atom) (ph_axiom_efq p) (PHLCEfq p).

Definition ph_hilbert_lc_dummett {Atom : Type}
    (p q : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_lc Atom) (ph_axiom_dummett p q) :=
  @PHPAxiom Atom (ph_hilbert_lc Atom) (ph_axiom_dummett p q)
    (PHLCDummett p q).

Definition ph_hilbert_kp_efq {Atom : Type} (p : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_kp Atom) (ph_axiom_efq p) :=
  @PHPAxiom Atom (ph_hilbert_kp Atom) (ph_axiom_efq p) (PHKPEfq p).

Definition ph_hilbert_kp_axiom {Atom : Type}
    (p q r : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_kp Atom)
      (ph_axiom_kreisel_putnam p q r) :=
  @PHPAxiom Atom (ph_hilbert_kp Atom) (ph_axiom_kreisel_putnam p q r)
    (PHKPKreiselPutnam p q r).

Definition ph_hilbert_cl_efq {Atom : Type} (p : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_cl Atom) (ph_axiom_efq p) :=
  @PHPAxiom Atom (ph_hilbert_cl Atom) (ph_axiom_efq p) (PHClEfq p).

Definition ph_hilbert_cl_lem {Atom : Type} (p : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_cl Atom) (ph_axiom_lem p) :=
  @PHPAxiom Atom (ph_hilbert_cl Atom) (ph_axiom_lem p) (PHClLem p).

(** DNE is derived from LEM and EFQ, as in the source's [DNE_of_LEM]
    adapter; it is deliberately not a primitive proof constructor. *)
Definition ph_hilbert_cl_dne {Atom : Type} (p : pformula Atom) :
    ph_hilbert_proof (ph_hilbert_cl Atom)
      (generic_axiom_dne (pformula_connectives Atom) p).
Proof.
  set (H := ph_hilbert_cl Atom).
  apply (@generic_dne_of_lem_efq_raw
    (ph_hilbert Atom) (pformula Atom) (ph_hilbert_entailment Atom)
    (pformula_connectives Atom) H).
  - exact (ph_hilbert_modus_ponens H).
  - exact (fun a b => PHPImplyK a b).
  - exact (fun a b c => PHPImplyS a b c).
  - exact (fun a b c => PHPOrElim a b c).
  - constructor. exact ph_hilbert_cl_lem.
  - constructor. exact ph_hilbert_cl_efq.
  - intro q. exact (@ph_hilbert_identity Atom H (pneg q)).
Defined.

Definition ph_hilbert_cl_classical (Atom : Type) :
    generic_classical_entailment
      (ph_hilbert_entailment Atom) (pformula_connectives Atom)
      (ph_hilbert_cl Atom).
Proof.
  constructor.
  - apply ph_hilbert_modus_ponens.
  - apply ph_hilbert_neg_equiv.
  - exact PHPVerum.
  - exact PHPImplyK.
  - exact PHPImplyS.
  - exact PHPAndElimL.
  - exact PHPAndElimR.
  - exact PHPAndIntro.
  - exact PHPOrIntroL.
  - exact PHPOrIntroR.
  - exact PHPOrElim.
  - exact ph_hilbert_cl_dne.
Defined.

(** The theorem predicate of any Hilbert system is an abstract logic. *)
Definition ph_hilbert_logic {Atom : Type}
    (H : ph_hilbert Atom) : pformula_logic Atom.
Proof.
  refine {| pformula_logic_theorems := ph_hilbert_provable H |}.
  - intros sigma p Hp.
    exact (@ph_hilbert_provable_substitute Atom H sigma p Hp).
  - intros p q [dpq] [dp]. constructor. exact (PHPModusPonens dpq dp).
Defined.

Lemma ph_hilbert_logic_iff_provable :
  forall (Atom : Type) (H : ph_hilbert Atom) (p : pformula Atom),
    pformula_logic_theorems (ph_hilbert_logic H) p <->
    ph_hilbert_provable H p.
Proof. reflexivity. Qed.

Lemma ph_hilbert_logic_subset_of_schema_inclusion :
  forall (Atom : Type) (H K : ph_hilbert Atom),
    (forall p, ph_hilbert_schema H p -> ph_hilbert_schema K p) ->
    pformula_logic_subset (ph_hilbert_logic H) (ph_hilbert_logic K).
Proof.
  intros Atom H K Hincl p Hp.
  exact (@ph_hilbert_provable_of_schema_inclusion
    Atom H K Hincl p Hp).
Qed.

Lemma ph_hilbert_logic_subset_of_provable_schema :
  forall (Atom : Type) (H K : ph_hilbert Atom),
    (forall p, ph_hilbert_schema H p -> ph_hilbert_provable K p) ->
    pformula_logic_subset (ph_hilbert_logic H) (ph_hilbert_logic K).
Proof.
  intros Atom H K Hschema p Hp.
  exact (@ph_hilbert_provable_of_provable_schema
    Atom H K Hschema p Hp).
Qed.

Definition ph_logic_int (Atom : Type) : pformula_logic Atom :=
  ph_hilbert_logic (ph_hilbert_int Atom).

Definition ph_logic_kc (Atom : Type) : pformula_logic Atom :=
  ph_hilbert_logic (ph_hilbert_kc Atom).

Definition ph_logic_lc (Atom : Type) : pformula_logic Atom :=
  ph_hilbert_logic (ph_hilbert_lc Atom).

Definition ph_logic_kreisel_putnam (Atom : Type) : pformula_logic Atom :=
  ph_hilbert_logic (ph_hilbert_kp Atom).

Definition ph_logic_cl (Atom : Type) : pformula_logic Atom :=
  ph_hilbert_logic (ph_hilbert_cl Atom).
