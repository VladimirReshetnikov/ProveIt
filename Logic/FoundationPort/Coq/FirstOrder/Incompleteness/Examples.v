(** Generalized strict-theory examples from Foundation's incompleteness layer.

    The source file [FirstOrder/Incompleteness/Examples.lean] specializes
    first and second incompleteness to [I Sigma_1], Peano arithmetic, their
    consistency/inconsistency extensions, and true arithmetic.  The current
    Coq development has the concrete first-order theories and the abstract
    provability theorems, but it does not yet have the adapter identifying
    concrete arithmetic syntax, quotation, and standard provability with the
    formula endomorphisms used by [ProvabilityAbstraction].

    This module therefore makes that missing boundary explicit.  A coding
    adapter packages precisely the classical core, inclusion, diagonalizer,
    and provability operator needed by the abstract theorems.  Extension and
    truth adapters expose, rather than assume, the facts supplied by the
    source's concrete theory unions and standard model.  The seven final
    corollaries correspond one-for-one to the seven source instances.

    The results are generalized from arithmetic sentences to arbitrary
    modal-formula atoms and introduce no axioms.  Their strictness proofs
    inherit the single [Classical_Prop.classic] dependency already present in
    [ProvabilityAbstraction]'s incompleteness theorems; the adapter records
    themselves are constructive. *)

From FoundationModal Require Import Syntax LogicInfrastructure.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction First.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Explicit adapters for the missing concrete coding boundary *)

Record pa_examples_coding_adapter {A : Type}
    (L : modal_logic_set A) : Type := {
  pa_examples_core : modal_logic_set A;
  pa_examples_core_classical : classical_logic pa_examples_core;
  pa_examples_theory_classical : classical_logic L;
  pa_examples_core_subset : logic_subset pa_examples_core L;
  pa_examples_diagonalization : pa_diagonalization pa_examples_core;
  pa_examples_provability : pa_provability pa_examples_core L
}.

Arguments pa_examples_core {A L} _.
Arguments pa_examples_core_classical {A L} _.
Arguments pa_examples_theory_classical {A L} _.
Arguments pa_examples_core_subset {A L} _.
Arguments pa_examples_diagonalization {A L} _.
Arguments pa_examples_provability {A L} _.

Definition pa_examples_consistency_statement {A L}
    (X : pa_examples_coding_adapter (A := A) L) : formula A :=
  pa_con (pa_examples_provability X).

Definition pa_examples_inconsistency_statement {A L}
    (X : pa_examples_coding_adapter (A := A) L) : formula A :=
  Neg (pa_examples_consistency_statement X).

(** A concrete theory-union adapter needs only prove that the old theory is
    included and that the newly adjoined sentence is available. *)
Record pa_examples_extension {A : Type}
    (L Lplus : modal_logic_set A) (added : formula A) : Prop := {
  pa_examples_extension_subset : logic_subset L Lplus;
  pa_examples_extension_proves : Lplus added
}.

Arguments pa_examples_extension_subset {A L Lplus added} _.
Arguments pa_examples_extension_proves {A L Lplus added} _.

(** The concrete true-arithmetic adapter separates sound inclusion from the
    two elementary semantic facts used to orient an independent sentence. *)
Record pa_examples_truth_adapter {A : Type}
    (L truth : modal_logic_set A) : Prop := {
  pa_examples_truth_subset : logic_subset L truth;
  pa_examples_truth_cases : forall p, truth p \/ ~ truth p;
  pa_examples_truth_neg_complete : forall p, ~ truth p -> truth (Neg p)
}.

Arguments pa_examples_truth_subset {A L truth} _.
Arguments pa_examples_truth_cases {A L truth} _ _.
Arguments pa_examples_truth_neg_complete {A L truth} _ _ _.

(** * Reusable strictness principles *)

(** The abstract common proof of the source instances
    [T strictly weaker than T union T.Con]. *)
Theorem pa_examples_strict_consistency_extension : forall (A : Type)
    (L Lcon : modal_logic_set A)
    (X : pa_examples_coding_adapter L),
  pa_hbl (pa_examples_provability X) ->
  logic_consistent L ->
  pa_examples_extension L Lcon (pa_examples_consistency_statement X) ->
  logic_strictly_weaker L Lcon.
Proof.
  intros A L Lcon X HH Hconsistent Hextension.
  apply (@pa_strictly_weaker_of_unprovable A L Lcon
    (pa_examples_consistency_statement X)).
  - exact (pa_examples_extension_subset Hextension).
  - exact (@pa_con_unprovable A
      (pa_examples_core X) L
      (pa_examples_core_classical X)
      (pa_examples_theory_classical X)
      (pa_examples_core_subset X)
      (pa_examples_diagonalization X)
      (pa_examples_provability X) HH Hconsistent).
  - exact (pa_examples_extension_proves Hextension).
Qed.

(** The abstract common proof of the source instances
    [T strictly weaker than T union T.Incon].  Source Sigma-one soundness is
    exposed here through its exact consequences: Kreisel reflection and
    consistency. *)
Theorem pa_examples_strict_inconsistency_extension : forall (A : Type)
    (L Lincon : modal_logic_set A)
    (X : pa_examples_coding_adapter L),
  pa_hbl (pa_examples_provability X) ->
  pa_kreisel (pa_examples_provability X) ->
  logic_consistent L ->
  pa_examples_extension L Lincon
    (pa_examples_inconsistency_statement X) ->
  logic_strictly_weaker L Lincon.
Proof.
  intros A L Lincon X HH HK Hconsistent Hextension.
  apply (@pa_strictly_weaker_of_unprovable A L Lincon
    (pa_examples_inconsistency_statement X)).
  - exact (pa_examples_extension_subset Hextension).
  - exact (@pa_con_unrefutable A
      (pa_examples_core X) L
      (pa_examples_core_classical X)
      (pa_examples_theory_classical X)
      (pa_examples_core_subset X)
      (pa_examples_diagonalization X)
      (pa_examples_provability X) HH HK Hconsistent).
  - exact (pa_examples_extension_proves Hextension).
Qed.

(** The generalized common proof of both source instances
    [T union T.Con strictly weaker than true arithmetic]. *)
Theorem pa_examples_strictly_weaker_than_truth : forall (A : Type)
    (L truth : modal_logic_set A)
    (X : pa_examples_coding_adapter L),
  pa_kreisel (pa_examples_provability X) ->
  logic_consistent L ->
  pa_examples_truth_adapter L truth ->
  logic_strictly_weaker L truth.
Proof.
  intros A L truth X HK Hconsistent Htruth.
  apply pa_incomplete_strictly_weaker_than_truth.
  - exact (pa_examples_truth_subset Htruth).
  - exact (pa_examples_truth_cases Htruth).
  - exact (pa_examples_truth_neg_complete Htruth).
  - exact (@pa_first_incompleteness A
      (pa_examples_core X) L
      (pa_examples_core_classical X)
      (pa_examples_theory_classical X)
      (pa_examples_core_subset X)
      (pa_examples_diagonalization X)
      (pa_examples_provability X) HK Hconsistent).
Qed.

(** * The seven source examples *)

(** Source instance 1: [I Sigma_1 < I Sigma_1 union I Sigma_1.Con]. *)
Corollary pa_examples_isigma1_strict_consistency_extension :
  forall (A : Type)
         (isigma1 isigma1_con : modal_logic_set A)
         (X : pa_examples_coding_adapter isigma1),
    pa_hbl (pa_examples_provability X) ->
    logic_consistent isigma1 ->
    pa_examples_extension isigma1 isigma1_con
      (pa_examples_consistency_statement X) ->
    logic_strictly_weaker isigma1 isigma1_con.
Proof.
  intros A isigma1 isigma1_con X HH Hconsistent Hextension.
  exact (pa_examples_strict_consistency_extension
    HH Hconsistent Hextension).
Qed.

(** Source instance 2:
    [I Sigma_1 union I Sigma_1.Con < true arithmetic].
    The adapter [X] is intentionally for the extended theory itself, matching
    the source's inherited Delta-one coding and soundness instances. *)
Corollary pa_examples_isigma1_consistency_extension_strict_truth :
  forall (A : Type)
         (isigma1_con truth : modal_logic_set A)
         (X : pa_examples_coding_adapter isigma1_con),
    pa_kreisel (pa_examples_provability X) ->
    logic_consistent isigma1_con ->
    pa_examples_truth_adapter isigma1_con truth ->
    logic_strictly_weaker isigma1_con truth.
Proof.
  intros A isigma1_con truth X HK Hconsistent Htruth.
  exact (pa_examples_strictly_weaker_than_truth HK Hconsistent Htruth).
Qed.

(** Source instance 3: [I Sigma_1 < I Sigma_1 union I Sigma_1.Incon]. *)
Corollary pa_examples_isigma1_strict_inconsistency_extension :
  forall (A : Type)
         (isigma1 isigma1_incon : modal_logic_set A)
         (X : pa_examples_coding_adapter isigma1),
    pa_hbl (pa_examples_provability X) ->
    pa_kreisel (pa_examples_provability X) ->
    logic_consistent isigma1 ->
    pa_examples_extension isigma1 isigma1_incon
      (pa_examples_inconsistency_statement X) ->
    logic_strictly_weaker isigma1 isigma1_incon.
Proof.
  intros A isigma1 isigma1_incon X HH HK Hconsistent Hextension.
  exact (pa_examples_strict_inconsistency_extension
    HH HK Hconsistent Hextension).
Qed.

(** Source instance 4: [PA < PA union PA.Con]. *)
Corollary pa_examples_peano_strict_consistency_extension :
  forall (A : Type)
         (peano peano_con : modal_logic_set A)
         (X : pa_examples_coding_adapter peano),
    pa_hbl (pa_examples_provability X) ->
    logic_consistent peano ->
    pa_examples_extension peano peano_con
      (pa_examples_consistency_statement X) ->
    logic_strictly_weaker peano peano_con.
Proof.
  intros A peano peano_con X HH Hconsistent Hextension.
  exact (pa_examples_strict_consistency_extension
    HH Hconsistent Hextension).
Qed.

(** Source instance 5: [PA union PA.Con < true arithmetic]. *)
Corollary pa_examples_peano_consistency_extension_strict_truth :
  forall (A : Type)
         (peano_con truth : modal_logic_set A)
         (X : pa_examples_coding_adapter peano_con),
    pa_kreisel (pa_examples_provability X) ->
    logic_consistent peano_con ->
    pa_examples_truth_adapter peano_con truth ->
    logic_strictly_weaker peano_con truth.
Proof.
  intros A peano_con truth X HK Hconsistent Htruth.
  exact (pa_examples_strictly_weaker_than_truth HK Hconsistent Htruth).
Qed.

(** Source instance 6: [PA < PA union PA.Incon]. *)
Corollary pa_examples_peano_strict_inconsistency_extension :
  forall (A : Type)
         (peano peano_incon : modal_logic_set A)
         (X : pa_examples_coding_adapter peano),
    pa_hbl (pa_examples_provability X) ->
    pa_kreisel (pa_examples_provability X) ->
    logic_consistent peano ->
    pa_examples_extension peano peano_incon
      (pa_examples_inconsistency_statement X) ->
    logic_strictly_weaker peano peano_incon.
Proof.
  intros A peano peano_incon X HH HK Hconsistent Hextension.
  exact (pa_examples_strict_inconsistency_extension
    HH HK Hconsistent Hextension).
Qed.

(** Source instance 7:
    [PA union PA.Con < (PA union PA.Con) union (PA union PA.Con).Incon].
    Here [X] is the coding adapter for the already consistency-extended base,
    exactly exposing the source proof's inherited [I Sigma_1]-strength. *)
Corollary
    pa_examples_peano_consistency_extension_strict_own_inconsistency_extension :
  forall (A : Type)
         (peano_con peano_con_incon : modal_logic_set A)
         (X : pa_examples_coding_adapter peano_con),
    pa_hbl (pa_examples_provability X) ->
    pa_kreisel (pa_examples_provability X) ->
    logic_consistent peano_con ->
    pa_examples_extension peano_con peano_con_incon
      (pa_examples_inconsistency_statement X) ->
    logic_strictly_weaker peano_con peano_con_incon.
Proof.
  intros A peano_con peano_con_incon X HH HK Hconsistent Hextension.
  exact (pa_examples_strict_inconsistency_extension
    HH HK Hconsistent Hextension).
Qed.
