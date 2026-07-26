(**
  Output-first graph for carrier-indexed numeral-term codes.

  [RawCodedNumeralTermCode] already contains the substantive construction:
  an internal beta trace starts at the code of [tZero], follows the
  transparent [tSucc] code constructor, and PA induction proves that it
  reaches every (possibly nonstandard) element of an arbitrary PA model.
  This module does not duplicate that construction.  It only exposes the
  existing relation in the output-first convention used by dynamic field
  graphs:

      output :: input :: tail.

  Here [input] is the carrier-valued numeral and [output] is the Goedel code
  of its represented numeral term.  The representation theorem is exact in
  every raw model; PA is needed only for totality and the elementary orbit
  facts inherited from the underlying trace construction.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors RawCodedNumeralTermCode
  RawCodedTruthCertificateMasterAssembler.

Module PABoundedRawCodedNumeralTermCodeOutputFirstGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedTruthCertificateMasterAssembler.

(** No new coding relation is introduced: variables zero and one simply
    select the output and input slots of the ambient environment. *)
Definition numeralTermCodeOutputFirstGraph : formula :=
  numeralTermCodeAtTermAt (tVar 1) (tVar 0).

Definition RawNumeralTermCodeOutputFirstAt (M : RawPAModel)
    (input output : M) : Prop :=
  RawNumeralTermCodeAt M input output.

Arguments RawNumeralTermCodeOutputFirstAt
  M input output : clear implicits.

(** Exact arbitrary-model semantics under [output :: input :: tail].  This
    lemma is law-free because all arithmetic is confined to the represented
    trace relation itself. *)
Theorem raw_sat_numeralTermCodeOutputFirstGraph_iff : forall
    (M : RawPAModel) tail input output,
  raw_formula_sat M (scons M output (scons M input tail))
    numeralTermCodeOutputFirstGraph <->
  RawNumeralTermCodeOutputFirstAt M input output.
Proof.
  intros M tail input output.
  unfold numeralTermCodeOutputFirstGraph,
    RawNumeralTermCodeOutputFirstAt.
  rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** The nonstandard totality theorem from [RawCodedNumeralTermCode] now has
    exactly the interface expected by the six-field graph assembler. *)
Theorem numeralTermCodeOutputFirstGraph_raw_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawOutputFirstFieldGraphTotal M numeralTermCodeOutputFirstGraph.
Proof.
  intros M hPA tail input.
  destruct (raw_numeralTermCodeExists_all M hPA input)
    as [output houtput].
  exists output.
  apply (proj2
    (raw_sat_numeralTermCodeOutputFirstGraph_iff
      M tail input output)).
  exact houtput.
Qed.

(** At zero the represented trace output is forced to be the transparent
    code of [tZero].  This tiny observation lets clients select a canonical
    base witness without reopening the beta-table construction. *)
Lemma raw_numeralTermCodeAt_zero_output : forall
    (M : RawPAModel), RawPASatisfies M -> forall output,
  RawNumeralTermCodeAt M (raw_zero M) output ->
  output = rawTermZeroCode M.
Proof.
  intros M hPA output
    (code & step & [_ [hzero _]] & houtput).
  exact (raw_codedAssignmentLookup_functional M hPA
    code step (raw_zero M) output (rawTermZeroCode M)
    houtput hzero).
Qed.

Theorem numeralTermCodeOutputFirstGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    numeralTermCodeOutputFirstGraph <->
  output = rawTermZeroCode M.
Proof.
  intros M hPA tail output.
  rewrite raw_sat_numeralTermCodeOutputFirstGraph_iff.
  split.
  - exact (raw_numeralTermCodeAt_zero_output M hPA output).
  - intro houtput. subst output.
    destruct (raw_numeralTermCodeExists_zero M hPA)
      as [candidate hcandidate].
    pose proof (raw_numeralTermCodeAt_zero_output
      M hPA candidate hcandidate) as hcandidateEq.
    rewrite hcandidateEq in hcandidate.
    exact hcandidate.
Qed.

Corollary numeralTermCodeOutputFirstGraph_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  raw_formula_sat M
    (scons M (rawTermZeroCode M) (scons M (raw_zero M) tail))
    numeralTermCodeOutputFirstGraph.
Proof.
  intros M hPA tail.
  apply (proj2
    (numeralTermCodeOutputFirstGraph_zero_iff
      M hPA tail (rawTermZeroCode M))).
  reflexivity.
Qed.

(** Successor closure is deliberately existential: the underlying module's
    public successor theorem promises a represented next code while keeping
    the freshly extended beta table abstract.  This is the strongest useful
    graph-level fact available without duplicating that proof tree. *)
Theorem numeralTermCodeOutputFirstGraph_succ_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail input current,
  raw_formula_sat M (scons M current (scons M input tail))
    numeralTermCodeOutputFirstGraph ->
  exists next,
    raw_formula_sat M
      (scons M next (scons M (raw_succ M input) tail))
      numeralTermCodeOutputFirstGraph.
Proof.
  intros M hPA tail input current hcurrent.
  pose proof (proj1
    (raw_sat_numeralTermCodeOutputFirstGraph_iff
      M tail input current) hcurrent) as hcurrentCode.
  destruct (raw_numeralTermCodeExists_succ M hPA input
    (ex_intro _ current hcurrentCode)) as [next hnext].
  exists next.
  apply (proj2
    (raw_sat_numeralTermCodeOutputFirstGraph_iff
      M tail (raw_succ M input) next)).
  exact hnext.
Qed.

End PABoundedRawCodedNumeralTermCodeOutputFirstGraph.
