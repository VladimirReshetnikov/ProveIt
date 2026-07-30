(**
  Repeated universal elimination for proof templates.

  Arithmetic helper theorems are often retained as explicitly universal
  sources and then instantiated at carrier-valued terms inside a deep rule
  context.  This module packages the finite chain of [trpAllE] nodes for an
  arbitrary metatheoretic list of template terms.

  [RawCoqTemplateAllEListReady] says only that the successive source formulas
  expose enough leading universal binders.  Each binder is opened immediately,
  so later replacements see the exact capture-avoiding result of all earlier
  openings.  No scope shortcut or decoded carrier syntax is used.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import RawCodedTemplateSyntax.

Import ListNotations.

Module PABoundedRawCodedTemplateRepeatedUniversalElimination.

Import PA.
Import PABoundedRawCodedTemplateSyntax.

(** Successive source formulas really have one [tfAll] constructor for each
    requested replacement. *)
Fixpoint RawCoqTemplateAllEListReady
    (replacements : list TemplateTerm) (source : TemplateFormula) : Prop :=
  match replacements with
  | [] => True
  | replacement :: tail =>
      match source with
      | tfAll body =>
          RawCoqTemplateAllEListReady tail
            (templateFormulaOpen replacement body)
      | _ => False
      end
  end.

Arguments RawCoqTemplateAllEListReady replacements source
  : clear implicits.

(** Exact formula after every opening.  The impossible not-ready branch is
    totalized by retaining its current source; correctness never enters it. *)
Fixpoint rawCoqTemplateAllEListResult
    (replacements : list TemplateTerm) (source : TemplateFormula)
    : TemplateFormula :=
  match replacements with
  | [] => source
  | replacement :: tail =>
      match source with
      | tfAll body =>
          rawCoqTemplateAllEListResult tail
            (templateFormulaOpen replacement body)
      | _ => source
      end
  end.

Arguments rawCoqTemplateAllEListResult replacements source
  : clear implicits.

(** The parallel proof tree. *)
Fixpoint rawCoqTemplateAllEListRoot
    (context : TemplateContext) (replacements : list TemplateTerm)
    (source : TemplateFormula) (sourceRoot : TemplateRawProof)
    : TemplateRawProof :=
  match replacements with
  | [] => sourceRoot
  | replacement :: tail =>
      match source with
      | tfAll body =>
          rawCoqTemplateAllEListRoot context tail
            (templateFormulaOpen replacement body)
            (trpAllE context body replacement sourceRoot)
      | _ => sourceRoot
      end
  end.

Arguments rawCoqTemplateAllEListRoot
  context replacements source sourceRoot : clear implicits.

Lemma templateRawDerives_allE : forall
    context body replacement sourceRoot,
  TemplateRawDerives context (tfAll body) sourceRoot ->
  TemplateRawDerives context (templateFormulaOpen replacement body)
    (trpAllE context body replacement sourceRoot).
Proof.
  intros context body replacement sourceRoot
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

(** Arbitrary-length correctness. *)
Theorem rawCoqTemplateAllEListRoot_derives : forall
    context replacements source sourceRoot,
  RawCoqTemplateAllEListReady replacements source ->
  TemplateRawDerives context source sourceRoot ->
  TemplateRawDerives context
    (rawCoqTemplateAllEListResult replacements source)
    (rawCoqTemplateAllEListRoot
      context replacements source sourceRoot).
Proof.
  intros context replacements.
  induction replacements as [|replacement tail ih];
    intros source sourceRoot hready hsource.
  - cbn [rawCoqTemplateAllEListResult
      rawCoqTemplateAllEListRoot]. exact hsource.
  - destruct source as
        [left right | | left right | left right | left right
        | body | body | predicate arguments];
      cbn [RawCoqTemplateAllEListReady] in hready;
      try contradiction.
    cbn [rawCoqTemplateAllEListResult rawCoqTemplateAllEListRoot].
    apply ih; [exact hready |].
    apply templateRawDerives_allE. exact hsource.
Qed.

End PABoundedRawCodedTemplateRepeatedUniversalElimination.
