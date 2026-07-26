(**
  Transparent projection schemas for model-coded proof templates.

  The dynamic-truth universal branch is a useful stress test for the
  template compiler.  Its antecedent has several existential witnesses and
  a long right-associated conjunction.  The desired conclusion keeps the
  *same* witnesses, drops some conjuncts, and repacks the retained facts in a
  shorter right-associated conjunction.  This file constructs that proof
  tree directly from the natural-deduction constructors of
  [RawCodedTemplateSyntax].

  There is no appeal to completeness here.  The central combinator accepts
  arbitrary numbers of existential binders and arbitrary lists of selected
  conjunction positions.  Position [length prefix] denotes the final tail
  of a right-associated conjunction; larger positions deliberately keep
  denoting that tail.  The latter total convention makes the proof-producing
  functions transparent and avoids carrying decidable bounds through every
  later specialization.  Callers normally use only in-range positions.

  A final wrapper introduces any number of universal binders around a closed
  template derivation.  Together these operations give the exact logical
  shape used by the universal-leaf projection: two universal variables,
  five preserved existential witnesses, and the selection [0,1,2,6,7] from
  an eight-component conjunction.
*)

From Stdlib Require Import List Arith.
From BoundedPAConsistency Require Import RawCodedTemplateSyntax.
From BoundedPAConsistency Require Import RawCodedTemplateLogicalSchemas.

Import ListNotations.

Module PABoundedRawCodedTemplateProjectionSchemas.

Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateLogicalSchemas.

(** ------------------------------------------------------------------
    Right-associated conjunctions and their total positional selector. *)

Fixpoint templateRightConjunction
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    : TemplateFormula :=
  match prefix with
  | [] => tail
  | head :: rest => tfAnd head (templateRightConjunction rest tail)
  end.

(** Index zero selects the first prefix formula.  Once the prefix is
    exhausted, every remaining index selects the final tail. *)
Fixpoint templateRightConjunctionSelect
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    (index : nat) : TemplateFormula :=
  match prefix, index with
  | [], _ => tail
  | head :: _, 0 => head
  | _ :: rest, S next =>
      templateRightConjunctionSelect rest tail next
  end.

Definition templateSelectedRightConjunction
    (sourcePrefix : list TemplateFormula) (sourceTail : TemplateFormula)
    (selectedPrefix : list nat) (selectedTail : nat) : TemplateFormula :=
  templateRightConjunction
    (map (templateRightConjunctionSelect sourcePrefix sourceTail)
      selectedPrefix)
    (templateRightConjunctionSelect sourcePrefix sourceTail selectedTail).

(** ------------------------------------------------------------------
    Projection of one component from an already-derived conjunction. *)

Fixpoint templateRightConjunctionProjectFrom
    (context : TemplateContext)
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    (index : nat) (sourceProof : TemplateRawProof) : TemplateRawProof :=
  match prefix, index with
  | [], _ => sourceProof
  | head :: rest, 0 =>
      trpAndE1 context head (templateRightConjunction rest tail)
        sourceProof
  | head :: rest, S next =>
      templateRightConjunctionProjectFrom context rest tail next
        (trpAndE2 context head (templateRightConjunction rest tail)
          sourceProof)
  end.

Lemma templateAndLeftFrom_derives : forall
    context leftFormula rightFormula sourceProof,
  TemplateRawDerives context (tfAnd leftFormula rightFormula) sourceProof ->
  TemplateRawDerives context leftFormula
    (trpAndE1 context leftFormula rightFormula sourceProof).
Proof.
  intros context leftFormula rightFormula sourceProof hsource.
  destruct hsource as [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives. cbn.
  repeat split; assumption.
Qed.

Lemma templateAndRightFrom_derives : forall
    context leftFormula rightFormula sourceProof,
  TemplateRawDerives context (tfAnd leftFormula rightFormula) sourceProof ->
  TemplateRawDerives context rightFormula
    (trpAndE2 context leftFormula rightFormula sourceProof).
Proof.
  intros context leftFormula rightFormula sourceProof hsource.
  destruct hsource as [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives. cbn.
  repeat split; assumption.
Qed.

Theorem templateRightConjunctionProjectFrom_derives : forall
    context prefix tail index sourceProof,
  TemplateRawDerives context
    (templateRightConjunction prefix tail) sourceProof ->
  TemplateRawDerives context
    (templateRightConjunctionSelect prefix tail index)
    (templateRightConjunctionProjectFrom
      context prefix tail index sourceProof).
Proof.
  intros context prefix.
  induction prefix as [|head rest ih];
    intros tail [|index] sourceProof hsource; cbn.
  - exact hsource.
  - exact hsource.
  - now apply templateAndLeftFrom_derives.
  - apply ih.
    now apply templateAndRightFrom_derives.
Qed.

(** ------------------------------------------------------------------
    Repacking any finite list of selected components.

    Every projection below starts from the same [sourceProof].  This
    duplicates a finite proof subtree, which is exactly what the represented
    raw proof format permits and keeps this construction independent of any
    proof-sharing mechanism. *)

Fixpoint templateRightConjunctionPackFrom
    (context : TemplateContext)
    (sourcePrefix : list TemplateFormula) (sourceTail : TemplateFormula)
    (selectedPrefix : list nat) (selectedTail : nat)
    (sourceProof : TemplateRawProof) : TemplateRawProof :=
  match selectedPrefix with
  | [] =>
      templateRightConjunctionProjectFrom context sourcePrefix sourceTail
        selectedTail sourceProof
  | selected :: rest =>
      trpAndI context
        (templateRightConjunctionSelect sourcePrefix sourceTail selected)
        (templateSelectedRightConjunction sourcePrefix sourceTail
          rest selectedTail)
        (templateRightConjunctionProjectFrom context sourcePrefix sourceTail
          selected sourceProof)
        (templateRightConjunctionPackFrom context sourcePrefix sourceTail
          rest selectedTail sourceProof)
  end.

Theorem templateRightConjunctionPackFrom_derives : forall
    context sourcePrefix sourceTail selectedPrefix selectedTail sourceProof,
  TemplateRawDerives context
    (templateRightConjunction sourcePrefix sourceTail) sourceProof ->
  TemplateRawDerives context
    (templateSelectedRightConjunction sourcePrefix sourceTail
      selectedPrefix selectedTail)
    (templateRightConjunctionPackFrom context sourcePrefix sourceTail
      selectedPrefix selectedTail sourceProof).
Proof.
  intros context sourcePrefix sourceTail selectedPrefix.
  induction selectedPrefix as [|selected rest ih];
    intros selectedTail sourceProof hsource.
  - unfold templateSelectedRightConjunction. cbn.
    now apply templateRightConjunctionProjectFrom_derives.
  - unfold templateSelectedRightConjunction at 1. cbn.
    unfold TemplateRawDerives.
    pose proof (templateRightConjunctionProjectFrom_derives
      context sourcePrefix sourceTail selected sourceProof hsource)
      as hleft.
    pose proof (ih selectedTail sourceProof hsource) as hright.
    destruct hleft as [hleftValid [hleftContext hleftConclusion]].
    destruct hright as [hrightValid [hrightContext hrightConclusion]].
    cbn.
    repeat split; assumption.
Qed.

(** The corresponding closed implication. *)
Definition templateRightConjunctionSelectionProof
    (sourcePrefix : list TemplateFormula) (sourceTail : TemplateFormula)
    (selectedPrefix : list nat) (selectedTail : nat) : TemplateRawProof :=
  let source := templateRightConjunction sourcePrefix sourceTail in
  let target := templateSelectedRightConjunction
    sourcePrefix sourceTail selectedPrefix selectedTail in
  let context := [source] in
  trpImpI [] source target
    (templateRightConjunctionPackFrom context
      sourcePrefix sourceTail selectedPrefix selectedTail
      (trpAss context source)).

Theorem templateRightConjunctionSelectionProof_derives : forall
    sourcePrefix sourceTail selectedPrefix selectedTail,
  TemplateRawDerives []
    (tfImp
      (templateRightConjunction sourcePrefix sourceTail)
      (templateSelectedRightConjunction sourcePrefix sourceTail
        selectedPrefix selectedTail))
    (templateRightConjunctionSelectionProof
      sourcePrefix sourceTail selectedPrefix selectedTail).
Proof.
  intros sourcePrefix sourceTail selectedPrefix selectedTail.
  unfold templateRightConjunctionSelectionProof.
  unfold TemplateRawDerives at 1. cbn.
  pose proof (templateRightConjunctionPackFrom_derives
    [templateRightConjunction sourcePrefix sourceTail]
    sourcePrefix sourceTail selectedPrefix selectedTail
    (trpAss [templateRightConjunction sourcePrefix sourceTail]
      (templateRightConjunction sourcePrefix sourceTail))) as hpack.
  assert (hassumption : TemplateRawDerives
      [templateRightConjunction sourcePrefix sourceTail]
      (templateRightConjunction sourcePrefix sourceTail)
      (trpAss [templateRightConjunction sourcePrefix sourceTail]
        (templateRightConjunction sourcePrefix sourceTail))).
  { apply templateRawDerives_assumption. left. reflexivity. }
  specialize (hpack hassumption).
  destruct hpack as [hvalid [hcontext hconclusion]].
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Preserving an arbitrary number of existential witnesses. *)

Fixpoint templateRepeatedExists
    (binderCount : nat) (body : TemplateFormula) : TemplateFormula :=
  match binderCount with
  | 0 => body
  | S smaller => tfEx (templateRepeatedExists smaller body)
  end.

(** Starting from a derivation of the source existential tower in [context],
    eliminate one source witness at a time.  In each eigenvariable context,
    recursively project the remaining tower and then reintroduce that very
    eigenvariable as the corresponding target witness. *)
Fixpoint templateRepeatedExistsSelectionFrom
    (binderCount : nat) (context : TemplateContext)
    (sourcePrefix : list TemplateFormula) (sourceTail : TemplateFormula)
    (selectedPrefix : list nat) (selectedTail : nat)
    (sourceProof : TemplateRawProof) : TemplateRawProof :=
  match binderCount with
  | 0 =>
      templateRightConjunctionPackFrom context
        sourcePrefix sourceTail selectedPrefix selectedTail sourceProof
  | S smaller =>
      let sourceBody := templateRepeatedExists smaller
        (templateRightConjunction sourcePrefix sourceTail) in
      let targetBody := templateRepeatedExists smaller
        (templateSelectedRightConjunction
          sourcePrefix sourceTail selectedPrefix selectedTail) in
      let eigenContext := sourceBody :: templateContextShift context in
      let projectedBody :=
        templateRepeatedExistsSelectionFrom smaller eigenContext
          sourcePrefix sourceTail selectedPrefix selectedTail
          (trpAss eigenContext sourceBody) in
      let preservedWitness :=
        trpExI eigenContext
          (templateFormulaRename (templateUpRenaming S) targetBody)
          (ttVar 0) projectedBody in
      trpExE context sourceBody (tfEx targetBody)
        sourceProof preservedWitness
  end.

Theorem templateRepeatedExistsSelectionFrom_derives : forall
    binderCount context sourcePrefix sourceTail
    selectedPrefix selectedTail sourceProof,
  TemplateRawDerives context
    (templateRepeatedExists binderCount
      (templateRightConjunction sourcePrefix sourceTail)) sourceProof ->
  TemplateRawDerives context
    (templateRepeatedExists binderCount
      (templateSelectedRightConjunction
        sourcePrefix sourceTail selectedPrefix selectedTail))
    (templateRepeatedExistsSelectionFrom binderCount context
      sourcePrefix sourceTail selectedPrefix selectedTail sourceProof).
Proof.
  induction binderCount as [|smaller ih];
    intros context sourcePrefix sourceTail
      selectedPrefix selectedTail sourceProof hsource.
  - cbn. now apply templateRightConjunctionPackFrom_derives.
  - cbn [templateRepeatedExistsSelectionFrom templateRepeatedExists].
    set (sourceBody := templateRepeatedExists smaller
      (templateRightConjunction sourcePrefix sourceTail)).
    set (targetBody := templateRepeatedExists smaller
      (templateSelectedRightConjunction
        sourcePrefix sourceTail selectedPrefix selectedTail)).
    set (eigenContext := sourceBody :: templateContextShift context).
    assert (hassumption : TemplateRawDerives eigenContext sourceBody
        (trpAss eigenContext sourceBody)).
    { apply templateRawDerives_assumption. left. reflexivity. }
    pose proof (ih eigenContext sourcePrefix sourceTail
      selectedPrefix selectedTail
      (trpAss eigenContext sourceBody) hassumption) as hprojected.
    destruct hsource as [hsourceValid [hsourceContext hsourceConclusion]].
    destruct hprojected as
      [hprojectedValid [hprojectedContext hprojectedConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    rewrite templateFormulaOpen_binderShift_zero.
    repeat split; try assumption; try reflexivity.
Qed.

Definition templateRepeatedExistsSelectionProof
    (binderCount : nat)
    (sourcePrefix : list TemplateFormula) (sourceTail : TemplateFormula)
    (selectedPrefix : list nat) (selectedTail : nat) : TemplateRawProof :=
  let sourceBody := templateRightConjunction sourcePrefix sourceTail in
  let targetBody := templateSelectedRightConjunction
    sourcePrefix sourceTail selectedPrefix selectedTail in
  let source := templateRepeatedExists binderCount sourceBody in
  let target := templateRepeatedExists binderCount targetBody in
  let context := [source] in
  trpImpI [] source target
    (templateRepeatedExistsSelectionFrom binderCount context
      sourcePrefix sourceTail selectedPrefix selectedTail
      (trpAss context source)).

Theorem templateRepeatedExistsSelectionProof_derives : forall
    binderCount sourcePrefix sourceTail selectedPrefix selectedTail,
  TemplateRawDerives []
    (tfImp
      (templateRepeatedExists binderCount
        (templateRightConjunction sourcePrefix sourceTail))
      (templateRepeatedExists binderCount
        (templateSelectedRightConjunction
          sourcePrefix sourceTail selectedPrefix selectedTail)))
    (templateRepeatedExistsSelectionProof binderCount
      sourcePrefix sourceTail selectedPrefix selectedTail).
Proof.
  intros binderCount sourcePrefix sourceTail selectedPrefix selectedTail.
  unfold templateRepeatedExistsSelectionProof.
  set (source := templateRepeatedExists binderCount
    (templateRightConjunction sourcePrefix sourceTail)).
  assert (hassumption : TemplateRawDerives [source] source
      (trpAss [source] source)).
  { apply templateRawDerives_assumption. left. reflexivity. }
  pose proof (templateRepeatedExistsSelectionFrom_derives
    binderCount [source] sourcePrefix sourceTail
    selectedPrefix selectedTail (trpAss [source] source)
    hassumption) as hprojection.
  destruct hprojection as [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives. cbn.
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Universal closure of a closed derivation. *)

Fixpoint templateRepeatedForall
    (binderCount : nat) (body : TemplateFormula) : TemplateFormula :=
  match binderCount with
  | 0 => body
  | S smaller => tfAll (templateRepeatedForall smaller body)
  end.

Fixpoint templateUniversalCloseProof
    (binderCount : nat) (body : TemplateFormula)
    (bodyProof : TemplateRawProof) : TemplateRawProof :=
  match binderCount with
  | 0 => bodyProof
  | S smaller =>
      trpAllI [] (templateRepeatedForall smaller body)
        (templateUniversalCloseProof smaller body bodyProof)
  end.

Theorem templateUniversalCloseProof_derives : forall
    binderCount body bodyProof,
  TemplateRawDerives [] body bodyProof ->
  TemplateRawDerives [] (templateRepeatedForall binderCount body)
    (templateUniversalCloseProof binderCount body bodyProof).
Proof.
  induction binderCount as [|smaller ih];
    intros body bodyProof hbody; cbn.
  - exact hbody.
  - pose proof (ih body bodyProof hbody) as hclosed.
    destruct hclosed as [hvalid [hcontext hconclusion]].
    unfold TemplateRawDerives. cbn.
    repeat split; assumption.
Qed.

(** A universally closed version of the existential/conjunction projection.
    This is often the most convenient public compiler input. *)
Definition templateClosedRepeatedExistsSelectionProof
    (universalCount existentialCount : nat)
    (sourcePrefix : list TemplateFormula) (sourceTail : TemplateFormula)
    (selectedPrefix : list nat) (selectedTail : nat) : TemplateRawProof :=
  let implicationProof := templateRepeatedExistsSelectionProof
    existentialCount sourcePrefix sourceTail selectedPrefix selectedTail in
  let implicationFormula := tfImp
    (templateRepeatedExists existentialCount
      (templateRightConjunction sourcePrefix sourceTail))
    (templateRepeatedExists existentialCount
      (templateSelectedRightConjunction
        sourcePrefix sourceTail selectedPrefix selectedTail)) in
  templateUniversalCloseProof universalCount implicationFormula
    implicationProof.

Theorem templateClosedRepeatedExistsSelectionProof_derives : forall
    universalCount existentialCount sourcePrefix sourceTail
    selectedPrefix selectedTail,
  TemplateRawDerives []
    (templateRepeatedForall universalCount
      (tfImp
        (templateRepeatedExists existentialCount
          (templateRightConjunction sourcePrefix sourceTail))
        (templateRepeatedExists existentialCount
          (templateSelectedRightConjunction
            sourcePrefix sourceTail selectedPrefix selectedTail))))
    (templateClosedRepeatedExistsSelectionProof
      universalCount existentialCount sourcePrefix sourceTail
      selectedPrefix selectedTail).
Proof.
  intros universalCount existentialCount sourcePrefix sourceTail
    selectedPrefix selectedTail.
  unfold templateClosedRepeatedExistsSelectionProof.
  apply templateUniversalCloseProof_derives.
  apply templateRepeatedExistsSelectionProof_derives.
Qed.

(** ------------------------------------------------------------------
    The concrete logical shape of the dynamic-truth universal leaf.

    The source conjunction has components

      bound, free, formula, subformula, universal, rank, negation, leaf.

    The projection retains positions [0], [1], [2], [6], and [7], while all
    five existential witnesses are reintroduced in their original order. *)

Definition templateUniversalLeafProjectionProof
    (boundFormula freeFormula codeFormula subformulaFormula
      universalFormula rankFormula negationFormula leafFormula
      : TemplateFormula) : TemplateRawProof :=
  templateClosedRepeatedExistsSelectionProof 2 5
    [boundFormula; freeFormula; codeFormula; subformulaFormula;
      universalFormula; rankFormula; negationFormula]
    leafFormula [0; 1; 2; 6] 7.

Theorem templateUniversalLeafProjectionProof_derives : forall
    boundFormula freeFormula codeFormula subformulaFormula
    universalFormula rankFormula negationFormula leafFormula,
  TemplateRawDerives []
    (templateRepeatedForall 2
      (tfImp
        (templateRepeatedExists 5
          (templateRightConjunction
            [boundFormula; freeFormula; codeFormula; subformulaFormula;
              universalFormula; rankFormula; negationFormula]
            leafFormula))
        (templateRepeatedExists 5
          (templateRightConjunction
            [boundFormula; freeFormula; codeFormula; negationFormula]
            leafFormula))))
    (templateUniversalLeafProjectionProof
      boundFormula freeFormula codeFormula subformulaFormula
      universalFormula rankFormula negationFormula leafFormula).
Proof.
  intros.
  unfold templateUniversalLeafProjectionProof.
  change (TemplateRawDerives []
    (templateRepeatedForall 2
      (tfImp
        (templateRepeatedExists 5
          (templateRightConjunction
            [boundFormula; freeFormula; codeFormula; subformulaFormula;
              universalFormula; rankFormula; negationFormula]
            leafFormula))
        (templateRepeatedExists 5
          (templateSelectedRightConjunction
            [boundFormula; freeFormula; codeFormula; subformulaFormula;
              universalFormula; rankFormula; negationFormula]
            leafFormula [0; 1; 2; 6] 7))))
    (templateClosedRepeatedExistsSelectionProof 2 5
      [boundFormula; freeFormula; codeFormula; subformulaFormula;
        universalFormula; rankFormula; negationFormula]
      leafFormula [0; 1; 2; 6] 7)).
  apply templateClosedRepeatedExistsSelectionProof_derives.
Qed.

End PABoundedRawCodedTemplateProjectionSchemas.
