(**
  Declarative nested existential elimination for proof templates.

  Several direct rule compilers open fixed tuples of represented witnesses.
  The carrier compiler already provides a local-proof eliminator, but callers
  which build a complete finite [TemplateRawProof] had to repeat the same
  [trpExE] tree and its context bookkeeping.

  This module constructs that tree for an arbitrary metatheoretic witness
  count.  Its context is exactly [rawCoqTemplateNestedExContext], including
  every shifted intermediate existential assumption, and its deepest target
  is renamed exactly once per opened binder.  No formula code or carrier
  witness is inspected.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.

Module PABoundedRawCodedTemplateNestedExistentialElimination.

Import ListNotations.
Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.

(** One declarative Ex-E step, packaged at complete endpoints. *)
Lemma templateRawDerives_exE : forall
    context body conclusion existentialRoot bodyRoot,
  TemplateRawDerives context (tfEx body) existentialRoot ->
  TemplateRawDerives
    (body :: templateContextShift context)
    (templateFormulaRename S conclusion) bodyRoot ->
  TemplateRawDerives context conclusion
    (trpExE context body conclusion existentialRoot bodyRoot).
Proof.
  intros context body conclusion existentialRoot bodyRoot
    [hexValid [hexContext hexConclusion]]
    [hbodyValid [hbodyContext hbodyConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

(** Rebuild every outer Ex-E node around one proof already inhabiting the
    deepest context.  The recursive target is shifted because each Ex-E body
    is checked beneath one fresh de Bruijn binder. *)
Fixpoint rawCoqTemplateNestedExEliminationRoot
    (count : nat) (body conclusion : TemplateFormula)
    (tail : TemplateContext) (innerRoot : TemplateRawProof)
    : TemplateRawProof :=
  match count with
  | 0 => innerRoot
  | S remaining =>
      let outerFormula := rawCoqTemplateExN (S remaining) body in
      let outerContext := outerFormula :: tail in
      trpExE outerContext
        (rawCoqTemplateExN remaining body) conclusion
        (trpAss outerContext outerFormula)
        (rawCoqTemplateNestedExEliminationRoot remaining body
          (templateFormulaRename S conclusion)
          (templateContextShift outerContext) innerRoot)
  end.

Arguments rawCoqTemplateNestedExEliminationRoot
  count body conclusion tail innerRoot : clear implicits.

(** Complete endpoint theorem.  This is the declarative counterpart of
    [raw_codedPALocalProofOf_templateNestedExElimination]. *)
Theorem rawCoqTemplateNestedExEliminationRoot_derives : forall
    count body conclusion tail innerRoot,
  TemplateRawDerives
    (rawCoqTemplateNestedExContext count body tail)
    (rawCoqTemplateRenameN count conclusion) innerRoot ->
  TemplateRawDerives
    (rawCoqTemplateExN count body :: tail) conclusion
    (rawCoqTemplateNestedExEliminationRoot
      count body conclusion tail innerRoot).
Proof.
  induction count as [|remaining ih];
    intros body conclusion tail innerRoot hinner.
  - cbn [rawCoqTemplateNestedExContext rawCoqTemplateRenameN
      rawCoqTemplateExN rawCoqTemplateNestedExEliminationRoot] in *.
    exact hinner.
  - cbn [rawCoqTemplateNestedExContext rawCoqTemplateRenameN] in hinner.
    cbn [rawCoqTemplateNestedExEliminationRoot rawCoqTemplateExN].
    apply templateRawDerives_exE.
    + apply templateRawDerives_assumption. left. reflexivity.
    + exact (ih body (templateFormulaRename S conclusion)
        (templateContextShift
          (tfEx (rawCoqTemplateExN remaining body) :: tail))
        innerRoot hinner).
Qed.

End PABoundedRawCodedTemplateNestedExistentialElimination.
