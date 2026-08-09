(**
  Iterated represented K-combinators in an unchanged local context.

  Several direct rule-case semantic residuals end in truth of the parent's
  displayed conclusion.  Once native aligned truth has produced that final
  atom, the residual's constructor-code and premise-truth antecedents are not
  needed to derive it.  They must nevertheless be introduced by genuine PA
  proof nodes; meta-level weakening is not sound for an arbitrary represented
  context code.

  The one-antecedent K proof is provided by the same-context unary compiler.
  This module iterates it over a metatheoretic list, preserving the displayed
  implication order and returning the represented root chosen at every step.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.

Import ListNotations.

Module PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.

(** Right-associated implication chain.  For example,
    [[A; B]] compiles to [A -> B -> consequence]. *)
Fixpoint coqTemplateImpChain
    (antecedents : list TemplateFormula) (consequence : TemplateFormula)
    : TemplateFormula :=
  match antecedents with
  | [] => consequence
  | antecedent :: rest =>
      tfImp antecedent (coqTemplateImpChain rest consequence)
  end.

Arguments coqTemplateImpChain antecedents consequence : clear implicits.

(** Add every unused antecedent with a represented Imp-I/K proof.  Induction
    proceeds from the tail so the source list's left-to-right order is exactly
    the object-language implication order. *)
Theorem raw_codedPALocalProofOf_iterated_unused_antecedents : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    localContext antecedents consequence consequenceRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation consequence) consequenceRoot ->
  exists resultRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation localContext)
      (rawTemplateFormula translation
        (coqTemplateImpChain antecedents consequence)) resultRoot.
Proof.
  intros M hPA translation localContext antecedents.
  induction antecedents as [|antecedent rest ih];
    intros consequence consequenceRoot hconsequence.
  - exists consequenceRoot. exact hconsequence.
  - destruct (ih consequence consequenceRoot hconsequence)
      as [restRoot hrest].
    cbn [coqTemplateImpChain].
    exact
      (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
        M hPA translation localContext
        (coqTemplateImpChain rest consequence) antecedent
        restRoot hrest).
Qed.

End PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.
