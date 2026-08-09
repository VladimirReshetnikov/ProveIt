(**
  Congruence for ternary applications compiled by different direct
  structural translations.

  A native truth trace and a restricted-soundness trace frequently choose
  different opaque-symbol packages.  Once their predicate and argument
  codes have been identified, however, both packages describe the same
  represented five-step ternary application.  Cross-trace functionality
  therefore identifies their outputs.  Factoring that argument here avoids
  rebuilding it at every rule-local rerooting boundary.
*)

From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedDirectTemplateTernaryApplicationCongruence.

Module
  PABoundedRawCodedDirectTemplateTernaryApplicationCrossTranslationCongruence.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import PABoundedRawCodedDirectTemplateTernaryApplicationCongruence.

(** The two translations may use unrelated templates and unrelated opaque
    dispatchers.  Only the four represented input codes must agree. *)
Theorem raw_directTemplateTernaryApplication_congr_across : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (leftInputs rightInputs : RawCodedTemplateDirectStructuralInputs M)
    leftPredicate rightPredicate
    leftFirst rightFirst leftSecond rightSecond leftThird rightThird,
  rawDirectTemplateFormula leftInputs leftPredicate =
    rawDirectTemplateFormula rightInputs rightPredicate ->
  rawDirectTemplateTerm leftInputs leftFirst =
    rawDirectTemplateTerm rightInputs rightFirst ->
  rawDirectTemplateTerm leftInputs leftSecond =
    rawDirectTemplateTerm rightInputs rightSecond ->
  rawDirectTemplateTerm leftInputs leftThird =
    rawDirectTemplateTerm rightInputs rightThird ->
  rawDirectTemplateFormula leftInputs
      (coqRestrictedPATemplateTernaryApplication
        leftPredicate leftFirst leftSecond leftThird) =
    rawDirectTemplateFormula rightInputs
      (coqRestrictedPATemplateTernaryApplication
        rightPredicate rightFirst rightSecond rightThird).
Proof.
  intros M hPA leftInputs rightInputs leftPredicate rightPredicate
    leftFirst rightFirst leftSecond rightSecond leftThird rightThird
    hpredicate hfirst hsecond hthird.
  pose proof (raw_directTemplateTernaryApplication_trace
    M hPA leftInputs leftPredicate leftFirst leftSecond leftThird)
    as hleft.
  pose proof (raw_directTemplateTernaryApplication_trace
    M hPA rightInputs rightPredicate rightFirst rightSecond rightThird)
    as hright.
  rewrite <- hpredicate, <- hfirst, <- hsecond, <- hthird in hright.
  exact (raw_codedTernaryApplication_functional M hPA
    (rawDirectTemplateFormula leftInputs leftPredicate)
    (rawDirectTemplateTerm leftInputs leftFirst)
    (rawDirectTemplateTerm leftInputs leftSecond)
    (rawDirectTemplateTerm leftInputs leftThird)
    (rawDirectTemplateFormula leftInputs
      (coqRestrictedPATemplateTernaryApplication
        leftPredicate leftFirst leftSecond leftThird))
    (rawDirectTemplateFormula rightInputs
      (coqRestrictedPATemplateTernaryApplication
        rightPredicate rightFirst rightSecond rightThird))
    hleft hright).
Qed.

(** Variable term codes are definitionally independent of the chosen opaque
    symbol package.  This is the compact form used by recursive rule cases,
    whose local formula and assignment coordinates are de Bruijn variables. *)
Corollary
    raw_directTemplateTernaryApplication_congr_across_at_variables : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (leftInputs rightInputs : RawCodedTemplateDirectStructuralInputs M)
    leftPredicate rightPredicate,
  rawDirectTemplateFormula leftInputs leftPredicate =
    rawDirectTemplateFormula rightInputs rightPredicate ->
  forall firstIndex secondIndex thirdIndex,
  rawDirectTemplateFormula leftInputs
      (coqRestrictedPATemplateTernaryApplication leftPredicate
        (ttVar firstIndex) (ttVar secondIndex) (ttVar thirdIndex)) =
    rawDirectTemplateFormula rightInputs
      (coqRestrictedPATemplateTernaryApplication rightPredicate
        (ttVar firstIndex) (ttVar secondIndex) (ttVar thirdIndex)).
Proof.
  intros M hPA leftInputs rightInputs leftPredicate rightPredicate
    hpredicate firstIndex secondIndex thirdIndex.
  apply (raw_directTemplateTernaryApplication_congr_across
    M hPA leftInputs rightInputs leftPredicate rightPredicate
    (ttVar firstIndex) (ttVar firstIndex)
    (ttVar secondIndex) (ttVar secondIndex)
    (ttVar thirdIndex) (ttVar thirdIndex));
    assumption || reflexivity.
Qed.

End
  PABoundedRawCodedDirectTemplateTernaryApplicationCrossTranslationCongruence.
