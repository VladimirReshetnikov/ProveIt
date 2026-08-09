(**
  Assumption audit for the two synchronized positive Imp-I bodies.

  The three source applications below deliberately expose their endpoint
  coordinates.  The false predecessor is the Pi source at mode 1 and
  [(#6,#9,#8)]; the true predecessor is the Sigma source at mode 0 and
  [(#5,#9,#8)]; and the parent is the Sigma source at mode 0, evaluated at
  the shifted outer-conclusion term and [(#9,#8)].  Consequently the branch
  prefixes checked here are literally

    [piLeft; formulaRelation; ready]

  and

    [sigmaRight; formulaRelation; ready].

  The compiler record also makes the standard-witness synchronization
  explicit: the true-right compiler starts from the extension produced by
  the false-left compiler, after which the older roots are transported to
  that common target.
*)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADirectImpIntroductionPositiveBodyCompilation.

Import
  PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyCompilation.

Check
  coqRestrictedPADirectImpIntroductionFalseLeftPiEvidenceTemplate.
Check
  coqRestrictedPADirectImpIntroductionTrueRightSigmaEvidenceTemplate.
Check
  coqRestrictedPADirectImpIntroductionParentSigmaEvidenceTemplate.
Check
  coqRestrictedPADirectImpIntroductionFalsePositiveBodyPrefix.
Check
  coqRestrictedPADirectImpIntroductionTruePositiveBodyPrefix.
Check
  RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilerAt.
Check
  RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilers.
Check
  raw_selectedImpIntroductionFixedRowSplitTail_of_ready_decision_and_positive_body_compilers.

Print Assumptions
  raw_selectedImpIntroductionFixedRowSplitTail_of_ready_decision_and_positive_body_compilers.
