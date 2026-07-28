(**
  Extend a six-field master common context by one fixed ordinary PA theorem.

  A proof of the helper theorem may use a finite metatheoretic list of PA
  axioms which is not already present in the master's witnessed context.
  [raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail] chooses one
  synchronized standard witness prefix and compiles the helper above the old
  context.  The same prefix is then used, literally, to transplant each of
  the six old roots.  Thus all seven returned proof nodes mention one and the
  same carrier-coded context; no context is decoded and no implicit weakening
  is used.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAProof
  RawCodedTruthCertificateMasterBaseBridge.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterFixedHelperExtension.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.

(** The exact seven-root interface.  In particular, there is only one
    existentially chosen [context], and every local-proof assertion below
    uses that carrier element syntactically.  The helper target is kept in
    its translated-template form so it can contain the caller's chosen
    carrier interpretation while [phi] remains ordinary PA syntax. *)
Definition RawSixFieldMasterCommonContextProofsWithFixedPAHelperOf
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (field1 field2 field3 field4 field5 finalField : M)
    (phi : formula) : Prop :=
  exists witnessList context
      root1 root2 root3 root4 root5 finalRoot helperRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList context /\
    RawCodedPALocalProofOf M context field1 root1 /\
    RawCodedPALocalProofOf M context field2 root2 /\
    RawCodedPALocalProofOf M context field3 root3 /\
    RawCodedPALocalProofOf M context field4 root4 /\
    RawCodedPALocalProofOf M context field5 root5 /\
    RawCodedPALocalProofOf M context finalField finalRoot /\
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation (embedPAFormula phi)) helperRoot.

Arguments RawSixFieldMasterCommonContextProofsWithFixedPAHelperOf
  M translation field1 field2 field3 field4 field5 finalField phi
    : clear implicits.

(** Add one fixed ordinary PA helper to an existing six-field package.

    The helper compiler chooses [prefix] once.  Every call to the transplant
    theorem below receives that exact same Rocq list and the exact old
    [baseContext], so all six rebuilt roots end at the context returned with
    [helperRoot]. *)
Theorem
    raw_sixFieldMasterCommonContextProofsWithFixedPAHelper_of_BProv : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall field1 field2 field3 field4 field5 finalField phi,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  Formula.BProv Formula.Ax_s [] phi ->
  RawSixFieldMasterCommonContextProofsWithFixedPAHelperOf
    M translation field1 field2 field3 field4 field5 finalField phi.
Proof.
  intros M hPA translation hagreement
    field1 field2 field3 field4 field5 finalField phi
    hmaster hhelper.
  unfold RawSixFieldMasterCommonContextProofsOf in hmaster.
  destruct hmaster as
    (baseWitnessList & baseContext & root1 & root2 & root3 & root4 &
      root5 & finalRoot & hbaseWitnessed & hfield1 & hfield2 & hfield3 &
      hfield4 & hfield5 & hfinal).

  (* A witnessed context supplies the sole realizability premise needed to
     rebuild each old proof through a finite standard prefix. *)
  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
      M baseWitnessList baseContext hbaseWitnessed)
    as hbaseRealizable.

  (* The ordinary proof chooses one standard axiom prefix.  Its returned
     helper root already lives over the synchronized prefixed context. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation hagreement
      baseWitnessList baseContext phi hbaseWitnessed hhelper)
    as (prefix & helperRoot & hprefixedWitnessed & hhelperProof).

  (* Rebuild every existing root through exactly [prefix].  These six calls
     do not make six independent context choices: their conclusions contain
     the same explicit [rawStandardPAAxiomWitnessPrefixContextCode]. *)
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext field1 root1
    hbaseRealizable hfield1) as [prefixedRoot1 hprefixed1].
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext field2 root2
    hbaseRealizable hfield2) as [prefixedRoot2 hprefixed2].
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext field3 root3
    hbaseRealizable hfield3) as [prefixedRoot3 hprefixed3].
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext field4 root4
    hbaseRealizable hfield4) as [prefixedRoot4 hprefixed4].
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext field5 root5
    hbaseRealizable hfield5) as [prefixedRoot5 hprefixed5].
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext finalField finalRoot
    hbaseRealizable hfinal) as [prefixedFinalRoot hprefixedFinal].

  unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperOf.
  exists
    (rawStandardPAAxiomWitnessPrefixWitnessListCode
      M prefix baseWitnessList),
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext),
    prefixedRoot1, prefixedRoot2, prefixedRoot3, prefixedRoot4,
    prefixedRoot5, prefixedFinalRoot, helperRoot.
  split; [exact hprefixedWitnessed |].
  split; [exact hprefixed1 |].
  split; [exact hprefixed2 |].
  split; [exact hprefixed3 |].
  split; [exact hprefixed4 |].
  split; [exact hprefixed5 |].
  split; [exact hprefixedFinal |].
  exact hhelperProof.
Qed.

End PABoundedRawCodedTruthCertificateMasterFixedHelperExtension.
