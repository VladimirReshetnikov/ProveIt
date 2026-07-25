(* ===================================================================== *)
(*  PAHFOrdinalCodeTotalInduction.v                                       *)
(*                                                                       *)
(*  Final PA induction and projection layer for totality of the           *)
(*  Ackermann finite-ordinal code graph.                                  *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFProofCalculus PAHFOrdinalCode PAHFOrdinalCodeTotal
  PAHFOrdinalCodeTotalCapacity.

Import ListNotations.
Import PA PA.Term PA.Formula.

Lemma BProv_Ax_s_betaCodeExtensionExistsTermAt_of_accumulator :
  forall G oldCode step target newOut,
  BProv Ax_s G
    (betaPrefixCRTAccumulatorExistsTermAt step target target) ->
  BProv Ax_s G
    (ltTermAt newOut (betaModTermTerm step target)) ->
  BProv Ax_s G
    (betaCodeExtensionExistsTermAt oldCode step target newOut).
Proof.
  intros G oldCode step target newOut hacc hnewBound.
  set (goal :=
    betaCodeExtensionExistsTermAt oldCode step target newOut).
  apply (BProv_Ax_s_betaPrefixCRTAccumulatorExistsTermAt_elim_opened
    G step target target goal); [|exact hacc].
  set (accBody :=
    betaPrefixCRTAccumulatorExistsTermAtBody step target target).
  set (D := accBody :: map (rename S) G).
  set (oldCode1 := Term.rename S oldCode).
  set (step1 := Term.rename S step).
  set (target1 := Term.rename S target).
  set (newOut1 := Term.rename S newOut).
  assert (haccD : BProv Ax_s D
    (betaPrefixCRTAccumulatorTermAt
      step1 target1 target1 (tVar 0))).
  {
    apply BProv_ass.
    unfold D, accBody, betaPrefixCRTAccumulatorExistsTermAtBody,
      step1, target1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_andE1 Ax_s D _ _ haccD) as hprefix.
  pose proof (BProv_andE2 Ax_s D _ _ haccD) as hinverse.
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hnewBound S) as hboundRen.
  rewrite rename_ltTermAt in hboundRen.
  rewrite term_rename_betaModTermTerm in hboundRen.
  pose proof (BProv_context_cons Ax_s (map (rename S) G)
    accBody _ hboundRen) as hboundD.
  change (BProv Ax_s D
    (ltTermAt newOut1 (betaModTermTerm step1 target1))) in hboundD.
  pose proof
    (BProv_Ax_s_betaCodeExtensionExistsTermAt_of_prefix_inverse
      D oldCode1 (tVar 0) step1 target1 newOut1
      hprefix hinverse hboundD) as hex.
  unfold goal.
  rewrite rename_betaCodeExtensionExistsTermAt.
  exact hex.
Qed.

Lemma BProv_Ax_s_betaCodeExtensionExistsTermAt_of_common :
  forall G oldCode step target newOut,
  BProv Ax_s G (commonMultipleThroughTermAt target step) ->
  BProv Ax_s G
    (ltTermAt newOut (betaModTermTerm step target)) ->
  BProv Ax_s G
    (betaCodeExtensionExistsTermAt oldCode step target newOut).
Proof.
  intros G oldCode step target newOut hcommon hnewBound.
  apply (BProv_Ax_s_betaCodeExtensionExistsTermAt_of_accumulator
    G oldCode step target newOut); [|exact hnewBound].
  exact (BProv_Ax_s_betaPrefixCRTAccumulatorExistsTermAt_self
    G step target hcommon).
Qed.

Lemma BProv_Ax_s_betaCodeExtensionExistsTermAt_of_sum_capacity :
  forall G oldSequenceCode raw oldCapacity newCoded step,
  BProv Ax_s G
    (betaCodingStepTermAt (tSucc raw)
      (tAdd oldCapacity newCoded) step) ->
  BProv Ax_s G
    (betaCodeExtensionExistsTermAt oldSequenceCode step
      (tSucc raw) newCoded).
Proof.
  intros G oldSequenceCode raw oldCapacity newCoded step hcoding.
  unfold betaCodingStepTermAt in hcoding.
  pose proof (BProv_andE1 Ax_s G _ _ hcoding) as hcommon.
  pose proof (BProv_andE2 Ax_s G _ _ hcoding) as hlargeSum.
  pose proof (BProv_Ax_s_add_comm_terms G oldCapacity newCoded)
    as hcomm.
  pose proof (BProv_Ax_s_leTermAt_of_eq_add_right_terms
    G newCoded (tAdd oldCapacity newCoded) oldCapacity hcomm)
    as hnewLeSum.
  pose proof (BProv_Ax_s_leTermAt_succ_succ
    G newCoded (tAdd oldCapacity newCoded) hnewLeSum)
    as hsuccNewLeSum.
  pose proof (BProv_Ax_s_leTermAt_trans G
    (tSucc newCoded) (tSucc (tAdd oldCapacity newCoded)) step
    hsuccNewLeSum hlargeSum) as hlargeNew.
  pose proof (BProv_Ax_s_leTermAt_step_betaModTermTerm
    G step (tSucc raw)) as hstepMod.
  pose proof (BProv_Ax_s_leTermAt_trans G
    (tSucc newCoded) step (betaModTermTerm step (tSucc raw))
    hlargeNew hstepMod) as hsuccNewMod.
  pose proof (BProv_Ax_s_ltTermAt_of_succ_leTermAt
    G newCoded (betaModTermTerm step (tSucc raw)) hsuccNewMod)
    as hnewLtMod.
  exact (BProv_Ax_s_betaCodeExtensionExistsTermAt_of_common
    G oldSequenceCode step (tSucc raw) newCoded hcommon hnewLtMod).
Qed.

Lemma BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_succ_of_sum_capacity :
  forall G step raw oldCoded newCoded oldCapacity,
  BProv Ax_s G
    (ordinalCodeGraphBodyExistsTermAt step raw oldCoded) ->
  BProv Ax_s G
    (betaCodingStepTermAt (tSucc raw)
      (tAdd oldCapacity newCoded) step) ->
  BProv Ax_s G
    (hfAdjoinGraphTermAt newCoded oldCoded oldCoded) ->
  BProv Ax_s G
    (ordinalCodeGraphBodyExistsTermAt step (tSucc raw) newCoded).
Proof.
  intros G step raw oldCoded newCoded oldCapacity
    holdTrace hcoding hadjoin.
  set (goal :=
    ordinalCodeGraphBodyExistsTermAt step (tSucc raw) newCoded).
  apply (BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_elim_opened
    G step raw oldCoded goal); [|exact holdTrace].
  set (oldBody := ordinalCodeGraphBodyTermAt
    (tVar 0) (Term.rename S step)
    (Term.rename S raw) (Term.rename S oldCoded)).
  set (D := oldBody :: map (rename S) G).
  set (step1 := Term.rename S step).
  set (raw1 := Term.rename S raw).
  set (oldCoded1 := Term.rename S oldCoded).
  set (newCoded1 := Term.rename S newCoded).
  set (oldCapacity1 := Term.rename S oldCapacity).
  assert (holdBody : BProv Ax_s D
    (ordinalCodeGraphBodyTermAt (tVar 0) step1 raw1 oldCoded1)).
  {
    apply BProv_ass.
    unfold D, oldBody, step1, raw1, oldCoded1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hcoding S) as hcodingRen.
  rewrite rename_betaCodingStepTermAt in hcodingRen.
  pose proof (BProv_context_cons Ax_s (map (rename S) G)
    oldBody _ hcodingRen) as hcodingD.
  change (BProv Ax_s D
    (betaCodingStepTermAt (tSucc raw1)
      (tAdd oldCapacity1 newCoded1) step1)) in hcodingD.
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hadjoin S) as hadjoinRen.
  rewrite rename_hfAdjoinGraphTermAt in hadjoinRen.
  pose proof (BProv_context_cons Ax_s (map (rename S) G)
    oldBody _ hadjoinRen) as hadjoinD.
  change (BProv Ax_s D
    (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1)) in hadjoinD.
  pose proof
    (BProv_Ax_s_betaCodeExtensionExistsTermAt_of_sum_capacity
      D (tVar 0) raw1 oldCapacity1 newCoded1 step1 hcodingD)
    as hextExists.
  apply (BProv_Ax_s_betaCodeExtensionExistsTermAt_elim_opened
    D (tVar 0) step1 (tSucc raw1) newCoded1
    (rename S goal)); [|exact hextExists].
  set (extensionBody := betaCodeExtensionExistsTermAtBody
    (tVar 0) step1 (tSucc raw1) newCoded1).
  set (E := extensionBody :: map (rename S) D).
  set (step2 := Term.rename S step1).
  set (raw2 := Term.rename S raw1).
  set (oldCoded2 := Term.rename S oldCoded1).
  set (newCoded2 := Term.rename S newCoded1).
  assert (hextension : BProv Ax_s E
    (betaCodeExtensionTermAt
      (tVar 1) step2 (tSucc raw2) newCoded2 (tVar 0))).
  {
    apply BProv_ass.
    unfold E, extensionBody, betaCodeExtensionExistsTermAtBody,
      step2, raw2, newCoded2.
    simpl. left. reflexivity.
  }
  assert (holdBodyE : BProv Ax_s E
    (ordinalCodeGraphBodyTermAt
      (tVar 1) step2 raw2 oldCoded2)).
  {
    assert (hraw : BProv Ax_s E (rename S oldBody)).
    {
      apply BProv_ass.
      unfold E, D. simpl. right. left. reflexivity.
    }
    unfold oldBody in hraw.
    rewrite rename_ordinalCodeGraphBodyTermAt in hraw.
    change (BProv Ax_s E
      (ordinalCodeGraphBodyTermAt
        (tVar 1) step2 raw2 oldCoded2)) in hraw.
    exact hraw.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s D _
    hadjoinD S) as hadjoinDRen.
  rewrite rename_hfAdjoinGraphTermAt in hadjoinDRen.
  pose proof (BProv_context_cons Ax_s (map (rename S) D)
    extensionBody _ hadjoinDRen) as hadjoinE.
  change (BProv Ax_s E
    (hfAdjoinGraphTermAt newCoded2 oldCoded2 oldCoded2)) in hadjoinE.
  pose proof
    (BProv_Ax_s_ordinalCodeGraphBodyTermAt_succ_of_extension
      E (tVar 1) (tVar 0) step2 raw2 oldCoded2 newCoded2
      holdBodyE hextension hadjoinE) as hnewBody.
  pose proof (BProv_ordinalCodeGraphBodyExistsTermAt_of_term
    Ax_s E (tVar 0) step2 (tSucc raw2) newCoded2 hnewBody)
    as hnewExists.
  unfold goal.
  rewrite !rename_ordinalCodeGraphBodyExistsTermAt.
  change (BProv Ax_s E
    (ordinalCodeGraphBodyExistsTermAt step2 (tSucc raw2) newCoded2)).
  exact hnewExists.
Qed.

Lemma BProv_Ax_s_ordinalCodeTraceCapacityTermAt_succ :
  forall G raw oldCoded newCoded oldCapacity,
  BProv Ax_s G
    (ordinalCodeTraceCapacityTermAt raw oldCoded oldCapacity) ->
  BProv Ax_s G
    (hfAdjoinGraphTermAt newCoded oldCoded oldCoded) ->
  BProv Ax_s G
    (ordinalCodeTraceCapacityTermAt
      (tSucc raw) newCoded (tAdd oldCapacity newCoded)).
Proof.
  intros G raw oldCoded newCoded oldCapacity
    holdCapacity hadjoin.
  set (antecedent := betaCodingStepTermAt
    (tSucc (Term.rename S raw))
    (tAdd (Term.rename S oldCapacity) (Term.rename S newCoded))
    (tVar 0)).
  set (consequent := ordinalCodeGraphBodyExistsTermAt
    (tVar 0) (tSucc (Term.rename S raw)) (Term.rename S newCoded)).
  set (C := antecedent :: map (rename S) G).
  assert (hbody : BProv Ax_s C consequent).
  {
    set (raw1 := Term.rename S raw).
    set (oldCoded1 := Term.rename S oldCoded).
    set (newCoded1 := Term.rename S newCoded).
    set (oldCapacity1 := Term.rename S oldCapacity).
    assert (hcoding : BProv Ax_s C
      (betaCodingStepTermAt (tSucc raw1)
        (tAdd oldCapacity1 newCoded1) (tVar 0))).
    {
      apply BProv_ass.
      unfold C, antecedent, raw1, oldCapacity1, newCoded1.
      simpl. left. reflexivity.
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      holdCapacity S) as holdCapacityRen.
    rewrite rename_ordinalCodeTraceCapacityTermAt in holdCapacityRen.
    pose proof (BProv_context_cons Ax_s (map (rename S) G)
      antecedent _ holdCapacityRen) as holdCapacityC.
    change (BProv Ax_s C
      (ordinalCodeTraceCapacityTermAt raw1 oldCoded1 oldCapacity1))
      in holdCapacityC.
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hadjoin S) as hadjoinRen.
    rewrite rename_hfAdjoinGraphTermAt in hadjoinRen.
    pose proof (BProv_context_cons Ax_s (map (rename S) G)
      antecedent _ hadjoinRen) as hadjoinC.
    change (BProv Ax_s C
      (hfAdjoinGraphTermAt newCoded1 oldCoded1 oldCoded1))
      in hadjoinC.
    pose proof
      (BProv_Ax_s_betaCodingStepTermAt_old_of_sum_capacity
        C raw1 oldCapacity1 newCoded1 (tVar 0) hcoding)
      as holdCoding.
    pose proof
      (BProv_Ax_s_ordinalCodeTraceCapacityTermAt_trace_of_coding
        C raw1 oldCoded1 oldCapacity1 (tVar 0)
        holdCapacityC holdCoding) as holdTrace.
    pose proof
      (BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_succ_of_sum_capacity
        C (tVar 0) raw1 oldCoded1 newCoded1 oldCapacity1
        holdTrace hcoding hadjoinC) as hnewTrace.
    change (BProv Ax_s C consequent) in hnewTrace.
    exact hnewTrace.
  }
  assert (himp : BProv Ax_s (map (rename S) G)
    (pImp antecedent consequent)).
  {
    unfold C in hbody.
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent consequent hbody).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _ sentence_ax_s himp)
    as hall.
  unfold ordinalCodeTraceCapacityTermAt.
  change (BProv Ax_s G (pAll (pImp antecedent consequent))).
  exact hall.
Qed.

Definition ordinalCodeTotalCapacityTermAt (raw : term) : formula :=
  pEx (pEx
    (ordinalCodeTraceCapacityTermAt
      (Term.rename (fun n => n + 2) raw)
      (tVar 1) (tVar 0))).

Lemma subst_ordinalCodeTotalCapacityTermAt : forall sigma raw,
  subst sigma (ordinalCodeTotalCapacityTermAt raw) =
    ordinalCodeTotalCapacityTermAt (Term.subst sigma raw).
Proof.
  intros sigma raw.
  unfold ordinalCodeTotalCapacityTermAt.
  cbn [subst].
  rewrite subst_ordinalCodeTraceCapacityTermAt.
  simpl.
  rewrite term_subst_up_up_rename_add_two.
  reflexivity.
Qed.

Lemma rename_ordinalCodeTotalCapacityTermAt : forall r raw,
  rename r (ordinalCodeTotalCapacityTermAt raw) =
    ordinalCodeTotalCapacityTermAt (Term.rename r raw).
Proof.
  intros r raw.
  rewrite <- subst_var_rename.
  rewrite subst_ordinalCodeTotalCapacityTermAt.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma BProv_ordinalCodeTotalCapacityTermAt_of_terms :
  forall B G raw coded capacity,
  BProv B G
    (ordinalCodeTraceCapacityTermAt raw coded capacity) ->
  BProv B G (ordinalCodeTotalCapacityTermAt raw).
Proof.
  intros B G raw coded capacity hcapacity.
  unfold ordinalCodeTotalCapacityTermAt.
  apply (BProv_exI B G _ coded).
  apply (BProv_exI B G _ capacity).
  cbn [subst].
  rewrite !subst_ordinalCodeTraceCapacityTermAt.
  simpl.
  repeat rewrite term_subst_upSubst_instTerm_rename_add_two.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hcapacity.
Qed.

Lemma BProv_Ax_s_ordinalCodeTotalCapacityTermAt_zero : forall G,
  BProv Ax_s G (ordinalCodeTotalCapacityTermAt tZero).
Proof.
  intro G.
  exact (BProv_ordinalCodeTotalCapacityTermAt_of_terms
    Ax_s G tZero tZero tZero
    (BProv_Ax_s_ordinalCodeTraceCapacityTermAt_zero G)).
Qed.

Definition hfAdjoinExistsTermAt (oldCode elemCode : term) : formula :=
  pEx
    (hfAdjoinGraphTermAt
      (tVar 0)
      (Term.rename S oldCode)
      (Term.rename S elemCode)).

Lemma subst_hfAdjoinExistsTermAt : forall sigma oldCode elemCode,
  subst sigma (hfAdjoinExistsTermAt oldCode elemCode) =
    hfAdjoinExistsTermAt
      (Term.subst sigma oldCode) (Term.subst sigma elemCode).
Proof.
  intros sigma oldCode elemCode.
  unfold hfAdjoinExistsTermAt.
  cbn [subst].
  rewrite subst_hfAdjoinGraphTermAt.
  simpl.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_hfAdjoinExistsTermAt : forall r oldCode elemCode,
  rename r (hfAdjoinExistsTermAt oldCode elemCode) =
    hfAdjoinExistsTermAt
      (Term.rename r oldCode) (Term.rename r elemCode).
Proof.
  intros r oldCode elemCode.
  rename_from_subst subst_hfAdjoinExistsTermAt.
Qed.

Lemma BProv_hfAdjoinExistsTermAt_of_term :
  forall B G newCode oldCode elemCode,
  BProv B G (hfAdjoinGraphTermAt newCode oldCode elemCode) ->
  BProv B G (hfAdjoinExistsTermAt oldCode elemCode).
Proof.
  intros B G newCode oldCode elemCode hgraph.
  unfold hfAdjoinExistsTermAt.
  apply (BProv_exI B G _ newCode).
  rewrite subst_hfAdjoinGraphTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hgraph.
Qed.

Lemma BProv_Ax_s_hfAdjoinExistsTermAt_elim_opened :
  forall G oldCode elemCode target,
  BProv Ax_s
    (hfAdjoinGraphTermAt
        (tVar 0)
        (Term.rename S oldCode)
        (Term.rename S elemCode) ::
      map (rename S) G)
    (rename S target) ->
  BProv Ax_s G (hfAdjoinExistsTermAt oldCode elemCode) ->
  BProv Ax_s G target.
Proof.
  intros G oldCode elemCode target hopened hex.
  unfold hfAdjoinExistsTermAt in hex.
  exact (BProv_exE_of_sentences Ax_s G _ target
    sentence_ax_s hex hopened).
Qed.

(* The sole interface required from the omitted PA-internal finite-set
   adjunction construction.  This is ordinary proof data, not an axiom. *)
Definition PAHFAdjoinExistence : Prop :=
  forall (G : list formula) (oldCode elemCode : term),
    BProv Ax_s G (hfAdjoinExistsTermAt oldCode elemCode).

Lemma BProv_Ax_s_ordinalCodeTotalCapacityTermAt_succ_of_terms :
  PAHFAdjoinExistence ->
  forall G raw oldCoded oldCapacity,
  BProv Ax_s G
    (ordinalCodeTraceCapacityTermAt raw oldCoded oldCapacity) ->
  BProv Ax_s G
    (ordinalCodeTotalCapacityTermAt (tSucc raw)).
Proof.
  intros hadjoinTotal G raw oldCoded oldCapacity holdCapacity.
  set (goal := ordinalCodeTotalCapacityTermAt (tSucc raw)).
  pose proof (hadjoinTotal G oldCoded oldCoded) as hex.
  apply (BProv_Ax_s_hfAdjoinExistsTermAt_elim_opened
    G oldCoded oldCoded goal); [|exact hex].
  set (graphBody := hfAdjoinGraphTermAt
    (tVar 0) (Term.rename S oldCoded) (Term.rename S oldCoded)).
  set (D := graphBody :: map (rename S) G).
  set (raw1 := Term.rename S raw).
  set (oldCoded1 := Term.rename S oldCoded).
  set (oldCapacity1 := Term.rename S oldCapacity).
  assert (hgraph : BProv Ax_s D
    (hfAdjoinGraphTermAt (tVar 0) oldCoded1 oldCoded1)).
  {
    apply BProv_ass.
    unfold D, graphBody, oldCoded1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    holdCapacity S) as holdCapacityRen.
  rewrite rename_ordinalCodeTraceCapacityTermAt in holdCapacityRen.
  pose proof (BProv_context_cons Ax_s (map (rename S) G)
    graphBody _ holdCapacityRen) as holdCapacityD.
  change (BProv Ax_s D
    (ordinalCodeTraceCapacityTermAt raw1 oldCoded1 oldCapacity1))
    in holdCapacityD.
  pose proof (BProv_Ax_s_ordinalCodeTraceCapacityTermAt_succ
    D raw1 oldCoded1 (tVar 0) oldCapacity1
    holdCapacityD hgraph) as hnewCapacity.
  pose proof (BProv_ordinalCodeTotalCapacityTermAt_of_terms
    Ax_s D (tSucc raw1) (tVar 0)
    (tAdd oldCapacity1 (tVar 0)) hnewCapacity) as hnewTotal.
  unfold goal.
  rewrite rename_ordinalCodeTotalCapacityTermAt.
  change (BProv Ax_s D
    (ordinalCodeTotalCapacityTermAt (tSucc raw1))).
  exact hnewTotal.
Qed.

Lemma BProv_Ax_s_ordinalCodeTotalCapacityTermAt_succ :
  PAHFAdjoinExistence ->
  forall G raw,
  BProv Ax_s G (ordinalCodeTotalCapacityTermAt raw) ->
  BProv Ax_s G (ordinalCodeTotalCapacityTermAt (tSucc raw)).
Proof.
  intros hadjoinTotal G raw holdTotal.
  set (goal := ordinalCodeTotalCapacityTermAt (tSucc raw)).
  set (pairBody := ordinalCodeTraceCapacityTermAt
    (Term.rename (fun n => n + 2) raw) (tVar 1) (tVar 0)).
  assert (holdEx : BProv Ax_s G (pEx (pEx pairBody))).
  {
    unfold ordinalCodeTotalCapacityTermAt in holdTotal.
    fold pairBody in holdTotal.
    exact holdTotal.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G pairBody goal holdEx).
  set (C := pairBody ::
    map (rename S) (pEx pairBody :: map (rename S) G)).
  change (BProv Ax_s C (rename S (rename S goal))).
      set (raw2 := Term.rename (fun n => n + 2) raw).
      assert (hcapacity : BProv Ax_s C
        (ordinalCodeTraceCapacityTermAt raw2 (tVar 1) (tVar 0))).
      {
        apply BProv_ass.
        unfold C, pairBody, raw2. simpl. left. reflexivity.
      }
      pose proof
        (BProv_Ax_s_ordinalCodeTotalCapacityTermAt_succ_of_terms
          hadjoinTotal C raw2 (tVar 1) (tVar 0) hcapacity) as hsucc.
      unfold goal.
      rewrite !rename_ordinalCodeTotalCapacityTermAt.
      simpl.
      rewrite term_rename_succ_twice_add_two.
      change (BProv Ax_s C
        (ordinalCodeTotalCapacityTermAt (tSucc raw2))).
      exact hsucc.
Qed.

Lemma BProv_Ax_s_all_ordinalCodeTotalCapacityTermAt :
  PAHFAdjoinExistence ->
  forall G,
  BProv Ax_s G
    (pAll (ordinalCodeTotalCapacityTermAt (tVar 0))).
Proof.
  intros hadjoinTotal G.
  set (phi := ordinalCodeTotalCapacityTermAt (tVar 0)).
  assert (hzeroRaw : BProv Ax_s G
    (ordinalCodeTotalCapacityTermAt tZero)).
  { apply BProv_Ax_s_ordinalCodeTotalCapacityTermAt_zero. }
  assert (hzero : BProv Ax_s G (subst substZero phi)).
  {
    unfold phi.
    rewrite subst_ordinalCodeTotalCapacityTermAt.
    simpl.
    exact hzeroRaw.
  }
  set (C := phi :: map (rename S) G).
  assert (hsuccBody : BProv Ax_s C (subst substSuccVar phi)).
  {
    assert (hcurrent : BProv Ax_s C
      (ordinalCodeTotalCapacityTermAt (tVar 0))).
    {
      apply BProv_ass.
      unfold C, phi. simpl. left. reflexivity.
    }
    pose proof (BProv_Ax_s_ordinalCodeTotalCapacityTermAt_succ
      hadjoinTotal C (tVar 0) hcurrent) as hnext.
    unfold phi.
    rewrite subst_ordinalCodeTotalCapacityTermAt.
    simpl.
    exact hnext.
  }
  assert (hsuccImp : BProv Ax_s (map (rename S) G)
    (pImp phi (subst substSuccVar phi))).
  {
    unfold C in hsuccBody.
    exact (BProv_impI Ax_s (map (rename S) G)
      phi (subst substSuccVar phi) hsuccBody).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _ sentence_ax_s hsuccImp)
    as hsuccAll.
  exact (BProv_Ax_s_induction_rule G phi hzero hsuccAll).
Qed.

Lemma BProv_Ax_s_commonMultipleThroughTermAt_mul_right :
  forall G bound multiple appended,
  BProv Ax_s G (commonMultipleThroughTermAt bound multiple) ->
  BProv Ax_s G
    (commonMultipleThroughTermAt bound (tMul multiple appended)).
Proof.
  intros G bound multiple appended hcommon.
  set (antecedent := ltTermAt (tVar 0) (Term.rename S bound)).
  set (consequent := dvdTermTermAt
    (tSucc (tVar 0)) (Term.rename S (tMul multiple appended))).
  set (C := antecedent :: map (rename S) G).
  assert (hbody : BProv Ax_s C consequent).
  {
    set (bound1 := Term.rename S bound).
    set (multiple1 := Term.rename S multiple).
    set (appended1 := Term.rename S appended).
    assert (hlt : BProv Ax_s C (ltTermAt (tVar 0) bound1)).
    {
      apply BProv_ass.
      unfold C, antecedent, bound1. simpl. left. reflexivity.
    }
    pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
      hcommon S) as hcommonRen.
    rewrite rename_commonMultipleThroughTermAt in hcommonRen.
    pose proof (BProv_context_cons Ax_s (map (rename S) G)
      antecedent _ hcommonRen) as hcommonC.
    change (BProv Ax_s C
      (commonMultipleThroughTermAt bound1 multiple1)) in hcommonC.
    pose proof
      (BProv_Ax_s_dvdTermTermAt_of_commonMultipleThroughTermAt
        C bound1 multiple1 (tVar 0) hcommonC hlt) as hdvd.
    pose proof (BProv_Ax_s_dvdTermTermAt_mul_right
      C (tSucc (tVar 0)) multiple1 appended1 hdvd) as hmul.
    change (BProv Ax_s C consequent) in hmul.
    exact hmul.
  }
  assert (himp : BProv Ax_s (map (rename S) G)
    (pImp antecedent consequent)).
  {
    unfold C in hbody.
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent consequent hbody).
  }
  pose proof (BProv_allI_of_sentences Ax_s G _ sentence_ax_s himp)
    as hall.
  unfold commonMultipleThroughTermAt.
  change (BProv Ax_s G (pAll (pImp antecedent consequent))).
  exact hall.
Qed.

Lemma BProv_Ax_s_leTermAt_succ_mul_succ_of_pos :
  forall G multiple value,
  BProv Ax_s G (ltTermAt tZero multiple) ->
  BProv Ax_s G
    (leTermAt (tSucc value) (tMul multiple (tSucc value))).
Proof.
  intros G multiple value hpos.
  set (target :=
    leTermAt (tSucc value) (tMul multiple (tSucc value))).
  apply (BProv_Ax_s_ltTermAt_elim_opened
    G tZero multiple target); [|exact hpos].
  set (body := pEq
    (tAdd (Term.rename S tZero) (tSucc (tVar 0)))
    (Term.rename S multiple)).
  set (D := body :: map (rename S) G).
  set (multiple1 := Term.rename S multiple).
  set (value1 := Term.rename S value).
  set (lower := tSucc value1).
  set (diff := tMul (tVar 0) lower).
  assert (hopened : BProv Ax_s D
    (pEq (tAdd tZero (tSucc (tVar 0))) multiple1)).
  {
    apply BProv_ass.
    unfold D, body, multiple1. simpl. left. reflexivity.
  }
  pose proof (BProv_Ax_s_zero_add_term D (tSucc (tVar 0)))
    as hzeroAdd.
  assert (hmultiple : BProv Ax_s D
    (pEq multiple1 (tSucc (tVar 0)))).
  {
    exact (BProv_eqTrans Ax_s D _ _ _
      (BProv_eqSym Ax_s D _ _ hopened) hzeroAdd).
  }
  pose proof (BProv_eq_congr_mul_left Ax_s D _ _ lower hmultiple)
    as hproductCong.
  assert (hsuccMul : BProv Ax_s D
    (pEq (tMul (tSucc (tVar 0)) lower)
      (tAdd diff lower))).
  {
    unfold diff.
    apply BProv_Ax_s_succ_mul_terms.
  }
  pose proof (BProv_Ax_s_add_comm_terms D diff lower) as hcomm.
  assert (hproduct : BProv Ax_s D
    (pEq (tMul multiple1 lower) (tAdd lower diff))).
  {
    exact (BProv_eqTrans Ax_s D _ _ _ hproductCong
      (BProv_eqTrans Ax_s D _ _ _ hsuccMul hcomm)).
  }
  pose proof (BProv_Ax_s_leTermAt_of_eq_add_right_terms
    D lower (tMul multiple1 lower) diff hproduct) as hle.
  unfold target.
  rewrite rename_leTermAt.
  change (BProv Ax_s D
    (leTermAt lower (tMul multiple1 lower))).
  exact hle.
Qed.

Lemma BProv_Ax_s_betaCodingStepTermAt_of_positiveCommon :
  forall G bound sourceCode multiple,
  BProv Ax_s G
    (positiveCommonMultipleThroughTermAt bound multiple) ->
  BProv Ax_s G
    (betaCodingStepTermAt bound sourceCode
      (tMul multiple (tSucc sourceCode))).
Proof.
  intros G bound sourceCode multiple hpositive.
  unfold positiveCommonMultipleThroughTermAt in hpositive.
  pose proof (BProv_andE1 Ax_s G _ _ hpositive) as hpos.
  pose proof (BProv_andE2 Ax_s G _ _ hpositive) as hcommon.
  pose proof (BProv_Ax_s_commonMultipleThroughTermAt_mul_right
    G bound multiple (tSucc sourceCode) hcommon) as hcommonScaled.
  pose proof (BProv_Ax_s_leTermAt_succ_mul_succ_of_pos
    G multiple sourceCode hpos) as hlarge.
  unfold betaCodingStepTermAt.
  exact (BProv_andI Ax_s G _ _ hcommonScaled hlarge).
Qed.

Lemma subst_positiveCommonMultipleExistsTermAt : forall sigma bound,
  subst sigma (positiveCommonMultipleExistsTermAt bound) =
    positiveCommonMultipleExistsTermAt (Term.subst sigma bound).
Proof.
  intros sigma bound.
  exact (PA.Formula.subst_positiveCommonMultipleExistsTermAt sigma bound).
Qed.

Lemma subst_betaCodingStepExistsTermAt : forall sigma bound sourceCode,
  subst sigma (betaCodingStepExistsTermAt bound sourceCode) =
    betaCodingStepExistsTermAt
      (Term.subst sigma bound) (Term.subst sigma sourceCode).
Proof.
  intros sigma bound sourceCode.
  exact (PA.Formula.subst_betaCodingStepExistsTermAt
    sigma bound sourceCode).
Qed.

Lemma rename_betaCodingStepExistsTermAt : forall r bound sourceCode,
  rename r (betaCodingStepExistsTermAt bound sourceCode) =
    betaCodingStepExistsTermAt
      (Term.rename r bound) (Term.rename r sourceCode).
Proof.
  intros r bound sourceCode.
  exact (PA.Formula.rename_betaCodingStepExistsTermAt
    r bound sourceCode).
Qed.

Lemma BProv_Ax_s_betaCodingStepExistsTermAt_of_term :
  forall G bound sourceCode step,
  BProv Ax_s G (betaCodingStepTermAt bound sourceCode step) ->
  BProv Ax_s G (betaCodingStepExistsTermAt bound sourceCode).
Proof.
  intros G bound sourceCode step hstep.
  unfold betaCodingStepExistsTermAt.
  apply (BProv_exI Ax_s G _ step).
  rewrite subst_betaCodingStepTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hstep.
Qed.

Lemma BProv_Ax_s_betaCodingStepExistsTermAt_elim_opened :
  forall G bound sourceCode target,
  BProv Ax_s
    (betaCodingStepExistsTermAtBody bound sourceCode ::
      map (rename S) G)
    (rename S target) ->
  BProv Ax_s G (betaCodingStepExistsTermAt bound sourceCode) ->
  BProv Ax_s G target.
Proof.
  intros G bound sourceCode target hopened hex.
  unfold betaCodingStepExistsTermAt in hex.
  unfold betaCodingStepExistsTermAtBody in hopened.
  exact (BProv_exE_of_sentences Ax_s G _ target
    sentence_ax_s hex hopened).
Qed.

Lemma BProv_Ax_s_betaCodingStepExistsTermAt :
  forall G bound sourceCode,
  BProv Ax_s G (betaCodingStepExistsTermAt bound sourceCode).
Proof.
  intros G bound sourceCode.
  pose proof (BProv_Ax_s_all_positiveCommonMultipleExistsTermAt G)
    as hall.
  pose proof (BProv_allE Ax_s G _ bound hall) as hpositiveRaw.
  rewrite subst_positiveCommonMultipleExistsTermAt in hpositiveRaw.
  simpl in hpositiveRaw.
  assert (hpositiveEx : BProv Ax_s G
    (positiveCommonMultipleExistsTermAt bound)).
  { exact hpositiveRaw. }
  set (goal := betaCodingStepExistsTermAt bound sourceCode).
  apply (BProv_Ax_s_positiveCommonMultipleExistsTermAt_elim_opened
    G bound goal); [|exact hpositiveEx].
  set (positiveBody := positiveCommonMultipleExistsTermAtBody bound).
  set (D := positiveBody :: map (rename S) G).
  set (bound1 := Term.rename S bound).
  set (sourceCode1 := Term.rename S sourceCode).
  assert (hpositive : BProv Ax_s D
    (positiveCommonMultipleThroughTermAt bound1 (tVar 0))).
  {
    apply BProv_ass.
    unfold D, positiveBody, positiveCommonMultipleExistsTermAtBody,
      bound1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_Ax_s_betaCodingStepTermAt_of_positiveCommon
    D bound1 sourceCode1 (tVar 0) hpositive) as hstep.
  pose proof (BProv_Ax_s_betaCodingStepExistsTermAt_of_term
    D bound1 sourceCode1 (tMul (tVar 0) (tSucc sourceCode1)) hstep)
    as hex.
  unfold goal.
  rewrite rename_betaCodingStepExistsTermAt.
  exact hex.
Qed.

Lemma BProv_Ax_s_ordinalCodeGraphTermAt_of_bodyExists :
  forall G step raw coded,
  BProv Ax_s G
    (ordinalCodeGraphBodyExistsTermAt step raw coded) ->
  BProv Ax_s G (ordinalCodeGraphTermAt raw coded).
Proof.
  intros G step raw coded htrace.
  set (target := ordinalCodeGraphTermAt raw coded).
  apply (BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_elim_opened
    G step raw coded target); [|exact htrace].
  set (body := ordinalCodeGraphBodyTermAt
    (tVar 0) (Term.rename S step)
    (Term.rename S raw) (Term.rename S coded)).
  set (D := body :: map (rename S) G).
  assert (hbody : BProv Ax_s D body).
  {
    apply BProv_ass.
    unfold D. simpl. left. reflexivity.
  }
  pose proof (BProv_ordinalCodeGraphTermAt_of_body
    Ax_s D (tVar 0) (Term.rename S step)
    (Term.rename S raw) (Term.rename S coded) hbody) as hgraph.
  unfold target.
  rewrite rename_ordinalCodeGraphTermAt.
  exact hgraph.
Qed.

Lemma BProv_Ax_s_ordinalCodeGraphTermAt_of_capacity :
  forall G raw coded capacity,
  BProv Ax_s G
    (ordinalCodeTraceCapacityTermAt raw coded capacity) ->
  BProv Ax_s G (ordinalCodeGraphTermAt raw coded).
Proof.
  intros G raw coded capacity hcapacity.
  set (target := ordinalCodeGraphTermAt raw coded).
  pose proof (BProv_Ax_s_betaCodingStepExistsTermAt
    G raw capacity) as hstepExists.
  apply (BProv_Ax_s_betaCodingStepExistsTermAt_elim_opened
    G raw capacity target); [|exact hstepExists].
  set (codingBody := betaCodingStepExistsTermAtBody raw capacity).
  set (D := codingBody :: map (rename S) G).
  set (raw1 := Term.rename S raw).
  set (coded1 := Term.rename S coded).
  set (capacity1 := Term.rename S capacity).
  assert (hcoding : BProv Ax_s D
    (betaCodingStepTermAt raw1 capacity1 (tVar 0))).
  {
    apply BProv_ass.
    unfold D, codingBody, betaCodingStepExistsTermAtBody,
      raw1, capacity1.
    simpl. left. reflexivity.
  }
  pose proof (BProv_rename_of_sentences Ax_s sentence_ax_s G _
    hcapacity S) as hcapacityRen.
  rewrite rename_ordinalCodeTraceCapacityTermAt in hcapacityRen.
  pose proof (BProv_context_cons Ax_s (map (rename S) G)
    codingBody _ hcapacityRen) as hcapacityD.
  change (BProv Ax_s D
    (ordinalCodeTraceCapacityTermAt raw1 coded1 capacity1))
    in hcapacityD.
  pose proof
    (BProv_Ax_s_ordinalCodeTraceCapacityTermAt_trace_of_coding
      D raw1 coded1 capacity1 (tVar 0) hcapacityD hcoding)
    as htrace.
  pose proof (BProv_Ax_s_ordinalCodeGraphTermAt_of_bodyExists
    D (tVar 0) raw1 coded1 htrace) as hgraph.
  unfold target.
  rewrite rename_ordinalCodeGraphTermAt.
  exact hgraph.
Qed.

Definition ordinalCodeGraphExistsTermAt (raw : term) : formula :=
  pEx (ordinalCodeGraphTermAt (Term.rename S raw) (tVar 0)).

Lemma subst_ordinalCodeGraphExistsTermAt : forall sigma raw,
  subst sigma (ordinalCodeGraphExistsTermAt raw) =
    ordinalCodeGraphExistsTermAt (Term.subst sigma raw).
Proof.
  intros sigma raw.
  unfold ordinalCodeGraphExistsTermAt.
  cbn [subst].
  rewrite subst_ordinalCodeGraphTermAt.
  simpl.
  rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodeGraphExistsTermAt : forall r raw,
  rename r (ordinalCodeGraphExistsTermAt raw) =
    ordinalCodeGraphExistsTermAt (Term.rename r raw).
Proof.
  intros r raw.
  rewrite <- subst_var_rename.
  rewrite subst_ordinalCodeGraphExistsTermAt.
  rewrite term_subst_var_rename.
  reflexivity.
Qed.

Lemma BProv_ordinalCodeGraphExistsTermAt_of_term :
  forall B G raw coded,
  BProv B G (ordinalCodeGraphTermAt raw coded) ->
  BProv B G (ordinalCodeGraphExistsTermAt raw).
Proof.
  intros B G raw coded hgraph.
  unfold ordinalCodeGraphExistsTermAt.
  apply (BProv_exI B G _ coded).
  rewrite subst_ordinalCodeGraphTermAt.
  simpl.
  rewrite term_subst_instTerm_rename_succ.
  exact hgraph.
Qed.

Lemma BProv_Ax_s_ordinalCodeGraphExistsTermAt_of_totalCapacity :
  forall G raw,
  BProv Ax_s G (ordinalCodeTotalCapacityTermAt raw) ->
  BProv Ax_s G (ordinalCodeGraphExistsTermAt raw).
Proof.
  intros G raw htotal.
  set (target := ordinalCodeGraphExistsTermAt raw).
  set (pairBody := ordinalCodeTraceCapacityTermAt
    (Term.rename (fun n => n + 2) raw) (tVar 1) (tVar 0)).
  assert (holdEx : BProv Ax_s G (pEx (pEx pairBody))).
  {
    unfold ordinalCodeTotalCapacityTermAt in htotal.
    fold pairBody in htotal.
    exact htotal.
  }
  apply (BProv_two_exE_of_sentences
    Ax_s sentence_ax_s G pairBody target holdEx).
  set (C := pairBody ::
    map (rename S) (pEx pairBody :: map (rename S) G)).
  change (BProv Ax_s C (rename S (rename S target))).
      set (raw2 := Term.rename (fun n => n + 2) raw).
      assert (hcapacity : BProv Ax_s C
        (ordinalCodeTraceCapacityTermAt raw2 (tVar 1) (tVar 0))).
      {
        apply BProv_ass.
        unfold C, pairBody, raw2. simpl. left. reflexivity.
      }
      pose proof (BProv_Ax_s_ordinalCodeGraphTermAt_of_capacity
        C raw2 (tVar 1) (tVar 0) hcapacity) as hgraph.
      pose proof (BProv_ordinalCodeGraphExistsTermAt_of_term
        Ax_s C raw2 (tVar 1) hgraph) as hex.
      unfold target.
      rewrite !rename_ordinalCodeGraphExistsTermAt.
      rewrite term_rename_succ_twice_add_two.
      change (BProv Ax_s C (ordinalCodeGraphExistsTermAt raw2)).
      exact hex.
Qed.

Theorem OrdinalCodeGraphProofs_total_of_adjoinExistence :
  PAHFAdjoinExistence ->
  forall (G : list formula) (raw : term),
  BProv Ax_s G
    (pEx (ordinalCodeGraphTermAt (Term.rename S raw) (tVar 0))).
Proof.
  intros hadjoinTotal G raw.
  pose proof (BProv_Ax_s_all_ordinalCodeTotalCapacityTermAt
    hadjoinTotal G) as hall.
  pose proof (BProv_allE Ax_s G _ raw hall) as hraw.
  rewrite subst_ordinalCodeTotalCapacityTermAt in hraw.
  simpl in hraw.
  pose proof (BProv_Ax_s_ordinalCodeGraphExistsTermAt_of_totalCapacity
    G raw hraw) as hex.
  unfold ordinalCodeGraphExistsTermAt in hex.
  exact hex.
Qed.
