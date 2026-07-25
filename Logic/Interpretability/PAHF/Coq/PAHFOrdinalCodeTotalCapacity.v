(* ===================================================================== *)
(*  PAHFOrdinalCodeTotalCapacity.v                                        *)
(*                                                                       *)
(*  Capacity/CRT layer for internal PA totality of the finite-ordinal     *)
(*  Ackermann code graph.  It imports the frozen local trace-extension    *)
(*  transformer and supplies the arithmetic majorant induction.           *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFProofCalculus
  PAHFOrdinalCode PAHFOrdinalCodeTotal.

Import ListNotations.
Import PA PA.Term PA.Formula.

(* Compatibility aliases: the canonical definitions now live in [PA.Formula]. *)
Definition betaCodingStepTermAt := PA.Formula.betaCodingStepTermAt.

Definition betaCodingStepExistsTermAt :=
  PA.Formula.betaCodingStepExistsTermAt.

Definition betaCodingStepExistsTermAtBody :=
  PA.Formula.betaCodingStepExistsTermAtBody.

Definition betaCodeExtensionExistsTermAtBody
    (oldCode step target newOut : term) : formula :=
  betaCodeExtensionTermAt
    (Term.rename S oldCode)
    (Term.rename S step)
    (Term.rename S target)
    (Term.rename S newOut)
    (tVar 0).

Lemma subst_leTermAt : forall sigma a b,
  subst sigma (leTermAt a b) =
    leTermAt (Term.subst sigma a) (Term.subst sigma b).
Proof.
  intros sigma a b.
  exact (PA.Formula.subst_leTermAt sigma a b).
Qed.

Lemma rename_leTermAt : forall r a b,
  rename r (leTermAt a b) =
    leTermAt (Term.rename r a) (Term.rename r b).
Proof.
  intros r a b.
  exact (PA.Formula.rename_leTermAt r a b).
Qed.

Lemma subst_dvdTermTermAt : forall sigma divisor value,
  subst sigma (dvdTermTermAt divisor value) =
    dvdTermTermAt
      (Term.subst sigma divisor) (Term.subst sigma value).
Proof.
  intros sigma divisor value.
  exact (PA.Formula.subst_dvdTermTermAt sigma divisor value).
Qed.

Lemma rename_dvdTermTermAt : forall r divisor value,
  rename r (dvdTermTermAt divisor value) =
    dvdTermTermAt
      (Term.rename r divisor) (Term.rename r value).
Proof.
  intros r divisor value.
  exact (PA.Formula.rename_dvdTermTermAt r divisor value).
Qed.

Lemma term_rename_betaModTermTerm : forall r step index,
  Term.rename r (betaModTermTerm step index) =
    betaModTermTerm (Term.rename r step) (Term.rename r index).
Proof.
  intros r step index.
  exact (PA.Formula.term_rename_betaModTermTerm r step index).
Qed.

Lemma subst_commonMultipleThroughTermAt : forall sigma bound multiple,
  subst sigma (commonMultipleThroughTermAt bound multiple) =
    commonMultipleThroughTermAt
      (Term.subst sigma bound) (Term.subst sigma multiple).
Proof.
  intros sigma bound multiple.
  exact (PA.Formula.subst_commonMultipleThroughTermAt
    sigma bound multiple).
Qed.

Lemma rename_commonMultipleThroughTermAt : forall r bound multiple,
  rename r (commonMultipleThroughTermAt bound multiple) =
    commonMultipleThroughTermAt
      (Term.rename r bound) (Term.rename r multiple).
Proof.
  intros r bound multiple.
  exact (PA.Formula.rename_commonMultipleThroughTermAt r bound multiple).
Qed.

Lemma subst_positiveCommonMultipleThroughTermAt :
  forall sigma bound multiple,
  subst sigma (positiveCommonMultipleThroughTermAt bound multiple) =
    positiveCommonMultipleThroughTermAt
      (Term.subst sigma bound) (Term.subst sigma multiple).
Proof.
  intros sigma bound multiple.
  exact (PA.Formula.subst_positiveCommonMultipleThroughTermAt
    sigma bound multiple).
Qed.

Lemma rename_positiveCommonMultipleThroughTermAt :
  forall r bound multiple,
  rename r (positiveCommonMultipleThroughTermAt bound multiple) =
    positiveCommonMultipleThroughTermAt
      (Term.rename r bound) (Term.rename r multiple).
Proof.
  intros r bound multiple.
  exact (PA.Formula.rename_positiveCommonMultipleThroughTermAt
    r bound multiple).
Qed.

Lemma subst_betaCodingStepTermAt : forall sigma bound sourceCode step,
  subst sigma (betaCodingStepTermAt bound sourceCode step) =
    betaCodingStepTermAt
      (Term.subst sigma bound)
      (Term.subst sigma sourceCode)
      (Term.subst sigma step).
Proof.
  intros sigma bound sourceCode step.
  exact (PA.Formula.subst_betaCodingStepTermAt
    sigma bound sourceCode step).
Qed.

Lemma rename_betaCodingStepTermAt : forall r bound sourceCode step,
  rename r (betaCodingStepTermAt bound sourceCode step) =
    betaCodingStepTermAt
      (Term.rename r bound)
      (Term.rename r sourceCode)
      (Term.rename r step).
Proof.
  intros r bound sourceCode step.
  exact (PA.Formula.rename_betaCodingStepTermAt
    r bound sourceCode step).
Qed.

Definition ordinalCodeGraphBodyExistsTermAt
    (step raw coded : term) : formula :=
  pEx
    (ordinalCodeGraphBodyTermAt
      (tVar 0)
      (Term.rename S step)
      (Term.rename S raw)
      (Term.rename S coded)).

Lemma subst_ordinalCodeGraphBodyExistsTermAt :
  forall sigma step raw coded,
  subst sigma (ordinalCodeGraphBodyExistsTermAt step raw coded) =
    ordinalCodeGraphBodyExistsTermAt
      (Term.subst sigma step)
      (Term.subst sigma raw)
      (Term.subst sigma coded).
Proof.
  intros sigma step raw coded.
  unfold ordinalCodeGraphBodyExistsTermAt.
  cbn [subst].
  rewrite subst_ordinalCodeGraphBodyTermAt.
  simpl.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodeGraphBodyExistsTermAt :
  forall r step raw coded,
  rename r (ordinalCodeGraphBodyExistsTermAt step raw coded) =
    ordinalCodeGraphBodyExistsTermAt
      (Term.rename r step)
      (Term.rename r raw)
      (Term.rename r coded).
Proof.
  intros r step raw coded.
  rename_from_subst subst_ordinalCodeGraphBodyExistsTermAt.
Qed.

Lemma BProv_ordinalCodeGraphBodyExistsTermAt_of_term :
  forall B G sequenceCode step raw coded,
  BProv B G
    (ordinalCodeGraphBodyTermAt sequenceCode step raw coded) ->
  BProv B G (ordinalCodeGraphBodyExistsTermAt step raw coded).
Proof.
  intros B G sequenceCode step raw coded hbody.
  apply (BProv_exI B G _ sequenceCode).
  rewrite subst_ordinalCodeGraphBodyTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hbody.
Qed.

Lemma BProv_Ax_s_ordinalCodeGraphBodyExistsTermAt_elim_opened :
  forall G step raw coded target,
  BProv Ax_s
    (ordinalCodeGraphBodyTermAt
        (tVar 0)
        (Term.rename S step)
        (Term.rename S raw)
        (Term.rename S coded) ::
      map (rename S) G)
    (rename S target) ->
  BProv Ax_s G (ordinalCodeGraphBodyExistsTermAt step raw coded) ->
  BProv Ax_s G target.
Proof.
  intros G step raw coded target hopened hex.
  exact (BProv_exE_of_sentences Ax_s G
    (ordinalCodeGraphBodyTermAt
      (tVar 0) (Term.rename S step)
      (Term.rename S raw) (Term.rename S coded))
    target sentence_ax_s hex hopened).
Qed.

(* A strict inequality exposes the same positive difference as the witness
   for [S lower <= upper]. *)
Lemma BProv_Ax_s_leTermAt_succ_left_of_ltTermAt :
  forall G lower upper,
  BProv Ax_s G (ltTermAt lower upper) ->
  BProv Ax_s G (leTermAt (tSucc lower) upper).
Proof.
  intros G lower upper hlt.
  set (target := leTermAt (tSucc lower) upper).
  apply (BProv_Ax_s_ltTermAt_elim_opened
    G lower upper target); [|exact hlt].
  set (body := pEq
    (tAdd (Term.rename S lower) (tSucc (tVar 0)))
    (Term.rename S upper)).
  set (D := body :: map (rename S) G).
  set (lower1 := Term.rename S lower).
  set (upper1 := Term.rename S upper).
  assert (hopened : BProv Ax_s D
    (pEq (tAdd lower1 (tSucc (tVar 0))) upper1)).
  {
    apply BProv_ass.
    unfold D, body, lower1, upper1. simpl. left. reflexivity.
  }
  pose proof (BProv_Ax_s_succ_add_terms
    D lower1 (tVar 0)) as hsuccAdd.
  assert (haddSucc : BProv Ax_s D
    (pEq (tAdd lower1 (tSucc (tVar 0)))
      (tSucc (tAdd lower1 (tVar 0))))).
  {
    apply BProv_Ax_s_addSucc_terms.
  }
  pose proof (BProv_eqTrans Ax_s D _ _ _ hsuccAdd
    (BProv_eqTrans Ax_s D _ _ _
      (BProv_eqSym Ax_s D _ _ haddSucc) hopened)) as hleEq.
  assert (hsubst : BProv Ax_s D
    (subst (instTerm (tVar 0))
      (pEq
        (tAdd (Term.rename S (tSucc lower1)) (tVar 0))
        (Term.rename S upper1)))).
  {
    cbn [subst]. simpl.
    repeat rewrite term_subst_instTerm_rename_succ.
    exact hleEq.
  }
  assert (hle : BProv Ax_s D (leTermAt (tSucc lower1) upper1)).
  {
    unfold leTermAt.
    exact (BProv_exI Ax_s D _ (tVar 0) hsubst).
  }
  unfold target, D, body, lower1, upper1 in *.
  rewrite rename_leTermAt.
  simpl.
  exact hle.
Qed.

Lemma BProv_Ax_s_ltTermAt_of_lt_leTermAt :
  forall G lower middle upper,
  BProv Ax_s G (ltTermAt lower middle) ->
  BProv Ax_s G (leTermAt middle upper) ->
  BProv Ax_s G (ltTermAt lower upper).
Proof.
  intros G lower middle upper hlt hle.
  apply BProv_Ax_s_ltTermAt_of_succ_leTermAt.
  exact (BProv_Ax_s_leTermAt_trans G
    (tSucc lower) middle upper
    (BProv_Ax_s_leTermAt_succ_left_of_ltTermAt
      G lower middle hlt) hle).
Qed.

Lemma BProv_Ax_s_commonMultipleThroughTermAt_of_le :
  forall G lower upper multiple,
  BProv Ax_s G (commonMultipleThroughTermAt upper multiple) ->
  BProv Ax_s G (leTermAt lower upper) ->
  BProv Ax_s G (commonMultipleThroughTermAt lower multiple).
Proof.
  intros G lower upper multiple hcommon hle.
  set (antecedent :=
    ltTermAt (tVar 0) (Term.rename S lower)).
  set (consequent :=
    dvdTermTermAt (tSucc (tVar 0)) (Term.rename S multiple)).
  set (C := antecedent :: map (rename S) G).
  assert (hbody : BProv Ax_s C consequent).
  {
    set (lower1 := Term.rename S lower).
    set (upper1 := Term.rename S upper).
    set (multiple1 := Term.rename S multiple).
    assert (hltLower : BProv Ax_s C
      (ltTermAt (tVar 0) lower1)).
    {
      apply BProv_ass.
      unfold C, antecedent, lower1. simpl. left. reflexivity.
    }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G antecedent _ hle) as hleC.
    rewrite rename_leTermAt in hleC.
    change (BProv Ax_s C (leTermAt lower1 upper1)) in hleC.
    pose proof (BProv_Ax_s_ltTermAt_of_lt_leTermAt
      C (tVar 0) lower1 upper1 hltLower hleC) as hltUpper.
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G antecedent _ hcommon) as hcommonC.
    rewrite rename_commonMultipleThroughTermAt in hcommonC.
    change (BProv Ax_s C
      (commonMultipleThroughTermAt upper1 multiple1)) in hcommonC.
    pose proof
      (BProv_Ax_s_dvdTermTermAt_of_commonMultipleThroughTermAt
        C upper1 multiple1 (tVar 0) hcommonC hltUpper) as hdvd.
    change (BProv Ax_s C consequent) in hdvd.
    exact hdvd.
  }
  assert (himp : BProv Ax_s (map (rename S) G)
    (pImp antecedent consequent)).
  {
    unfold C in hbody.
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent consequent hbody).
  }
  assert (hall : BProv Ax_s G
    (pAll (pImp antecedent consequent))).
  {
    exact (BProv_allI_of_sentences Ax_s G _ sentence_ax_s himp).
  }
  unfold commonMultipleThroughTermAt.
  change (BProv Ax_s G (pAll (pImp antecedent consequent))).
  exact hall.
Qed.

Lemma BProv_Ax_s_leTermAt_step_betaModTermTerm :
  forall G step index,
  BProv Ax_s G
    (leTermAt step (betaModTermTerm step index)).
Proof.
  intros G step index.
  set (core := tMul index step).
  assert (hsuccMul : BProv Ax_s G
    (pEq (tMul (tSucc index) step) (tAdd core step))).
  {
    unfold core.
    apply BProv_Ax_s_succ_mul_terms.
  }
  pose proof (BProv_eq_congr_succ Ax_s G _ _ hsuccMul)
    as hsuccMulCong.
  pose proof (BProv_Ax_s_add_comm_terms G core step) as hcomm.
  pose proof (BProv_eq_congr_succ Ax_s G _ _ hcomm) as hcommSucc.
  assert (haddSucc : BProv Ax_s G
    (pEq (tAdd step (tSucc core))
      (tSucc (tAdd step core)))).
  {
    apply BProv_Ax_s_addSucc_terms.
  }
  assert (hmod : BProv Ax_s G
    (pEq (betaModTermTerm step index)
      (tAdd step (tSucc core)))).
  {
    unfold betaModTermTerm.
    exact (BProv_eqTrans Ax_s G _ _ _ hsuccMulCong
      (BProv_eqTrans Ax_s G _ _ _ hcommSucc
        (BProv_eqSym Ax_s G _ _ haddSucc))).
  }
  exact (BProv_Ax_s_leTermAt_of_eq_add_right_terms
    G step (betaModTermTerm step index) (tSucc core) hmod).
Qed.

Lemma BProv_Ax_s_betaCodingStepTermAt_old_of_sum_capacity :
  forall G raw oldCapacity newCoded step,
  BProv Ax_s G
    (betaCodingStepTermAt (tSucc raw)
      (tAdd oldCapacity newCoded) step) ->
  BProv Ax_s G (betaCodingStepTermAt raw oldCapacity step).
Proof.
  intros G raw oldCapacity newCoded step hcoding.
  unfold betaCodingStepTermAt in hcoding.
  pose proof (BProv_andE1 Ax_s G _ _ hcoding) as hcommonSucc.
  pose proof (BProv_andE2 Ax_s G _ _ hcoding) as hlargeSum.
  assert (hcommon : BProv Ax_s G
    (commonMultipleThroughTermAt raw step)).
  {
    exact (BProv_Ax_s_commonMultipleThroughTermAt_of_le
      G raw (tSucc raw) step hcommonSucc
      (BProv_Ax_s_leTermAt_self_succ G raw)).
  }
  assert (holdLeSum : BProv Ax_s G
    (leTermAt oldCapacity (tAdd oldCapacity newCoded))).
  {
    apply (BProv_Ax_s_leTermAt_of_eq_add_right_terms
      G oldCapacity (tAdd oldCapacity newCoded) newCoded).
    apply BProv_eqRefl.
  }
  pose proof (BProv_Ax_s_leTermAt_succ_succ
    G oldCapacity (tAdd oldCapacity newCoded) holdLeSum)
    as hsuccOldLeSum.
  pose proof (BProv_Ax_s_leTermAt_trans G
    (tSucc oldCapacity) (tSucc (tAdd oldCapacity newCoded)) step
    hsuccOldLeSum hlargeSum) as hlargeOld.
  unfold betaCodingStepTermAt.
  exact (BProv_andI Ax_s G _ _ hcommon hlargeOld).
Qed.

Definition ordinalCodeTraceCapacityTermAt
    (raw coded capacity : term) : formula :=
  pAll
    (pImp
      (betaCodingStepTermAt
        (Term.rename S raw)
        (Term.rename S capacity)
        (tVar 0))
      (ordinalCodeGraphBodyExistsTermAt
        (tVar 0)
        (Term.rename S raw)
        (Term.rename S coded))).

Lemma subst_ordinalCodeTraceCapacityTermAt :
  forall sigma raw coded capacity,
  subst sigma (ordinalCodeTraceCapacityTermAt raw coded capacity) =
    ordinalCodeTraceCapacityTermAt
      (Term.subst sigma raw)
      (Term.subst sigma coded)
      (Term.subst sigma capacity).
Proof.
  intros sigma raw coded capacity.
  unfold ordinalCodeTraceCapacityTermAt.
  cbn [subst].
  rewrite subst_betaCodingStepTermAt.
  rewrite subst_ordinalCodeGraphBodyExistsTermAt.
  simpl.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_ordinalCodeTraceCapacityTermAt :
  forall r raw coded capacity,
  rename r (ordinalCodeTraceCapacityTermAt raw coded capacity) =
    ordinalCodeTraceCapacityTermAt
      (Term.rename r raw)
      (Term.rename r coded)
      (Term.rename r capacity).
Proof.
  intros r raw coded capacity.
  rename_from_subst subst_ordinalCodeTraceCapacityTermAt.
Qed.

Lemma BProv_Ax_s_betaTermTermAt_zero_code_zero :
  forall G step index,
  BProv Ax_s G (betaTermTermAt tZero tZero step index).
Proof.
  intros G step index.
  set (modulus := betaModTermTerm step index).
  assert (hlt : BProv Ax_s G (ltTermAt tZero modulus)).
  {
    unfold modulus, betaModTermTerm.
    apply BProv_Ax_s_ltTermAt_zero_succ.
  }
  assert (hzeroMul : BProv Ax_s G
    (pEq (tMul tZero modulus) tZero)).
  { apply BProv_Ax_s_zero_mul_term. }
  assert (haddZero : BProv Ax_s G
    (pEq (tAdd tZero tZero) tZero)).
  {
    apply BProv_Ax_s_addZero_term.
  }
  pose proof (BProv_eq_congr_add_left Ax_s G _ _ tZero hzeroMul)
    as hcong.
  assert (hvalue : BProv Ax_s G
    (pEq tZero (tAdd (tMul tZero modulus) tZero))).
  {
    exact (BProv_eqSym Ax_s G _ _
      (BProv_eqTrans Ax_s G _ _ _ hcong haddZero)).
  }
  pose proof (BProv_Ax_s_remTermTermAt_of_eq_add_mul_terms
    G tZero tZero modulus tZero hlt hvalue) as hrem.
  exact (BProv_Ax_s_betaTermTermAt_of_rem
    G tZero tZero step index modulus
    (BProv_eqRefl Ax_s G modulus) hrem).
Qed.

Lemma BProv_Ax_s_ordinalCodeGraphBodyTermAt_zero_at_step :
  forall G step,
  BProv Ax_s G (leTermAt (tSucc tZero) step) ->
  BProv Ax_s G
    (ordinalCodeGraphBodyTermAt tZero step tZero tZero).
Proof.
  intros G step _.
  pose proof (BProv_Ax_s_betaTermTermAt_zero_code_zero
    G step tZero) as hentry.
  pose proof (BProv_Ax_s_ordinalCodeStepsTermAt_zero
    G tZero step) as hsteps.
  unfold ordinalCodeGraphBodyTermAt.
  exact (BProv_andI Ax_s G _ _ hentry
    (BProv_andI Ax_s G _ _ hentry hsteps)).
Qed.

Lemma BProv_Ax_s_ordinalCodeTraceCapacityTermAt_zero : forall G,
  BProv Ax_s G
    (ordinalCodeTraceCapacityTermAt tZero tZero tZero).
Proof.
  intro G.
  set (antecedent := betaCodingStepTermAt tZero tZero (tVar 0)).
  set (consequent :=
    ordinalCodeGraphBodyExistsTermAt (tVar 0) tZero tZero).
  set (C := antecedent :: map (rename S) G).
  assert (hbody : BProv Ax_s C consequent).
  {
    assert (hcoding : BProv Ax_s C antecedent).
    {
      apply BProv_ass.
      unfold C. simpl. left. reflexivity.
    }
    unfold antecedent, betaCodingStepTermAt in hcoding.
    pose proof (BProv_andE2 Ax_s C _ _ hcoding) as hlarge.
    pose proof (BProv_Ax_s_ordinalCodeGraphBodyTermAt_zero_at_step
      C (tVar 0) hlarge) as hzero.
    unfold consequent.
    exact (BProv_ordinalCodeGraphBodyExistsTermAt_of_term
      Ax_s C tZero (tVar 0) tZero tZero hzero).
  }
  assert (himp : BProv Ax_s (map (rename S) G)
    (pImp antecedent consequent)).
  {
    unfold C in hbody.
    exact (BProv_impI Ax_s (map (rename S) G)
      antecedent consequent hbody).
  }
  assert (hall : BProv Ax_s G
    (pAll (pImp antecedent consequent))).
  {
    exact (BProv_allI_of_sentences Ax_s G _ sentence_ax_s himp).
  }
  unfold ordinalCodeTraceCapacityTermAt.
  change (BProv Ax_s G (pAll (pImp antecedent consequent))).
  exact hall.
Qed.

Lemma BProv_Ax_s_ordinalCodeTraceCapacityTermAt_trace_of_coding :
  forall G raw coded capacity step,
  BProv Ax_s G
    (ordinalCodeTraceCapacityTermAt raw coded capacity) ->
  BProv Ax_s G (betaCodingStepTermAt raw capacity step) ->
  BProv Ax_s G
    (ordinalCodeGraphBodyExistsTermAt step raw coded).
Proof.
  intros G raw coded capacity step hcapacity hcoding.
  pose proof (BProv_allE Ax_s G _ step hcapacity) as himp.
  cbn [subst] in himp.
  rewrite subst_betaCodingStepTermAt in himp.
  rewrite subst_ordinalCodeGraphBodyExistsTermAt in himp.
  simpl in himp.
  repeat rewrite term_subst_instTerm_rename_succ in himp.
  exact (BProv_mp Ax_s G
    (betaCodingStepTermAt raw capacity step)
    (ordinalCodeGraphBodyExistsTermAt step raw coded)
    himp hcoding).
Qed.

Lemma BProv_Ax_s_dvdTermTermAt_elim_opened_for_crt :
  forall G divisor value target,
  BProv Ax_s
    (pEq
        (tMul (Term.rename S divisor) (tVar 0))
        (Term.rename S value) ::
      map (rename S) G)
    (rename S target) ->
  BProv Ax_s G (dvdTermTermAt divisor value) ->
  BProv Ax_s G target.
Proof.
  intros G divisor value target hbody hdvd.
  unfold dvdTermTermAt in hdvd.
  exact (BProv_exE_of_sentences Ax_s G
    (pEq (tMul (Term.rename S divisor) (tVar 0))
      (Term.rename S value))
    target sentence_ax_s hdvd hbody).
Qed.

Lemma BProv_Ax_s_betaTermTermAt_crtExtend_preserve_of_dvd :
  forall G out oldCode product inverse delta step index,
  BProv Ax_s G (betaTermTermAt out oldCode step index) ->
  BProv Ax_s G
    (dvdTermTermAt (betaModTermTerm step index) product) ->
  BProv Ax_s G
    (betaTermTermAt out
      (crtExtendCodeTerm oldCode product inverse delta)
      step index).
Proof.
  intros G out oldCode product inverse delta step index hbeta hdvd.
  set (target := betaTermTermAt out
    (crtExtendCodeTerm oldCode product inverse delta) step index).
  apply (BProv_Ax_s_dvdTermTermAt_elim_opened_for_crt
    G (betaModTermTerm step index) product target); [|exact hdvd].
  set (factorBody := pEq
    (tMul (Term.rename S (betaModTermTerm step index)) (tVar 0))
    (Term.rename S product)).
  set (D := factorBody :: map (rename S) G).
  set (out1 := Term.rename S out).
  set (oldCode1 := Term.rename S oldCode).
  set (product1 := Term.rename S product).
  set (inverse1 := Term.rename S inverse).
  set (delta1 := Term.rename S delta).
  set (step1 := Term.rename S step).
  set (index1 := Term.rename S index).
  set (modulus1 := betaModTermTerm step1 index1).
  assert (hfactor : BProv Ax_s D
    (pEq (tMul modulus1 (tVar 0)) product1)).
  {
    apply BProv_ass.
    unfold D, factorBody, modulus1, step1, index1, product1,
      betaModTermTerm.
    simpl. left. reflexivity.
  }
  pose proof (BProv_Ax_s_mul_comm_terms
    D (tVar 0) modulus1) as hcomm.
  assert (hProduct : BProv Ax_s D
    (pEq product1 (tMul (tVar 0) modulus1))).
  {
    exact (BProv_eqSym Ax_s D _ _
      (BProv_eqTrans Ax_s D _ _ _ hcomm hfactor)).
  }
  pose proof (BProv_rename_succ_context_cons_of_sentences
    Ax_s sentence_ax_s G factorBody _ hbeta) as hbetaD.
  rewrite rename_betaTermTermAt in hbetaD.
  change (BProv Ax_s D
    (betaTermTermAt out1 oldCode1 step1 index1)) in hbetaD.
  pose proof (BProv_Ax_s_betaTermTermAt_crtExtend_preserve
    D out1 oldCode1 product1 inverse1 delta1 step1 index1 (tVar 0)
    hbetaD hProduct) as hnew.
  unfold target.
  rewrite rename_betaTermTermAt.
  unfold crtExtendCodeTerm.
  simpl.
  change (BProv Ax_s D
    (betaTermTermAt out1
      (crtExtendCodeTerm oldCode1 product1 inverse1 delta1)
      step1 index1)).
  exact hnew.
Qed.

Lemma subst_betaPrefixDividesTermAt : forall sigma step bound product,
  subst sigma (betaPrefixDividesTermAt step bound product) =
    betaPrefixDividesTermAt
      (Term.subst sigma step)
      (Term.subst sigma bound)
      (Term.subst sigma product).
Proof.
  intros sigma step bound product.
  exact (PA.Formula.subst_betaPrefixDividesTermAt
    sigma step bound product).
Qed.

Lemma rename_betaPrefixDividesTermAt : forall r step bound product,
  rename r (betaPrefixDividesTermAt step bound product) =
    betaPrefixDividesTermAt
      (Term.rename r step)
      (Term.rename r bound)
      (Term.rename r product).
Proof.
  intros r step bound product.
  exact (PA.Formula.rename_betaPrefixDividesTermAt
    r step bound product).
Qed.

Lemma BProv_Ax_s_betaPrefixAgreementTermAt_crtExtend :
  forall G oldCode product inverse delta step bound,
  BProv Ax_s G (betaPrefixDividesTermAt step bound product) ->
  BProv Ax_s G
    (betaPrefixAgreementTermAt oldCode
      (crtExtendCodeTerm oldCode product inverse delta)
      step bound).
Proof.
  intros G oldCode product inverse delta step bound hprefix.
  set (newCode := crtExtendCodeTerm oldCode product inverse delta).
  set (outerAntecedent :=
    ltTermAt (tVar 0) (Term.rename S bound)).
  set (oldEntry := betaTermTermAt (tVar 0)
    (Term.rename (fun n => n + 2) oldCode)
    (Term.rename (fun n => n + 2) step)
    (tVar 1)).
  set (newEntry := betaTermTermAt (tVar 0)
    (Term.rename (fun n => n + 2) newCode)
    (Term.rename (fun n => n + 2) step)
    (tVar 1)).
  set (innerBody := pImp oldEntry newEntry).
  set (outerBody := pImp outerAntecedent (pAll innerBody)).
  set (C := outerAntecedent :: map (rename S) G).
  assert (hinnerAll : BProv Ax_s C (pAll innerBody)).
  {
    set (oldCode1 := Term.rename S oldCode).
    set (product1 := Term.rename S product).
    set (inverse1 := Term.rename S inverse).
    set (delta1 := Term.rename S delta).
    set (step1 := Term.rename S step).
    set (bound1 := Term.rename S bound).
    assert (hlt : BProv Ax_s C (ltTermAt (tVar 0) bound1)).
    {
      apply BProv_ass.
      unfold C, outerAntecedent, bound1. simpl. left. reflexivity.
    }
    pose proof (BProv_rename_succ_context_cons_of_sentences
      Ax_s sentence_ax_s G outerAntecedent _ hprefix) as hprefixC.
    rewrite rename_betaPrefixDividesTermAt in hprefixC.
    change (BProv Ax_s C
      (betaPrefixDividesTermAt step1 bound1 product1)) in hprefixC.
    pose proof
      (BProv_Ax_s_dvdTermTermAt_of_betaPrefixDividesTermAt
        C step1 bound1 product1 (tVar 0) hprefixC hlt) as hdvd.
    set (D := oldEntry :: map (rename S) C).
    assert (hnew : BProv Ax_s D newEntry).
    {
      set (oldCode2 := Term.rename (fun n => n + 2) oldCode).
      set (product2 := Term.rename (fun n => n + 2) product).
      set (inverse2 := Term.rename (fun n => n + 2) inverse).
      set (delta2 := Term.rename (fun n => n + 2) delta).
      set (step2 := Term.rename (fun n => n + 2) step).
      assert (hold : BProv Ax_s D
        (betaTermTermAt (tVar 0) oldCode2 step2 (tVar 1))).
      {
        apply BProv_ass.
        unfold D, oldEntry, oldCode2, step2. simpl. left. reflexivity.
      }
      pose proof (BProv_rename_succ_context_cons_of_sentences
        Ax_s sentence_ax_s C oldEntry _ hdvd) as hdvdD.
      rewrite rename_dvdTermTermAt in hdvdD.
      replace
        (dvdTermTermAt
          (Term.rename S (betaModTermTerm step1 (tVar 0)))
          (Term.rename S product1))
        with
        (dvdTermTermAt
          (betaModTermTerm step2 (tVar 1)) product2)
        in hdvdD.
      2:{
        unfold step1, product1, step2, product2.
        rewrite term_rename_betaModTermTerm.
        simpl.
        repeat rewrite term_rename_succ_twice_add_two.
        reflexivity.
      }
      pose proof
        (BProv_Ax_s_betaTermTermAt_crtExtend_preserve_of_dvd
          D (tVar 0) oldCode2 product2 inverse2 delta2
          step2 (tVar 1) hold hdvdD) as hraw.
      unfold newEntry, newCode.
      unfold crtExtendCodeTerm.
      simpl.
      change (BProv Ax_s D
        (betaTermTermAt (tVar 0)
          (crtExtendCodeTerm oldCode2 product2 inverse2 delta2)
          step2 (tVar 1))).
      exact hraw.
    }
    assert (hinnerImp : BProv Ax_s (map (rename S) C)
      (pImp oldEntry newEntry)).
    {
      unfold D in hnew.
      exact (BProv_impI Ax_s (map (rename S) C)
        oldEntry newEntry hnew).
    }
    unfold innerBody.
    exact (BProv_allI_of_sentences Ax_s C _ sentence_ax_s hinnerImp).
  }
  assert (houterImp : BProv Ax_s (map (rename S) G) outerBody).
  {
    unfold C in hinnerAll.
    unfold outerBody.
    exact (BProv_impI Ax_s (map (rename S) G)
      outerAntecedent (pAll innerBody) hinnerAll).
  }
  pose proof (BProv_allI_of_sentences Ax_s G outerBody
    sentence_ax_s houterImp) as hall.
  unfold betaPrefixAgreementTermAt.
  change (BProv Ax_s G (pAll outerBody)).
  exact hall.
Qed.

Definition crtSuccessorCorrectionTerm
    (oldCode modulusPred newRem : term) : term :=
  tAdd (tMul modulusPred oldCode) newRem.

Lemma BProv_Ax_s_crtExtendCodeTerm_new_decomposition_of_code :
  forall G oldCode product inverse delta modulus inverseQuot
      correctionQuot newRem,
  BProv Ax_s G
    (pEq (tMul product inverse)
      (tSucc (tMul modulus inverseQuot))) ->
  BProv Ax_s G
    (pEq (tAdd oldCode delta)
      (tAdd (tMul correctionQuot modulus) newRem)) ->
  BProv Ax_s G
    (pEq (crtExtendCodeTerm oldCode product inverse delta)
      (tAdd
        (tMul
          (tAdd (tMul inverseQuot delta) correctionQuot)
          modulus)
        newRem)).
Proof.
  intros G oldCode product inverse delta modulus inverseQuot
    correctionQuot newRem hInverse hDelta.
  set (increment := tMul inverse delta).
  set (inverseContribution := tMul inverseQuot delta).
  set (addedBase := tMul inverseContribution modulus).
  set (correctionBase := tMul correctionQuot modulus).
  assert (hincrementAssoc : BProv Ax_s G
    (pEq (tMul product increment)
      (tMul (tMul product inverse) delta))).
  {
    unfold increment.
    exact (BProv_eqSym Ax_s G _ _
      (BProv_Ax_s_mul_assoc_terms G product inverse delta)).
  }
  pose proof (BProv_eq_congr_mul_left Ax_s G _ _ delta hInverse)
    as hinverseCong.
  assert (hsuccMul : BProv Ax_s G
    (pEq (tMul (tSucc (tMul modulus inverseQuot)) delta)
      (tAdd (tMul (tMul modulus inverseQuot) delta) delta))).
  { apply BProv_Ax_s_succ_mul_terms. }
  assert (hbaseAssoc : BProv Ax_s G
    (pEq (tMul (tMul modulus inverseQuot) delta)
      (tMul modulus inverseContribution))).
  {
    unfold inverseContribution.
    apply BProv_Ax_s_mul_assoc_terms.
  }
  assert (hbaseComm : BProv Ax_s G
    (pEq (tMul modulus inverseContribution) addedBase)).
  {
    unfold addedBase.
    apply BProv_Ax_s_mul_comm_terms.
  }
  pose proof (BProv_eqTrans Ax_s G _ _ _ hbaseAssoc hbaseComm)
    as hbase.
  pose proof (BProv_eq_congr_add_left Ax_s G _ _ delta hbase)
    as hbaseCong.
  assert (hincrement : BProv Ax_s G
    (pEq (tMul product increment) (tAdd addedBase delta))).
  {
    exact (BProv_eqTrans Ax_s G _ _ _ hincrementAssoc
      (BProv_eqTrans Ax_s G _ _ _ hinverseCong
        (BProv_eqTrans Ax_s G _ _ _ hsuccMul hbaseCong))).
  }
  assert (hcode : BProv Ax_s G
    (pEq (crtExtendCodeTerm oldCode product inverse delta)
      (tAdd oldCode (tAdd addedBase delta)))).
  {
    unfold crtExtendCodeTerm, increment.
    exact (BProv_eq_congr_add_right Ax_s G oldCode _ _ hincrement).
  }
  pose proof (BProv_eqSym Ax_s G _ _
    (BProv_Ax_s_add_assoc_terms G oldCode addedBase delta))
    as hregroup1.
  pose proof (BProv_Ax_s_add_comm_terms G oldCode addedBase) as hcomm.
  pose proof (BProv_eq_congr_add_left Ax_s G _ _ delta hcomm)
    as hcommCong.
  pose proof (BProv_Ax_s_add_assoc_terms G addedBase oldCode delta)
    as hregroup2.
  assert (hdeltaCong : BProv Ax_s G
    (pEq (tAdd addedBase (tAdd oldCode delta))
      (tAdd addedBase (tAdd correctionBase newRem)))).
  {
    unfold correctionBase.
    exact (BProv_eq_congr_add_right Ax_s G addedBase _ _ hDelta).
  }
  pose proof (BProv_eqSym Ax_s G _ _
    (BProv_Ax_s_add_assoc_terms G addedBase correctionBase newRem))
    as hregroup3.
  assert (hquotMul : BProv Ax_s G
    (pEq (tMul (tAdd inverseContribution correctionQuot) modulus)
      (tAdd addedBase correctionBase))).
  {
    unfold addedBase, correctionBase.
    apply BProv_Ax_s_add_mul_terms.
  }
  pose proof (BProv_eq_congr_add_left Ax_s G _ _ newRem
    (BProv_eqSym Ax_s G _ _ hquotMul)) as hquotCong.
  unfold inverseContribution.
  exact (BProv_eqTrans Ax_s G _ _ _ hcode
    (BProv_eqTrans Ax_s G _ _ _ hregroup1
      (BProv_eqTrans Ax_s G _ _ _ hcommCong
        (BProv_eqTrans Ax_s G _ _ _ hregroup2
          (BProv_eqTrans Ax_s G _ _ _ hdeltaCong
            (BProv_eqTrans Ax_s G _ _ _ hregroup3 hquotCong)))))).
Qed.

Lemma BProv_Ax_s_crtSuccessorCorrectionTerm :
  forall G oldCode modulusPred newRem,
  BProv Ax_s G
    (pEq
      (tAdd oldCode
        (crtSuccessorCorrectionTerm oldCode modulusPred newRem))
      (tAdd (tMul oldCode (tSucc modulusPred)) newRem)).
Proof.
  intros G oldCode modulusPred newRem.
  pose proof (BProv_eqSym Ax_s G _ _
    (BProv_Ax_s_add_assoc_terms G
      oldCode (tMul modulusPred oldCode) newRem)) as hassoc.
  pose proof (BProv_Ax_s_mul_comm_terms G modulusPred oldCode)
    as hmulComm.
  pose proof (BProv_eq_congr_add_right Ax_s G oldCode _ _ hmulComm)
    as hinnerComm1.
  pose proof (BProv_Ax_s_add_comm_terms G
    oldCode (tMul oldCode modulusPred)) as hinnerComm2.
  assert (hmulSucc : BProv Ax_s G
    (pEq (tMul oldCode (tSucc modulusPred))
      (tAdd (tMul oldCode modulusPred) oldCode))).
  {
    apply BProv_Ax_s_mulSucc_terms.
  }
  assert (hinner : BProv Ax_s G
    (pEq (tAdd oldCode (tMul modulusPred oldCode))
      (tMul oldCode (tSucc modulusPred)))).
  {
    exact (BProv_eqTrans Ax_s G _ _ _ hinnerComm1
      (BProv_eqTrans Ax_s G _ _ _ hinnerComm2
        (BProv_eqSym Ax_s G _ _ hmulSucc))).
  }
  pose proof (BProv_eq_congr_add_left Ax_s G _ _ newRem hinner)
    as hinnerCong.
  unfold crtSuccessorCorrectionTerm.
  exact (BProv_eqTrans Ax_s G _ _ _ hassoc hinnerCong).
Qed.

Lemma BProv_Ax_s_remTermTermAt_crtExtend_successor_new :
  forall G oldCode product inverse modulusPred inverseQuot newRem,
  BProv Ax_s G
    (pEq (tMul product inverse)
      (tSucc (tMul (tSucc modulusPred) inverseQuot))) ->
  BProv Ax_s G (ltTermAt newRem (tSucc modulusPred)) ->
  BProv Ax_s G
    (remTermTermAt newRem
      (crtExtendCodeTerm oldCode product inverse
        (crtSuccessorCorrectionTerm oldCode modulusPred newRem))
      (tSucc modulusPred)).
Proof.
  intros G oldCode product inverse modulusPred inverseQuot newRem
    hInverse hBound.
  set (delta := crtSuccessorCorrectionTerm oldCode modulusPred newRem).
  set (quotient := tAdd (tMul inverseQuot delta) oldCode).
  assert (hDelta : BProv Ax_s G
    (pEq (tAdd oldCode delta)
      (tAdd (tMul oldCode (tSucc modulusPred)) newRem))).
  {
    unfold delta.
    apply BProv_Ax_s_crtSuccessorCorrectionTerm.
  }
  assert (hdecomp : BProv Ax_s G
    (pEq (crtExtendCodeTerm oldCode product inverse delta)
      (tAdd (tMul quotient (tSucc modulusPred)) newRem))).
  {
    unfold quotient.
    exact (BProv_Ax_s_crtExtendCodeTerm_new_decomposition_of_code
      G oldCode product inverse delta (tSucc modulusPred)
      inverseQuot oldCode newRem hInverse hDelta).
  }
  unfold delta.
  exact (BProv_Ax_s_remTermTermAt_of_eq_add_mul_terms
    G newRem
    (crtExtendCodeTerm oldCode product inverse
      (crtSuccessorCorrectionTerm oldCode modulusPred newRem))
    (tSucc modulusPred) quotient hBound hdecomp).
Qed.

Lemma BProv_Ax_s_betaTermTermAt_crtExtend_successor_new :
  forall G oldCode product inverse step index inverseQuot newOut,
  BProv Ax_s G
    (pEq (tMul product inverse)
      (tSucc (tMul (betaModTermTerm step index) inverseQuot))) ->
  BProv Ax_s G
    (ltTermAt newOut (betaModTermTerm step index)) ->
  BProv Ax_s G
    (betaTermTermAt newOut
      (crtExtendCodeTerm oldCode product inverse
        (crtSuccessorCorrectionTerm oldCode
          (tMul (tSucc index) step) newOut))
      step index).
Proof.
  intros G oldCode product inverse step index inverseQuot newOut
    hInverse hBound.
  set (modulusPred := tMul (tSucc index) step).
  set (delta := crtSuccessorCorrectionTerm oldCode modulusPred newOut).
  assert (hrem : BProv Ax_s G
    (remTermTermAt newOut
      (crtExtendCodeTerm oldCode product inverse delta)
      (tSucc modulusPred))).
  {
    apply (BProv_Ax_s_remTermTermAt_crtExtend_successor_new
      G oldCode product inverse modulusPred inverseQuot newOut).
    - unfold modulusPred, betaModTermTerm in hInverse.
      exact hInverse.
    - unfold modulusPred, betaModTermTerm in hBound.
      exact hBound.
  }
  unfold delta, modulusPred.
  apply (BProv_Ax_s_betaTermTermAt_of_rem
    G newOut
    (crtExtendCodeTerm oldCode product inverse
      (crtSuccessorCorrectionTerm oldCode
        (tMul (tSucc index) step) newOut))
    step index (betaModTermTerm step index)).
  - apply BProv_eqRefl.
  - unfold betaModTermTerm.
    exact hrem.
Qed.

Lemma BProv_Ax_s_betaCodeExtensionTermAt_crtExtend :
  forall G oldCode product inverse step target inverseQuot newOut,
  BProv Ax_s G (betaPrefixDividesTermAt step target product) ->
  BProv Ax_s G
    (pEq (tMul product inverse)
      (tSucc (tMul (betaModTermTerm step target) inverseQuot))) ->
  BProv Ax_s G
    (ltTermAt newOut (betaModTermTerm step target)) ->
  BProv Ax_s G
    (betaCodeExtensionTermAt oldCode step target newOut
      (crtExtendCodeTerm oldCode product inverse
        (crtSuccessorCorrectionTerm oldCode
          (tMul (tSucc target) step) newOut))).
Proof.
  intros G oldCode product inverse step target inverseQuot newOut
    hprefix hInverse hBound.
  set (delta := crtSuccessorCorrectionTerm oldCode
    (tMul (tSucc target) step) newOut).
  pose proof (BProv_Ax_s_betaPrefixAgreementTermAt_crtExtend
    G oldCode product inverse delta step target hprefix) as hagreement.
  pose proof (BProv_Ax_s_betaTermTermAt_crtExtend_successor_new
    G oldCode product inverse step target inverseQuot newOut
    hInverse hBound) as htarget.
  unfold betaCodeExtensionTermAt, delta.
  exact (BProv_andI Ax_s G _ _ hagreement htarget).
Qed.

Lemma BProv_Ax_s_betaCodeExtensionExistsTermAt_of_term :
  forall G oldCode step target newOut newCode,
  BProv Ax_s G
    (betaCodeExtensionTermAt oldCode step target newOut newCode) ->
  BProv Ax_s G
    (betaCodeExtensionExistsTermAt oldCode step target newOut).
Proof.
  intros G oldCode step target newOut newCode hext.
  unfold betaCodeExtensionExistsTermAt.
  apply (BProv_exI Ax_s G _ newCode).
  rewrite subst_betaCodeExtensionTermAt.
  simpl.
  repeat rewrite term_subst_instTerm_rename_succ.
  exact hext.
Qed.

Lemma BProv_Ax_s_betaCodeExtensionExistsTermAt_elim_opened :
  forall G oldCode step target newOut goal,
  BProv Ax_s
    (betaCodeExtensionExistsTermAtBody
        oldCode step target newOut ::
      map (rename S) G)
    (rename S goal) ->
  BProv Ax_s G
    (betaCodeExtensionExistsTermAt oldCode step target newOut) ->
  BProv Ax_s G goal.
Proof.
  intros G oldCode step target newOut goal hopened hex.
  unfold betaCodeExtensionExistsTermAt in hex.
  unfold betaCodeExtensionExistsTermAtBody in hopened.
  exact (BProv_exE_of_sentences Ax_s G _ goal
    sentence_ax_s hex hopened).
Qed.

Lemma subst_betaCodeExtensionExistsTermAt :
  forall sigma oldCode step target newOut,
  subst sigma
      (betaCodeExtensionExistsTermAt oldCode step target newOut) =
    betaCodeExtensionExistsTermAt
      (Term.subst sigma oldCode)
      (Term.subst sigma step)
      (Term.subst sigma target)
      (Term.subst sigma newOut).
Proof.
  intros sigma oldCode step target newOut.
  unfold betaCodeExtensionExistsTermAt.
  cbn [subst].
  rewrite subst_betaCodeExtensionTermAt.
  simpl.
  repeat rewrite Term.subst_rename_succ_up.
  reflexivity.
Qed.

Lemma rename_betaCodeExtensionExistsTermAt :
  forall r oldCode step target newOut,
  rename r
      (betaCodeExtensionExistsTermAt oldCode step target newOut) =
    betaCodeExtensionExistsTermAt
      (Term.rename r oldCode)
      (Term.rename r step)
      (Term.rename r target)
      (Term.rename r newOut).
Proof.
  intros r oldCode step target newOut.
  rename_from_subst subst_betaCodeExtensionExistsTermAt.
Qed.

Lemma rename_succ_twice_betaPrefixDividesTermAt :
  forall step bound product,
  rename S (rename S (betaPrefixDividesTermAt step bound product)) =
    betaPrefixDividesTermAt
      (Term.rename (fun n => n + 2) step)
      (Term.rename (fun n => n + 2) bound)
      (Term.rename (fun n => n + 2) product).
Proof.
  intros step bound product.
  exact (PA.Formula.rename_succ_twice_betaPrefixDividesTermAt
    step bound product).
Qed.

Lemma rename_succ_twice_betaCodeExtensionExistsTermAt :
  forall oldCode step target newOut,
  rename S (rename S
      (betaCodeExtensionExistsTermAt oldCode step target newOut)) =
    betaCodeExtensionExistsTermAt
      (Term.rename (fun n => n + 2) oldCode)
      (Term.rename (fun n => n + 2) step)
      (Term.rename (fun n => n + 2) target)
      (Term.rename (fun n => n + 2) newOut).
Proof.
  intros oldCode step target newOut.
  rewrite !rename_betaCodeExtensionExistsTermAt.
  repeat rewrite term_rename_succ_twice_add_two.
  reflexivity.
Qed.

Lemma BProv_Ax_s_betaCodeExtensionExistsTermAt_of_prefix_inverse :
  forall G oldCode product step target newOut,
  BProv Ax_s G (betaPrefixDividesTermAt step target product) ->
  BProv Ax_s G
    (crtInverseExistsTermAt product (betaModTermTerm step target)) ->
  BProv Ax_s G
    (ltTermAt newOut (betaModTermTerm step target)) ->
  BProv Ax_s G
    (betaCodeExtensionExistsTermAt oldCode step target newOut).
Proof.
  intros G oldCode product step target newOut
    hprefix hinverse hnewBound.
  set (modulus := betaModTermTerm step target).
  set (goal := betaCodeExtensionExistsTermAt oldCode step target newOut).
  apply (BProv_Ax_s_crtInverseExistsTermAt_elim_opened
    G product modulus goal); [|unfold modulus; exact hinverse].
  set (quotEx := crtInverseExistsTermAtQuotEx product modulus).
  set (certBody := crtInverseExistsTermAtBody product modulus).
  set (D := crtInverseExistsTermAtOpenedContext product modulus G).
  set (oldCode2 := Term.rename (fun n => n + 2) oldCode).
  set (product2 := Term.rename (fun n => n + 2) product).
  set (step2 := Term.rename (fun n => n + 2) step).
  set (target2 := Term.rename (fun n => n + 2) target).
  set (newOut2 := Term.rename (fun n => n + 2) newOut).
  set (modulus2 := Term.rename (fun n => n + 2) modulus).
  assert (hmodulus2 : modulus2 = betaModTermTerm step2 target2).
  {
    unfold modulus2, modulus, step2, target2.
    apply term_rename_betaModTermTerm.
  }
  assert (hcert : BProv Ax_s D
    (crtInverseTermAt product2 modulus2 (tVar 1) (tVar 0))).
  {
    apply BProv_ass.
    unfold D, crtInverseExistsTermAtOpenedContext,
      certBody, crtInverseExistsTermAtBody,
      product2, modulus2.
    simpl. left. reflexivity.
  }
  pose proof (BProv_lift_two_contexts_of_sentences
    Ax_s sentence_ax_s G quotEx certBody _ hprefix) as hprefixD.
  change (BProv Ax_s D
    (rename S (rename S
      (betaPrefixDividesTermAt step target product)))) in hprefixD.
  rewrite rename_succ_twice_betaPrefixDividesTermAt in hprefixD.
  change (BProv Ax_s D
    (betaPrefixDividesTermAt step2 target2 product2)) in hprefixD.

  pose proof (BProv_lift_two_contexts_of_sentences
    Ax_s sentence_ax_s G quotEx certBody _ hnewBound) as hboundD.
  change (BProv Ax_s D
    (rename S (rename S (ltTermAt newOut modulus)))) in hboundD.
  rewrite rename_succ_twice_ltTermAt in hboundD.
  change (BProv Ax_s D (ltTermAt newOut2 modulus2)) in hboundD.

  assert (hcert' : BProv Ax_s D
    (crtInverseTermAt product2 (betaModTermTerm step2 target2)
      (tVar 1) (tVar 0))).
  { rewrite <- hmodulus2. exact hcert. }
  assert (hbound' : BProv Ax_s D
    (ltTermAt newOut2 (betaModTermTerm step2 target2))).
  { rewrite <- hmodulus2. exact hboundD. }
  unfold crtInverseTermAt in hcert'.
  pose proof (BProv_Ax_s_betaCodeExtensionTermAt_crtExtend
    D oldCode2 product2 (tVar 1) step2 target2 (tVar 0) newOut2
    hprefixD hcert' hbound') as hext.
  pose proof (BProv_Ax_s_betaCodeExtensionExistsTermAt_of_term
    D oldCode2 step2 target2 newOut2 _ hext) as hex.
  unfold goal.
  rewrite rename_succ_twice_betaCodeExtensionExistsTermAt.
  exact hex.
Qed.
