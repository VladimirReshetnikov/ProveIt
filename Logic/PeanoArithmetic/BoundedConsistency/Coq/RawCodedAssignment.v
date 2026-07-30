(**
  Beta-coded variable assignments in arbitrary raw models of PA.

  A Goedel-beta sequence is represented by two carrier elements: its residue
  code and its common step.  Keeping both components explicit is important in
  a nonstandard model: this module never decodes a carrier element into a
  Rocq [nat] or list.  Instead, lookup, finite-prefix definedness, and binder
  extension are expressed by genuine first-order PA formulae.

  The intended use is a future arithmetized term and partial-truth evaluator.
  Extending a de Bruijn environment with [head] puts [head] at index zero and
  shifts every source entry below the model-internal bound to its successor.
  PAHF's CRT development proves that such an extension exists even when the
  bound is nonstandard.  The results below package that arithmetic theorem
  behind an assignment-specific interface and prove its exact raw semantics.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFAdjoinTotal.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.

Import ListNotations.
Import PA PA.Term PA.Formula.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.

Module PABoundedRawCodedAssignment.

(** ------------------------------------------------------------------
    Raw semantic interface. *)

Definition RawCodedAssignmentLookup (M : RawPAModel)
    (code step index value : M) : Prop :=
  RawBetaEntry M value code step index.

Definition RawCodedAssignmentDefinedThrough (M : RawPAModel)
    (code step bound : M) : Prop :=
  forall index,
    rawLt M index bound ->
    exists value, RawCodedAssignmentLookup M code step index value.

(** [target] is [head :: source] through the strict source prefix [bound].
    Values outside that prefix are deliberately unconstrained. *)
Definition RawCodedAssignmentPrepend (M : RawPAModel)
    (sourceCode sourceStep head bound targetCode targetStep : M) : Prop :=
  RawCodedAssignmentLookup M targetCode targetStep (raw_zero M) head /\
  forall index,
    rawLt M index bound ->
    forall value,
      RawCodedAssignmentLookup M sourceCode sourceStep index value ->
      RawCodedAssignmentLookup M targetCode targetStep
        (raw_succ M index) value.

Arguments RawCodedAssignmentLookup
  M code step index value : clear implicits.
Arguments RawCodedAssignmentDefinedThrough
  M code step bound : clear implicits.
Arguments RawCodedAssignmentPrepend
  M sourceCode sourceStep head bound targetCode targetStep : clear implicits.

(** ------------------------------------------------------------------
    Object-language formulae.

    These are term-parametric formula constructors, so callers can place the
    assignment components in any surrounding environment without introducing
    a second coding convention. *)

Definition codedAssignmentLookupTermAt
    (code step index value : PA.term) : PA.formula :=
  PA.Formula.betaTermTermAt value code step index.

Definition codedAssignmentDefinedThroughTermAt
    (code step bound : PA.term) : PA.formula :=
  betaEntryExistsPrefixTermAt code step bound.

Definition codedAssignmentPrependTermAt
    (sourceCode sourceStep head bound targetCode targetStep : PA.term)
    : PA.formula :=
  PA.Formula.betaPrependPrefixTermAt
    sourceCode sourceStep head targetCode targetStep bound.

Definition codedAssignmentPrependExistsTermAt
    (sourceCode sourceStep head bound : PA.term) : PA.formula :=
  PA.Formula.betaPrependExistsTermAt
    sourceCode sourceStep head bound.

(** Canonical slot layout for the existential binder-extension formula:
    source code, source step, new head, and source bound. *)
Definition codedAssignmentPrependExistsFormula : PA.formula :=
  codedAssignmentPrependExistsTermAt
    (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3).

Definition rawCodedAssignmentPrependInputEnv (M : RawPAModel)
    (sourceCode sourceStep head bound : M) (tail : nat -> M) : nat -> M :=
  scons M sourceCode
    (scons M sourceStep (scons M head (scons M bound tail))).

Arguments rawCodedAssignmentPrependInputEnv
  M sourceCode sourceStep head bound tail : clear implicits.

(** ------------------------------------------------------------------
    Exact semantics in every raw arithmetic structure. *)

Lemma raw_sat_codedAssignmentLookupTermAt_iff :
  forall (M : RawPAModel) code step index value (e : nat -> M),
  raw_formula_sat M e
      (codedAssignmentLookupTermAt code step index value) <->
  RawCodedAssignmentLookup M
    (raw_term_eval M e code) (raw_term_eval M e step)
    (raw_term_eval M e index) (raw_term_eval M e value).
Proof.
  intros M code step index value e.
  unfold codedAssignmentLookupTermAt, RawCodedAssignmentLookup.
  rewrite raw_sat_betaTermTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_codedAssignmentDefinedThroughTermAt_iff :
  forall (M : RawPAModel) code step bound (e : nat -> M),
  raw_formula_sat M e
      (codedAssignmentDefinedThroughTermAt code step bound) <->
  RawCodedAssignmentDefinedThrough M
    (raw_term_eval M e code) (raw_term_eval M e step)
    (raw_term_eval M e bound).
Proof.
  intros M code step bound e.
  unfold codedAssignmentDefinedThroughTermAt,
    RawCodedAssignmentDefinedThrough, RawCodedAssignmentLookup.
  rewrite raw_sat_betaEntryExistsPrefixTermAt_iff.
  reflexivity.
Qed.

(** The explicit prepend relation is kept separate from its existential
    closure.  A later truth formula can therefore bind the new code and step
    and immediately use them to evaluate a quantified subformula. *)
Lemma raw_sat_codedAssignmentPrependTermAt_iff :
  forall (M : RawPAModel)
      sourceCode sourceStep head bound targetCode targetStep
      (e : nat -> M),
  raw_formula_sat M e
      (codedAssignmentPrependTermAt
        sourceCode sourceStep head bound targetCode targetStep) <->
  RawCodedAssignmentPrepend M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e head) (raw_term_eval M e bound)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep).
Proof.
  intros M sourceCode sourceStep head bound targetCode targetStep e.
  unfold codedAssignmentPrependTermAt,
    PA.Formula.betaPrependPrefixTermAt,
    PA.Formula.betaUnshiftPrefixTermAt,
    RawCodedAssignmentPrepend, RawCodedAssignmentLookup.
  cbn [raw_formula_sat].
  split.
  - intros [hhead hshift]. split.
    + apply (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)) in hhead.
      exact hhead.
    + intros index hlt value hsource.
      assert (hltSat : raw_formula_sat M (scons M index e)
          (PA.Formula.ltTermAt
            (PA.tVar 0) (PA.Term.rename S bound))).
      {
        apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
        rewrite raw_term_eval_rename_succ.
        cbn [raw_term_eval scons].
        exact hlt.
      }
      assert (hsourceSat : raw_formula_sat M
          (scons M value (scons M index e))
          (PA.Formula.betaTermTermAt (PA.tVar 0)
            (PA.Term.rename (fun n => n + 2) sourceCode)
            (PA.Term.rename (fun n => n + 2) sourceStep)
            (PA.tVar 1))).
      {
        apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
        repeat rewrite raw_term_eval_rename_two_scons.
        cbn [raw_term_eval scons].
        exact hsource.
      }
      pose proof (hshift index hltSat value hsourceSat) as htargetSat.
      apply (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _))
        in htargetSat.
      repeat rewrite raw_term_eval_rename_two_scons in htargetSat.
      cbn [raw_term_eval scons] in htargetSat.
      exact htargetSat.
  - intros [hhead hshift]. split.
    + apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
      exact hhead.
    + intros index hltSat value hsourceSat.
      pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hlt.
      rewrite raw_term_eval_rename_succ in hlt.
      cbn [raw_term_eval scons] in hlt.
      pose proof (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)
        hsourceSat) as hsource.
      repeat rewrite raw_term_eval_rename_two_scons in hsource.
      cbn [raw_term_eval scons] in hsource.
      pose proof (hshift index hlt value hsource) as htarget.
      apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
      repeat rewrite raw_term_eval_rename_two_scons.
      cbn [raw_term_eval scons].
      exact htarget.
Qed.

Lemma raw_sat_codedAssignmentPrependExistsTermAt_iff :
  forall (M : RawPAModel) sourceCode sourceStep head bound
      (e : nat -> M),
  raw_formula_sat M e
      (codedAssignmentPrependExistsTermAt
        sourceCode sourceStep head bound) <->
  exists targetCode targetStep : M,
    RawCodedAssignmentPrepend M
      (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
      (raw_term_eval M e head) (raw_term_eval M e bound)
      targetCode targetStep.
Proof.
  intros M sourceCode sourceStep head bound e.
  unfold codedAssignmentPrependExistsTermAt.
  rewrite raw_sat_betaPrependExistsTermAt_iff.
  unfold RawCodedAssignmentPrepend, RawCodedAssignmentLookup.
  split.
  - intros [targetStep [targetCode htarget]].
    exists targetCode, targetStep. exact htarget.
  - intros [targetCode [targetStep htarget]].
    exists targetStep, targetCode. exact htarget.
Qed.

Lemma raw_sat_codedAssignmentPrependExistsFormula_iff :
  forall (M : RawPAModel) sourceCode sourceStep head bound
      (tail : nat -> M),
  raw_formula_sat M
      (rawCodedAssignmentPrependInputEnv M
        sourceCode sourceStep head bound tail)
      codedAssignmentPrependExistsFormula <->
  exists targetCode targetStep : M,
    RawCodedAssignmentPrepend M
      sourceCode sourceStep head bound targetCode targetStep.
Proof.
  intros M sourceCode sourceStep head bound tail.
  unfold codedAssignmentPrependExistsFormula.
  rewrite raw_sat_codedAssignmentPrependExistsTermAt_iff.
  unfold rawCodedAssignmentPrependInputEnv.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** Instantiate prefix-definedness at any represented index below its bound.
    This is the proof-theoretic counterpart of applying
    [RawCodedAssignmentDefinedThrough] to one index.  Keeping the result at
    the object-language [BProv] level lets later proof-code compilers reuse
    it under arbitrary quoted contexts. *)
Theorem BProv_Ax_s_codedAssignmentDefinedThrough_entry_of_ltTerm :
  forall G code step bound idx,
  PA.Formula.BProv PA.Formula.Ax_s G
    (codedAssignmentDefinedThroughTermAt code step bound) ->
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.Formula.ltTermAt idx bound) ->
  PA.Formula.BProv PA.Formula.Ax_s G
    (betaEntryExistsTermAt code step idx).
Proof.
  intros G code step bound idx hentries hlt.
  pose proof (BProv_allE Ax_s G _ idx hentries) as himp.
  unfold codedAssignmentDefinedThroughTermAt,
    betaEntryExistsPrefixTermAt in hentries.
  cbn [subst] in himp.
  rewrite subst_ltTermAt in himp.
  unfold betaEntryExistsTermAt in himp.
  cbn [subst] in himp.
  rewrite subst_betaTermTermAt in himp.
  simpl in himp.
  rewrite term_subst_instTerm_rename_succ in himp.
  repeat rewrite Term.rename_comp in himp.
  simpl in himp.
  repeat rewrite term_subst_upSubst_instTerm_rename_two_succ in himp.
  unfold betaEntryExistsTermAt.
  exact (BProv_mp Ax_s G _ _ himp hlt).
Qed.

(** Closed implication form, suited to compilation as one reusable PA proof
    followed by two represented [Imp-E] nodes in an arbitrary local
    context. *)
Corollary BProv_Ax_s_codedAssignmentDefinedThrough_entry_imp :
  forall code step bound idx,
  PA.Formula.BProv PA.Formula.Ax_s []
    (pImp (codedAssignmentDefinedThroughTermAt code step bound)
      (pImp (PA.Formula.ltTermAt idx bound)
        (betaEntryExistsTermAt code step idx))).
Proof.
  intros code step bound idx.
  apply BProv_impI.
  apply BProv_impI.
  assert (hdefined : BProv Ax_s
      (PA.Formula.ltTermAt idx bound ::
        codedAssignmentDefinedThroughTermAt code step bound :: [])
      (codedAssignmentDefinedThroughTermAt code step bound)).
  { apply BProv_ass. simpl. right. left. reflexivity. }
  assert (hlt : BProv Ax_s
      (PA.Formula.ltTermAt idx bound ::
        codedAssignmentDefinedThroughTermAt code step bound :: [])
      (PA.Formula.ltTermAt idx bound)).
  { apply BProv_ass. simpl. left. reflexivity. }
  exact
    (BProv_Ax_s_codedAssignmentDefinedThrough_entry_of_ltTerm
      _ code step bound idx hdefined hlt).
Qed.

(** ------------------------------------------------------------------
    Functionality and the exact de Bruijn lookup equations. *)

Theorem raw_codedAssignmentLookup_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code step index left right : M,
  RawCodedAssignmentLookup M code step index left ->
  RawCodedAssignmentLookup M code step index right ->
  left = right.
Proof.
  intros M hPA code step index left right hleft hright.
  unfold RawCodedAssignmentLookup in *.
  exact (rawBetaEntry_functional M hPA
    left right code step index hleft hright).
Qed.

Corollary raw_sat_codedAssignmentLookupTermAt_functional :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code step index left right (e : nat -> M),
  raw_formula_sat M e
    (codedAssignmentLookupTermAt code step index left) ->
  raw_formula_sat M e
    (codedAssignmentLookupTermAt code step index right) ->
  raw_term_eval M e left = raw_term_eval M e right.
Proof.
  intros M hPA code step index left right e hleft hright.
  apply (raw_codedAssignmentLookup_functional M hPA
    (raw_term_eval M e code) (raw_term_eval M e step)
    (raw_term_eval M e index)).
  - apply (proj1 (raw_sat_codedAssignmentLookupTermAt_iff
      M code step index left e)). exact hleft.
  - apply (proj1 (raw_sat_codedAssignmentLookupTermAt_iff
      M code step index right e)). exact hright.
Qed.

Theorem raw_codedAssignment_defined_unique :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall code step bound : M,
  RawCodedAssignmentDefinedThrough M code step bound ->
  forall index,
    rawLt M index bound ->
    exists! value, RawCodedAssignmentLookup M code step index value.
Proof.
  intros M hPA code step bound hdefined index hindex.
  destruct (hdefined index hindex) as [value hvalue].
  exists value. split; [exact hvalue |].
  intros other hother.
  exact (raw_codedAssignmentLookup_functional M hPA
    code step index value other hvalue hother).
Qed.

Corollary raw_codedAssignmentPrepend_head :
  forall (M : RawPAModel) sourceCode sourceStep head bound
      targetCode targetStep,
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound targetCode targetStep ->
  RawCodedAssignmentLookup M targetCode targetStep (raw_zero M) head.
Proof.
  intros M sourceCode sourceStep head bound targetCode targetStep h.
  exact (proj1 h).
Qed.

Corollary raw_codedAssignmentPrepend_tail :
  forall (M : RawPAModel) sourceCode sourceStep head bound
      targetCode targetStep index value,
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound targetCode targetStep ->
  rawLt M index bound ->
  RawCodedAssignmentLookup M sourceCode sourceStep index value ->
  RawCodedAssignmentLookup M targetCode targetStep
    (raw_succ M index) value.
Proof.
  intros M sourceCode sourceStep head bound targetCode targetStep
    index value hprepend hindex hlookup.
  exact ((proj2 hprepend) index hindex value hlookup).
Qed.

Theorem raw_codedAssignmentPrepend_lookup_zero_iff :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceCode sourceStep head bound targetCode targetStep value,
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound targetCode targetStep ->
  (RawCodedAssignmentLookup M targetCode targetStep (raw_zero M) value <->
    value = head).
Proof.
  intros M hPA sourceCode sourceStep head bound targetCode targetStep
    value hprepend.
  split.
  - intro hvalue.
    exact (raw_codedAssignmentLookup_functional M hPA
      targetCode targetStep (raw_zero M) value head
      hvalue (proj1 hprepend)).
  - intro hvalue. subst value. exact (proj1 hprepend).
Qed.

Theorem raw_codedAssignmentPrepend_lookup_succ_iff :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceCode sourceStep head bound targetCode targetStep,
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound targetCode targetStep ->
  forall index,
  rawLt M index bound ->
  forall value,
  (RawCodedAssignmentLookup M targetCode targetStep
      (raw_succ M index) value <->
   RawCodedAssignmentLookup M sourceCode sourceStep index value).
Proof.
  intros M hPA sourceCode sourceStep head bound targetCode targetStep
    hdefined hprepend index hindex value.
  split.
  - intro htarget.
    destruct (hdefined index hindex) as [sourceValue hsource].
    pose proof ((proj2 hprepend) index hindex sourceValue hsource)
      as hshifted.
    assert (hvalue : value = sourceValue).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        targetCode targetStep (raw_succ M index)
        value sourceValue htarget hshifted).
    }
    subst value. exact hsource.
  - exact ((proj2 hprepend) index hindex value).
Qed.

(** ------------------------------------------------------------------
    Model-internal binder extension. *)

(** PA proves the existential prepend formula uniformly in all four terms.
    This is a small public alias for the much larger CRT development. *)
Theorem BProv_Ax_s_codedAssignmentPrependExistsTermAt :
  forall G sourceCode sourceStep head bound,
  PA.Formula.BProv PA.Formula.Ax_s G
    (codedAssignmentPrependExistsTermAt
      sourceCode sourceStep head bound).
Proof.
  intros G sourceCode sourceStep head bound.
  unfold codedAssignmentPrependExistsTermAt.
  exact (BProv_Ax_s_betaPrependExistsTermAt
    G sourceCode sourceStep head bound).
Qed.

(** This is the key nonstandard existence theorem.  [bound] is an arbitrary
    element of [M], not an external natural numeral. *)
Theorem raw_codedAssignmentPrepend_exists :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceCode sourceStep head bound : M,
  exists targetCode targetStep : M,
    RawCodedAssignmentPrepend M
      sourceCode sourceStep head bound targetCode targetStep.
Proof.
  intros M hPA sourceCode sourceStep head bound.
  set (tail := fun _ : nat => raw_zero M).
  set (e := rawCodedAssignmentPrependInputEnv M
    sourceCode sourceStep head bound tail).
  pose proof (raw_sat_of_BProv_axs M
    codedAssignmentPrependExistsFormula hPA
    (BProv_Ax_s_codedAssignmentPrependExistsTermAt []
      (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3)) e) as hsat.
  apply (proj1 (raw_sat_codedAssignmentPrependExistsFormula_iff
    M sourceCode sourceStep head bound tail)).
  unfold e.
  exact hsat.
Qed.

(** Two elementary PA consequences used to turn the exact head/shift
    equations into prefix-definedness at [succ bound]. *)
Lemma raw_assignment_zero_or_successor :
  forall (M : RawPAModel), RawPASatisfies M -> forall x : M,
  x = raw_zero M \/ exists predecessor : M,
    x = raw_succ M predecessor.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (PA.Formula.BProv_Ax_s_zeroOrSuccPredAt [] 0) e) as hcases.
  change (x = raw_zero M \/ exists predecessor : M,
    x = raw_succ M predecessor) in hcases.
  exact hcases.
Qed.

Lemma raw_assignment_lt_self_succ :
  forall (M : RawPAModel), RawPASatisfies M -> forall x : M,
  rawLt M x (raw_succ M x).
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (PA.Formula.BProv_Ax_s_leTermAt_refl [] (PA.tVar 0)) e) as hle.
  change (rawLe M x x) in hle.
  exact (raw_lt_succ_of_le M hPA x x hle).
Qed.

Lemma raw_assignment_lt_trans :
  forall (M : RawPAModel), RawPASatisfies M -> forall x y z : M,
  rawLt M x y -> rawLt M y z -> rawLt M x z.
Proof.
  intros M hPA x y z hxy hyz.
  set (xy := PA.Formula.ltAt 0 1).
  set (yz := PA.Formula.ltAt 1 2).
  set (G := [xy; yz] : list PA.formula).
  assert (hassXY : PA.Formula.BProv PA.Formula.Ax_s G xy).
  { apply PA.Formula.BProv_ass. unfold G. simpl. left. reflexivity. }
  assert (hassYZ : PA.Formula.BProv PA.Formula.Ax_s G yz).
  {
    apply PA.Formula.BProv_ass. unfold G. simpl. right. left. reflexivity.
  }
  pose proof (PA.Formula.BProv_Ax_s_ltAt_trans
    G 0 1 2 hassXY hassYZ) as htrans.
  set (e := scons M x
    (scons M y (scons M z (fun _ : nat => raw_zero M)))).
  assert (hxySat : raw_formula_sat M e xy).
  {
    unfold xy, PA.Formula.ltAt, rawLt.
    unfold e. cbn [raw_formula_sat raw_term_eval scons].
    exact hxy.
  }
  assert (hyzSat : raw_formula_sat M e yz).
  {
    unfold yz, PA.Formula.ltAt, rawLt.
    unfold e. cbn [raw_formula_sat raw_term_eval scons].
    exact hyz.
  }
  pose proof (raw_sat_of_BProv_axs_context M G _ hPA htrans e)
    as hsound.
  assert (hsat : raw_formula_sat M e (PA.Formula.ltAt 0 2)).
  {
    apply hsound. intros g hg.
    unfold G in hg. simpl in hg.
    destruct hg as [hg | [hg | []]]; subst g; assumption.
  }
  unfold PA.Formula.ltAt, rawLt in hsat.
  unfold e in hsat. cbn [raw_formula_sat raw_term_eval scons] in hsat.
  exact hsat.
Qed.

(** A prepend certificate through a large proof-wide carrier bound can be
    restricted to any smaller formula bound.  The head row is unchanged;
    only the tail prefix is weakened. *)
Theorem raw_codedAssignmentPrepend_restrict :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceCode sourceStep head smallBound largeBound
      targetCode targetStep,
  rawLt M smallBound largeBound ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head largeBound targetCode targetStep ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head smallBound targetCode targetStep.
Proof.
  intros M hPA sourceCode sourceStep head smallBound largeBound
    targetCode targetStep hsmall hprepend.
  split; [exact (proj1 hprepend) |].
  intros index hindex value hlookup.
  exact ((proj2 hprepend) index
    (raw_assignment_lt_trans M hPA index smallBound largeBound
      hindex hsmall)
    value hlookup).
Qed.

Theorem raw_codedAssignmentPrepend_definedThrough :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceCode sourceStep head bound targetCode targetStep,
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound targetCode targetStep ->
  RawCodedAssignmentDefinedThrough M targetCode targetStep
    (raw_succ M bound).
Proof.
  intros M hPA sourceCode sourceStep head bound targetCode targetStep
    hdefined hprepend index hindex.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [hzero | [predecessor hsucc]].
  - subst index. exists head. exact (proj1 hprepend).
  - subst index.
    assert (hpredSelf : rawLt M predecessor (raw_succ M predecessor)).
    { exact (raw_assignment_lt_self_succ M hPA predecessor). }
    assert (hpredBound : rawLt M predecessor bound).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M predecessor) bound hindex) as [hlt | heq].
      - exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) bound hpredSelf hlt).
      - rewrite <- heq. exact hpredSelf.
    }
    destruct (hdefined predecessor hpredBound) as [value hvalue].
    exists value.
    exact ((proj2 hprepend) predecessor hpredBound value hvalue).
Qed.

(** Binder extension through [bound] supplies one extra row, hence in
    particular remains defined through the original common bound. *)
Corollary raw_codedAssignmentPrepend_target_definedThrough_bound :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceCode sourceStep head bound targetCode targetStep,
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound targetCode targetStep ->
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound.
Proof.
  intros M hPA sourceCode sourceStep head bound targetCode targetStep
    hdefined hprepend index hindex.
  pose proof (raw_codedAssignmentPrepend_definedThrough M hPA
    sourceCode sourceStep head bound targetCode targetStep
    hdefined hprepend) as htarget.
  exact (htarget index
    (raw_assignment_lt_trans M hPA index bound (raw_succ M bound)
      hindex (raw_assignment_lt_self_succ M hPA bound))).
Qed.

Theorem raw_codedAssignmentPrepend_defined_exists :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall sourceCode sourceStep head bound,
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound ->
  exists targetCode targetStep,
    RawCodedAssignmentPrepend M
      sourceCode sourceStep head bound targetCode targetStep /\
    RawCodedAssignmentDefinedThrough M targetCode targetStep
      (raw_succ M bound).
Proof.
  intros M hPA sourceCode sourceStep head bound hdefined.
  destruct (raw_codedAssignmentPrepend_exists M hPA
    sourceCode sourceStep head bound) as [targetCode [targetStep hprepend]].
  exists targetCode, targetStep. split; [exact hprepend |].
  exact (raw_codedAssignmentPrepend_definedThrough M hPA
    sourceCode sourceStep head bound targetCode targetStep
    hdefined hprepend).
Qed.

(** A convenient empty environment.  No standardness of the zero bound is
    used; PA itself proves that nothing is strictly below zero. *)
Corollary raw_codedAssignment_empty_defined :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedAssignmentDefinedThrough M
    (raw_zero M) (raw_zero M) (raw_zero M).
Proof.
  intros M hPA index hindex.
  exfalso.
  exact (raw_not_lt_zero M hPA index hindex).
Qed.

End PABoundedRawCodedAssignment.
