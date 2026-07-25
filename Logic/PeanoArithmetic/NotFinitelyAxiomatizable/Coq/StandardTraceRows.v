(** Semantic normalization of genuine evaluator rows at standard codes. *)

From Stdlib Require Import List Arith Lia Classical ClassicalEpsilon.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction
  FiniteSkolemHull CanonicalSelector CanonicalSelectorPA
  SkolemProgramCode FiniteBetaCoding ProgramTrace TotalProgramRows
  EvaluatorCutContract.

Import ListNotations.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PASkolemProgramCode.
Import PAFiniteBetaCoding.
Import PAProgramTrace.
Import PATotalProgramRows.
Import PAEvaluatorCutContract.

Module PAStandardTraceRows.

(** Standard arithmetic normalization is carried out in the ambient PA
    model and then reflected into the (not necessarily PA) Skolem hull. *)
Lemma raw_add_numeral_values : forall (M : RawPAModel),
  RawPASatisfies M -> forall m n,
  raw_add M (rawNumeralValue M m) (rawNumeralValue M n) =
    rawNumeralValue M (m + n).
Proof.
  intros M hPA m n.
  set (e := fun _ : nat => raw_zero M).
  pose proof (raw_eq_of_closed_bprov M hPA
    (PA.tAdd (PA.Term.numeral m) (PA.Term.numeral n))
    (PA.Term.numeral (m + n)) e
    (PA.Formula.BProv_Ax_s_addNumerals nil m n)) as h.
  cbn [raw_term_eval] in h.
  rewrite !raw_term_eval_numeral in h. exact h.
Qed.

Lemma raw_eval_pairTerm_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b e m n,
  raw_term_eval M e a = rawNumeralValue M m ->
  raw_term_eval M e b = rawNumeralValue M n ->
  raw_term_eval M e (pairTerm a b) =
    rawNumeralValue M (polynomialPair m n).
Proof.
  intros M hPA a b e m n ha hb.
  unfold pairTerm, polynomialPair. cbn [raw_term_eval].
  rewrite ha, hb.
  rewrite raw_add_numeral_values by exact hPA.
  rewrite raw_mul_numeral_values by exact hPA.
  rewrite raw_add_numeral_values by exact hPA.
  reflexivity.
Qed.

Lemma raw_eval_nodeTerm_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall tagTerm payloadTerm e tag payload,
  raw_term_eval M e tagTerm = rawNumeralValue M tag ->
  raw_term_eval M e payloadTerm = rawNumeralValue M payload ->
  raw_term_eval M e (nodeTerm tagTerm payloadTerm) =
    rawNumeralValue M (polynomialNode tag payload).
Proof.
  intros M hPA tagTerm payloadTerm e tag payload htag hpayload.
  unfold nodeTerm, polynomialNode. cbn [raw_term_eval rawNumeralValue].
  f_equal.
  exact (raw_eval_pairTerm_numerals M hPA tagTerm payloadTerm e
    tag payload htag hpayload).
Qed.

Lemma hull_eval_pairTerm_numerals : forall
    (M : RawPAModel) seed rank selector,
  RawPASatisfies M -> forall leftTerm rightTerm
    (e : nat -> skolemHullRawModel M seed rank selector) left right,
  raw_term_eval (skolemHullRawModel M seed rank selector) e leftTerm =
      rawNumeralValue (skolemHullRawModel M seed rank selector) left ->
  raw_term_eval (skolemHullRawModel M seed rank selector) e rightTerm =
      rawNumeralValue (skolemHullRawModel M seed rank selector) right ->
  raw_term_eval (skolemHullRawModel M seed rank selector) e
      (pairTerm leftTerm rightTerm) =
    rawNumeralValue (skolemHullRawModel M seed rank selector)
      (polynomialPair left right).
Proof.
  intros M seed rank selector hPA leftTerm rightTerm e left right
    hleft hright.
  apply (skolemHullVal_injective M seed rank selector).
  rewrite skolemHull_term_eval, skolemHull_rawNumeralValue_val.
  apply raw_eval_pairTerm_numerals; [exact hPA | |].
  - apply (f_equal (skolemHullVal M seed rank selector)) in hleft.
    rewrite skolemHull_term_eval, skolemHull_rawNumeralValue_val in hleft.
    exact hleft.
  - apply (f_equal (skolemHullVal M seed rank selector)) in hright.
    rewrite skolemHull_term_eval, skolemHull_rawNumeralValue_val in hright.
    exact hright.
Qed.

Lemma hull_eval_nodeTerm_numerals : forall
    (M : RawPAModel) seed rank selector,
  RawPASatisfies M -> forall tagTerm payloadTerm
    (e : nat -> skolemHullRawModel M seed rank selector) tag payload,
  raw_term_eval (skolemHullRawModel M seed rank selector) e tagTerm =
      rawNumeralValue (skolemHullRawModel M seed rank selector) tag ->
  raw_term_eval (skolemHullRawModel M seed rank selector) e payloadTerm =
      rawNumeralValue (skolemHullRawModel M seed rank selector) payload ->
  raw_term_eval (skolemHullRawModel M seed rank selector) e
      (nodeTerm tagTerm payloadTerm) =
    rawNumeralValue (skolemHullRawModel M seed rank selector)
      (polynomialNode tag payload).
Proof.
  intros M seed rank selector hPA tagTerm payloadTerm e tag payload
    htag hpayload.
  apply (skolemHullVal_injective M seed rank selector).
  rewrite skolemHull_term_eval, skolemHull_rawNumeralValue_val.
  apply raw_eval_nodeTerm_numerals; [exact hPA | |].
  - apply (f_equal (skolemHullVal M seed rank selector)) in htag.
    rewrite skolemHull_term_eval, skolemHull_rawNumeralValue_val in htag.
    exact htag.
  - apply (f_equal (skolemHullVal M seed rank selector)) in hpayload.
    rewrite skolemHull_term_eval, skolemHull_rawNumeralValue_val in hpayload.
    exact hpayload.
Qed.

Definition standardCodeList (start count : nat)
    (codes : nat -> nat) : list nat :=
  map codes (seq start count).

Lemma standardCodeList_zero : forall start codes,
  standardCodeList start 0 codes = [].
Proof. reflexivity. Qed.

Lemma standardCodeList_succ : forall start count codes,
  standardCodeList start (S count) codes =
    codes start :: standardCodeList (S start) count codes.
Proof.
  intros start count codes. unfold standardCodeList.
  rewrite <- cons_seq. simpl. reflexivity.
Qed.

Lemma hull_eval_argumentVectorFrom_numerals : forall
    (M : RawPAModel) seed rank selector,
  RawPASatisfies M -> forall start count
    (e : nat -> skolemHullRawModel M seed rank selector) codes,
  (forall i, start <= i < start + count ->
    raw_term_eval (skolemHullRawModel M seed rank selector) e
        (argumentCodeTerm i) =
      rawNumeralValue (skolemHullRawModel M seed rank selector) (codes i)) ->
  raw_term_eval (skolemHullRawModel M seed rank selector) e
      (argumentVectorTermFrom start count) =
    rawNumeralValue (skolemHullRawModel M seed rank selector)
      (argsCodeOfCodes (standardCodeList start count codes)).
Proof.
  intros M seed rank selector hPA start count. revert start.
  induction count as [|count IH]; intros start e codes hcodes.
  - cbn [argumentVectorTermFrom standardCodeList argsCodeOfCodes].
    apply hull_eval_nodeTerm_numerals; [exact hPA | |].
    + apply raw_term_eval_numeral.
    + apply raw_term_eval_numeral.
  - rewrite standardCodeList_succ.
    cbn [argumentVectorTermFrom argsCodeOfCodes].
    apply hull_eval_nodeTerm_numerals; [exact hPA | |].
    + apply raw_term_eval_numeral.
    + apply hull_eval_pairTerm_numerals.
      * exact hPA.
      * apply hcodes. lia.
      * apply IH. intros i hi. apply hcodes. lia.
Qed.

Corollary hull_eval_argumentVector_numerals : forall
    (M : RawPAModel) seed rank selector,
  RawPASatisfies M -> forall traceRank
    (e : nat -> skolemHullRawModel M seed rank selector) codes,
  (forall i, i < traceRank ->
    raw_term_eval (skolemHullRawModel M seed rank selector) e
        (argumentCodeTerm i) =
      rawNumeralValue (skolemHullRawModel M seed rank selector) (codes i)) ->
  raw_term_eval (skolemHullRawModel M seed rank selector) e
      (argumentVectorTerm traceRank) =
    rawNumeralValue (skolemHullRawModel M seed rank selector)
      (argsCodeOfCodes (standardCodeList 0 traceRank codes)).
Proof.
  intros M seed rank selector hPA traceRank e codes hcodes.
  unfold argumentVectorTerm.
  apply hull_eval_argumentVectorFrom_numerals; [exact hPA |].
  intros i hi. apply hcodes. lia.
Qed.

Lemma hull_eval_argumentVectorOfTermsFrom_numerals : forall
    (M : RawPAModel) seed rank selector,
  RawPASatisfies M -> forall start count
    (e : nat -> skolemHullRawModel M seed rank selector) codes terms,
  (forall i, start <= i < start + count ->
    raw_term_eval (skolemHullRawModel M seed rank selector) e (terms i) =
      rawNumeralValue (skolemHullRawModel M seed rank selector) (codes i)) ->
  raw_term_eval (skolemHullRawModel M seed rank selector) e
      (argumentVectorOfTermsFrom terms start count) =
    rawNumeralValue (skolemHullRawModel M seed rank selector)
      (argsCodeOfCodes (standardCodeList start count codes)).
Proof.
  intros M seed rank selector hPA start count. revert start.
  induction count as [|count IH]; intros start e codes terms hcodes.
  - cbn [argumentVectorOfTermsFrom standardCodeList argsCodeOfCodes].
    apply hull_eval_nodeTerm_numerals; [exact hPA | |];
      apply raw_term_eval_numeral.
  - rewrite standardCodeList_succ.
    cbn [argumentVectorOfTermsFrom argsCodeOfCodes].
    apply hull_eval_nodeTerm_numerals; [exact hPA | |].
    + apply raw_term_eval_numeral.
    + apply hull_eval_pairTerm_numerals; [exact hPA | |].
      * apply hcodes. lia.
      * apply IH. intros i hi. apply hcodes. lia.
Qed.

Corollary hull_eval_argumentVectorOfTerms_numerals : forall
    (M : RawPAModel) seed rank selector,
  RawPASatisfies M -> forall traceRank
    (e : nat -> skolemHullRawModel M seed rank selector) codes terms,
  (forall i, i < traceRank ->
    raw_term_eval (skolemHullRawModel M seed rank selector) e (terms i) =
      rawNumeralValue (skolemHullRawModel M seed rank selector) (codes i)) ->
  raw_term_eval (skolemHullRawModel M seed rank selector) e
      (argumentVectorOfTerms traceRank terms) =
    rawNumeralValue (skolemHullRawModel M seed rank selector)
      (argsCodeOfCodes (standardCodeList 0 traceRank codes)).
Proof.
  intros M seed rank selector hPA traceRank e codes terms hcodes.
  unfold argumentVectorOfTerms.
  apply hull_eval_argumentVectorOfTermsFrom_numerals; [exact hPA |].
  intros i hi. apply hcodes. lia.
Qed.

(** A recognized row at an externally standard parent code.  The choose
    constructor deliberately retains raw child codes: recursive programs at
    those codes may be malformed, and the total decoder handles them. *)
Inductive StandardRowWitness (M : RawPAModel) (rank target : nat)
    (betaCode betaStep seed value : M) : Prop :=
| standardRowSeed :
    target = polynomialNode tagSeed 0 ->
    value = seed ->
    StandardRowWitness M rank target betaCode betaStep seed value
| standardRowZero :
    target = polynomialNode tagZero 0 ->
    value = raw_zero M ->
    StandardRowWitness M rank target betaCode betaStep seed value
| standardRowSucc : forall childCode childValue,
    target = polynomialNode tagSucc childCode ->
    RawBetaEntry M childValue betaCode betaStep
      (rawNumeralValue M childCode) ->
    value = raw_succ M childValue ->
    StandardRowWitness M rank target betaCode betaStep seed value
| standardRowAdd : forall leftCode rightCode leftValue rightValue,
    target = polynomialNode tagAdd (polynomialPair leftCode rightCode) ->
    RawBetaEntry M leftValue betaCode betaStep
      (rawNumeralValue M leftCode) ->
    RawBetaEntry M rightValue betaCode betaStep
      (rawNumeralValue M rightCode) ->
    value = raw_add M leftValue rightValue ->
    StandardRowWitness M rank target betaCode betaStep seed value
| standardRowMul : forall leftCode rightCode leftValue rightValue,
    target = polynomialNode tagMul (polynomialPair leftCode rightCode) ->
    RawBetaEntry M leftValue betaCode betaStep
      (rawNumeralValue M leftCode) ->
    RawBetaEntry M rightValue betaCode betaStep
      (rawNumeralValue M rightCode) ->
    value = raw_mul M leftValue rightValue ->
    StandardRowWitness M rank target betaCode betaStep seed value
| standardRowChoose : forall formulaIndex codes values,
    formulaIndex < length (formula_rank_enum rank) ->
    target = polynomialNode tagChoose
      (polynomialPair formulaIndex
        (argsCodeOfCodes (standardCodeList 0 rank codes))) ->
    (forall i, i < rank ->
      RawBetaEntry M (values i) betaCode betaStep
        (rawNumeralValue M (codes i))) ->
    raw_formula_sat M (scons M value (boundedEnv M rank values))
      (canonicalSelectorFormula (selectorBody rank formulaIndex)) ->
    StandardRowWitness M rank target betaCode betaStep seed value.

Lemma hull_rawNumeralValue_injective : forall
    (M : RawPAModel) seed rank selector,
  RawPASatisfies M -> forall m n,
  rawNumeralValue (skolemHullRawModel M seed rank selector) m =
    rawNumeralValue (skolemHullRawModel M seed rank selector) n ->
  m = n.
Proof.
  intros M seed rank selector hPA m n hmn.
  apply (rawNumeralValue_injective M hPA m n).
  apply (f_equal (skolemHullVal M seed rank selector)) in hmn.
  now rewrite !skolemHull_rawNumeralValue_val in hmn.
Qed.

Lemma hull_rawLt_numeralValue_cases : forall
    (M : RawPAModel) seed rank selector,
  RawPASatisfies M -> forall
    (x : skolemHullRawModel M seed rank selector) target,
  rawLt (skolemHullRawModel M seed rank selector) x
    (rawNumeralValue (skolemHullRawModel M seed rank selector) target) ->
  exists code, code < target /\
    x = rawNumeralValue
      (skolemHullRawModel M seed rank selector) code.
Proof.
  intros M seed rank selector hPA x target hlt.
  pose proof (skolemHull_rawLt_to_ambient M seed rank selector x
    (rawNumeralValue (skolemHullRawModel M seed rank selector) target)
    hlt) as hambient.
  rewrite skolemHull_rawNumeralValue_val in hambient.
  destruct (raw_lt_numeralValue_cases M hPA
    (skolemHullVal M seed rank selector x) target hambient)
    as [code [hcode hx]].
  exists code. split; [exact hcode |].
  apply (skolemHullVal_injective M seed rank selector).
  rewrite skolemHull_rawNumeralValue_val. exact hx.
Qed.

Lemma hull_rawLt_numeralValue_of_lt : forall
    (M : RawPAModel) seed rank,
  RawPASatisfies M ->
  formula_rank hullLtFormula <= rank ->
  forall left right, left < right ->
  rawLt (skolemHullRawModel M seed rank (rawCanonicalSelector M))
    (rawNumeralValue
      (skolemHullRawModel M seed rank (rawCanonicalSelector M)) left)
    (rawNumeralValue
      (skolemHullRawModel M seed rank (rawCanonicalSelector M)) right).
Proof.
  intros M seed rank hPA hLtRank left right hlt.
  apply (skolemHull_rawLt_of_ambient M seed rank
    (rawCanonicalSelector M)).
  - apply rawCanonicalSelector_witnesses.
    exact (raw_definable_least_number_of_pa M hPA).
  - exact hLtRank.
  - rewrite !skolemHull_rawNumeralValue_val.
    exact (raw_lt_numeralValue_of_lt M hPA left right hlt).
Qed.

Section RowInversion.

Context (M : RawPAModel) (ambientSeed : M) (rank : nat).
Let K : RawPAModel := skolemHullRawModel M ambientSeed rank
  (rawCanonicalSelector M).

Variable hPA : RawPASatisfies M.

(** Shared discharge for the nullary (seed/zero) row cases: identify the
    target code through numeral injectivity and forward the value fact. *)
Ltac nullary_row_of_sat ctor hcode hsat :=
  apply ctor;
  [ apply (hull_rawNumeralValue_injective M ambientSeed rank
      (rawCanonicalSelector M) hPA);
    etransitivity; [symmetry; exact hcode |];
    etransitivity; [exact (proj1 hsat) |];
    apply hull_eval_nodeTerm_numerals; [exact hPA | |];
      apply raw_term_eval_numeral
  | exact (proj2 hsat) ].

Lemma standardRowSeed_of_sat : forall target
    code value betaCode betaStep seedTerm e,
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e (seedCase code value seedTerm) ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value).
Proof.
  intros target code value betaCode betaStep seedTerm e hcode hsat.
  cbn [seedCase raw_formula_sat] in hsat.
  nullary_row_of_sat standardRowSeed hcode hsat.
Qed.

Lemma standardRowZero_of_sat : forall target
    code value betaCode betaStep seedTerm e,
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e (zeroCase code value) ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value).
Proof.
  intros target code value betaCode betaStep seedTerm e hcode hsat.
  cbn [zeroCase raw_formula_sat] in hsat.
  nullary_row_of_sat standardRowZero hcode hsat.
Qed.

Lemma standardRowSucc_of_sat : forall target
    code value betaCode betaStep seedTerm e,
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e (succCase code value betaCode betaStep) ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value).
Proof.
  intros target code value betaCode betaStep seedTerm e hcode hsat.
  destruct (proj1 (raw_sat_existsN_iff_slots K 2 _ e) hsat)
    as [slots hconj].
  pose proof (proj1 (raw_sat_conjunction K (slotEnv K 2 slots e) _)
    hconj) as hall.
  pose proof (hall
    (PA.pEq (liftTerm 2 code)
      (nodeTerm (PA.Term.numeral tagSucc) (argumentCodeTerm 0)))
    (or_introl eq_refl)) as hrowCode.
  pose proof (hall
    (PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 2 code))
    (or_intror (or_introl eq_refl))) as hbound.
  pose proof (hall
    (PA.Formula.betaTermTermAt (argumentValueTerm 0)
      (liftTerm 2 betaCode) (liftTerm 2 betaStep)
      (argumentCodeTerm 0))
    (or_intror (or_intror (or_introl eq_refl)))) as hlookup.
  pose proof (hall
    (PA.pEq (liftTerm 2 value)
      (PA.tSucc (argumentValueTerm 0)))
    (or_intror (or_intror (or_intror (or_introl eq_refl))))) as hvalue.
  change (raw_term_eval K (slotEnv K 2 slots e) (liftTerm 2 code) =
    raw_term_eval K (slotEnv K 2 slots e)
      (nodeTerm (PA.Term.numeral tagSucc) (argumentCodeTerm 0)))
    in hrowCode.
  rewrite raw_term_eval_liftTerm_slotEnv in hrowCode.
  apply (proj1 (raw_sat_ltTermAt_iff K _ _ _)) in hbound.
  rewrite raw_term_eval_liftTerm_slotEnv, hcode in hbound.
  set (childValue := raw_term_eval K (slotEnv K 2 slots e)
    (argumentValueTerm 0)).
  set (childIndex := raw_term_eval K (slotEnv K 2 slots e)
    (argumentCodeTerm 0)).
  destruct (hull_rawLt_numeralValue_cases M ambientSeed rank
    (rawCanonicalSelector M) hPA childIndex target)
    as [childCode [hchildLt hchildIndex]].
  { exact hbound. }
  apply (proj1 (raw_sat_betaTermTermAt_iff K _ _ _ _ _)) in hlookup.
  rewrite !raw_term_eval_liftTerm_slotEnv in hlookup.
  change (RawBetaEntry K childValue
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    childIndex) in hlookup.
  change (raw_term_eval K (slotEnv K 2 slots e) (liftTerm 2 value) =
    raw_succ K childValue) in hvalue.
  rewrite raw_term_eval_liftTerm_slotEnv in hvalue.
  apply standardRowSucc with (childCode := childCode)
    (childValue := childValue).
  - apply (hull_rawNumeralValue_injective M ambientSeed rank
      (rawCanonicalSelector M) hPA).
    etransitivity; [symmetry; exact hcode |].
    etransitivity; [exact hrowCode |].
    apply hull_eval_nodeTerm_numerals; [exact hPA | |].
    + apply raw_term_eval_numeral.
    + exact hchildIndex.
  - rewrite hchildIndex in hlookup. exact hlookup.
  - exact hvalue.
Qed.

Lemma standardBinaryFacts_of_sat : forall target tag op opValue
    code value betaCode betaStep e,
  (forall e' a b,
    raw_term_eval K e' (op a b) =
      opValue (raw_term_eval K e' a) (raw_term_eval K e' b)) ->
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e
    (binaryCase tag op code value betaCode betaStep) ->
  exists leftCode rightCode leftValue rightValue,
    target = polynomialNode tag (polynomialPair leftCode rightCode) /\
    RawBetaEntry K leftValue
      (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
      (rawNumeralValue K leftCode) /\
    RawBetaEntry K rightValue
      (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
      (rawNumeralValue K rightCode) /\
    raw_term_eval K e value = opValue leftValue rightValue.
Proof.
  intros target tag op opValue code value betaCode betaStep e
    hop hcode hsat.
  destruct (proj1 (raw_sat_existsN_iff_slots K 4 _ e) hsat)
    as [slots hconj].
  pose proof (proj1 (raw_sat_conjunction K (slotEnv K 4 slots e) _)
    hconj) as hall.
  pose proof (hall
    (PA.pEq (liftTerm 4 code)
      (nodeTerm (PA.Term.numeral tag)
        (pairTerm (argumentCodeTerm 0) (argumentCodeTerm 1))))
    (or_introl eq_refl)) as hrowCode.
  pose proof (hall
    (PA.Formula.ltTermAt (argumentCodeTerm 0) (liftTerm 4 code))
    (or_intror (or_introl eq_refl))) as hleftBound.
  pose proof (hall
    (PA.Formula.ltTermAt (argumentCodeTerm 1) (liftTerm 4 code))
    (or_intror (or_intror (or_introl eq_refl)))) as hrightBound.
  pose proof (hall
    (PA.Formula.betaTermTermAt (argumentValueTerm 0)
      (liftTerm 4 betaCode) (liftTerm 4 betaStep)
      (argumentCodeTerm 0))
    (or_intror (or_intror (or_intror (or_introl eq_refl)))))
    as hleftLookup.
  pose proof (hall
    (PA.Formula.betaTermTermAt (argumentValueTerm 1)
      (liftTerm 4 betaCode) (liftTerm 4 betaStep)
      (argumentCodeTerm 1))
    (or_intror (or_intror (or_intror
      (or_intror (or_introl eq_refl)))))) as hrightLookup.
  pose proof (hall
    (PA.pEq (liftTerm 4 value)
      (op (argumentValueTerm 0) (argumentValueTerm 1)))
    (or_intror (or_intror (or_intror
      (or_intror (or_intror (or_introl eq_refl))))))) as hvalue.
  change (raw_term_eval K (slotEnv K 4 slots e) (liftTerm 4 code) =
    raw_term_eval K (slotEnv K 4 slots e)
      (nodeTerm (PA.Term.numeral tag)
        (pairTerm (argumentCodeTerm 0) (argumentCodeTerm 1))))
    in hrowCode.
  rewrite raw_term_eval_liftTerm_slotEnv in hrowCode.
  apply (proj1 (raw_sat_ltTermAt_iff K _ _ _)) in hleftBound.
  apply (proj1 (raw_sat_ltTermAt_iff K _ _ _)) in hrightBound.
  rewrite raw_term_eval_liftTerm_slotEnv, hcode in hleftBound.
  rewrite raw_term_eval_liftTerm_slotEnv, hcode in hrightBound.
  set (leftValue := raw_term_eval K (slotEnv K 4 slots e)
    (argumentValueTerm 0)).
  set (rightValue := raw_term_eval K (slotEnv K 4 slots e)
    (argumentValueTerm 1)).
  set (leftIndex := raw_term_eval K (slotEnv K 4 slots e)
    (argumentCodeTerm 0)).
  set (rightIndex := raw_term_eval K (slotEnv K 4 slots e)
    (argumentCodeTerm 1)).
  destruct (hull_rawLt_numeralValue_cases M ambientSeed rank
    (rawCanonicalSelector M) hPA leftIndex target hleftBound)
    as [leftCode [hleftLt hleftIndex]].
  destruct (hull_rawLt_numeralValue_cases M ambientSeed rank
    (rawCanonicalSelector M) hPA rightIndex target hrightBound)
    as [rightCode [hrightLt hrightIndex]].
  apply (proj1 (raw_sat_betaTermTermAt_iff K _ _ _ _ _))
    in hleftLookup.
  apply (proj1 (raw_sat_betaTermTermAt_iff K _ _ _ _ _))
    in hrightLookup.
  rewrite !raw_term_eval_liftTerm_slotEnv in hleftLookup.
  rewrite !raw_term_eval_liftTerm_slotEnv in hrightLookup.
  change (RawBetaEntry K leftValue
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    leftIndex) in hleftLookup.
  change (RawBetaEntry K rightValue
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    rightIndex) in hrightLookup.
  change (raw_term_eval K (slotEnv K 4 slots e) (liftTerm 4 value) =
    raw_term_eval K (slotEnv K 4 slots e)
      (op (argumentValueTerm 0) (argumentValueTerm 1))) in hvalue.
  rewrite raw_term_eval_liftTerm_slotEnv, hop in hvalue.
  change (raw_term_eval K e value = opValue leftValue rightValue) in hvalue.
  exists leftCode, rightCode, leftValue, rightValue.
  split.
  - apply (hull_rawNumeralValue_injective M ambientSeed rank
      (rawCanonicalSelector M) hPA).
    etransitivity; [symmetry; exact hcode |].
    etransitivity; [exact hrowCode |].
    apply hull_eval_nodeTerm_numerals; [exact hPA | |].
    + apply raw_term_eval_numeral.
    + apply hull_eval_pairTerm_numerals; [exact hPA | |].
      * exact hleftIndex.
      * exact hrightIndex.
  - split.
    + rewrite hleftIndex in hleftLookup. exact hleftLookup.
    + split.
      * rewrite hrightIndex in hrightLookup. exact hrightLookup.
      * exact hvalue.
Qed.

(** Shared discharge for the binary (add/mul) row cases: unpack the
    seven-fold witness of [standardBinaryFacts_of_sat] and rebuild the
    corresponding [StandardRowWitness] constructor. *)
Ltac binary_row_of_sat tag op opValue ctor hcode hsat :=
  destruct (standardBinaryFacts_of_sat _ tag op opValue _ _ _ _ _
    (fun _ _ _ => eq_refl) hcode hsat)
    as [leftCode [rightCode [leftValue [rightValue
      [htarget [hleft [hright hvalue]]]]]]];
  exact (ctor _ _ _ _ _ _ _
    leftCode rightCode leftValue rightValue
    htarget hleft hright hvalue).

Lemma standardRowAdd_of_sat : forall target
    code value betaCode betaStep seedTerm e,
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e
    (binaryCase tagAdd PA.tAdd code value betaCode betaStep) ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value).
Proof.
  intros target code value betaCode betaStep seedTerm e hcode hsat.
  binary_row_of_sat tagAdd PA.tAdd (raw_add K) standardRowAdd hcode hsat.
Qed.

Lemma standardRowMul_of_sat : forall target
    code value betaCode betaStep seedTerm e,
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e
    (binaryCase tagMul PA.tMul code value betaCode betaStep) ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value).
Proof.
  intros target code value betaCode betaStep seedTerm e hcode hsat.
  binary_row_of_sat tagMul PA.tMul (raw_mul K) standardRowMul hcode hsat.
Qed.

Lemma standardRowChooseBranch_of_sat : forall target formulaIndex
    code value betaCode betaStep seedTerm e,
  formulaIndex < length (formula_rank_enum rank) ->
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e
    (selectorBranch rank formulaIndex
      (canonicalSelectorFormula (selectorBody rank formulaIndex))
      code value betaCode betaStep) ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value).
Proof.
  intros target formulaIndex code value betaCode betaStep seedTerm e
    hindex hcode hsat.
  set (width := 2 * rank).
  destruct (proj1 (raw_sat_existsN_iff_slots K width _ e) hsat)
    as [slots hconj].
  pose proof (proj1 (raw_sat_conjunction K
    (slotEnv K width slots e) _) hconj) as hall.
  pose proof (hall
    (PA.pEq (liftTerm width code)
      (nodeTerm (PA.Term.numeral tagChoose)
        (pairTerm (PA.Term.numeral formulaIndex)
          (argumentVectorTerm rank))))
    (or_introl eq_refl)) as hrowCode.
  pose proof (hall
    (conjunction (map (fun i =>
      PA.Formula.ltTermAt (argumentCodeTerm i)
        (liftTerm width code)) (seq 0 rank)))
    (or_intror (or_introl eq_refl))) as hboundsConj.
  pose proof (hall
    (conjunction (map (fun i =>
      PA.Formula.betaTermTermAt (argumentValueTerm i)
        (liftTerm width betaCode) (liftTerm width betaStep)
        (argumentCodeTerm i)) (seq 0 rank)))
    (or_intror (or_intror (or_introl eq_refl)))) as hlookupConj.
  pose proof (hall
    (graphAt rank
      (canonicalSelectorFormula (selectorBody rank formulaIndex))
      (liftTerm width value) argumentValueTerm)
    (or_intror (or_intror (or_intror (or_introl eq_refl))))) as hgraph.
  change (raw_term_eval K (slotEnv K width slots e)
      (liftTerm width code) =
    raw_term_eval K (slotEnv K width slots e)
      (nodeTerm (PA.Term.numeral tagChoose)
        (pairTerm (PA.Term.numeral formulaIndex)
          (argumentVectorTerm rank)))) in hrowCode.
  subst width.
  rewrite raw_term_eval_liftTerm_slotEnv in hrowCode.
  pose proof (proj1 (raw_sat_conjunction K
    (slotEnv K (2 * rank) slots e) _) hboundsConj) as hbounds.
  pose proof (proj1 (raw_sat_conjunction K
    (slotEnv K (2 * rank) slots e) _) hlookupConj) as hlookups.
  set (values := fun i => raw_term_eval K
    (slotEnv K (2 * rank) slots e) (argumentValueTerm i)).
  set (indices := fun i => raw_term_eval K
    (slotEnv K (2 * rank) slots e) (argumentCodeTerm i)).
  assert (hstandard : forall i, i < rank -> exists childCode,
      childCode < target /\ indices i = rawNumeralValue K childCode).
  {
    intros i hi.
    pose proof (hbounds
      (PA.Formula.ltTermAt (argumentCodeTerm i)
        (liftTerm (2 * rank) code))) as hbound.
    assert (hmem : In
      (PA.Formula.ltTermAt (argumentCodeTerm i)
        (liftTerm (2 * rank) code))
      (map (fun j => PA.Formula.ltTermAt (argumentCodeTerm j)
        (liftTerm (2 * rank) code)) (seq 0 rank))).
    {
      apply in_map_iff. exists i. split; [reflexivity |].
      apply in_seq. lia.
    }
    specialize (hbound hmem).
    apply (proj1 (raw_sat_ltTermAt_iff K _ _ _)) in hbound.
    rewrite raw_term_eval_liftTerm_slotEnv, hcode in hbound.
    exact (hull_rawLt_numeralValue_cases M ambientSeed rank
      (rawCanonicalSelector M) hPA (indices i) target hbound).
  }
  set (codes := fun i => epsilon (inhabits 0) (fun childCode =>
    i < rank -> childCode < target /\
      indices i = rawNumeralValue K childCode)).
  assert (hcodes : forall i, i < rank ->
      codes i < target /\ indices i = rawNumeralValue K (codes i)).
  {
    intros i hi. unfold codes.
    destruct (hstandard i hi) as [childCode [hlt heq]].
    assert (hex : exists candidate,
      i < rank -> candidate < target /\
        indices i = rawNumeralValue K candidate).
    { exists childCode. exact (fun _ => conj hlt heq). }
    exact (epsilon_spec (inhabits 0) (fun candidate =>
      i < rank -> candidate < target /\
        indices i = rawNumeralValue K candidate) hex hi).
  }
  assert (hlookup : forall i, i < rank ->
      RawBetaEntry K (values i)
        (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
        (rawNumeralValue K (codes i))).
  {
    intros i hi.
    pose proof (hlookups
      (PA.Formula.betaTermTermAt (argumentValueTerm i)
        (liftTerm (2 * rank) betaCode) (liftTerm (2 * rank) betaStep)
        (argumentCodeTerm i))) as hentry.
    assert (hmem : In
      (PA.Formula.betaTermTermAt (argumentValueTerm i)
        (liftTerm (2 * rank) betaCode) (liftTerm (2 * rank) betaStep)
        (argumentCodeTerm i))
      (map (fun j => PA.Formula.betaTermTermAt (argumentValueTerm j)
        (liftTerm (2 * rank) betaCode) (liftTerm (2 * rank) betaStep)
        (argumentCodeTerm j)) (seq 0 rank))).
    {
      apply in_map_iff. exists i. split; [reflexivity |].
      apply in_seq. lia.
    }
    specialize (hentry hmem).
    apply (proj1 (raw_sat_betaTermTermAt_iff K _ _ _ _ _)) in hentry.
    rewrite !raw_term_eval_liftTerm_slotEnv in hentry.
    change (RawBetaEntry K (values i)
      (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
      (indices i)) in hentry.
    rewrite (proj2 (hcodes i hi)) in hentry. exact hentry.
  }
  apply (proj1 (raw_sat_graphAt K rank
    (canonicalSelectorFormula (selectorBody rank formulaIndex))
    (liftTerm (2 * rank) value) argumentValueTerm
    (slotEnv K (2 * rank) slots e))) in hgraph.
  rewrite raw_term_eval_liftTerm_slotEnv in hgraph.
  change (raw_formula_sat K
    (scons K (raw_term_eval K e value) (boundedEnv K rank values))
    (canonicalSelectorFormula (selectorBody rank formulaIndex))) in hgraph.
  apply standardRowChoose with (formulaIndex := formulaIndex)
    (codes := codes) (values := values).
  - exact hindex.
  - apply (hull_rawNumeralValue_injective M ambientSeed rank
      (rawCanonicalSelector M) hPA).
    etransitivity; [symmetry; exact hcode |].
    etransitivity; [exact hrowCode |].
    apply hull_eval_nodeTerm_numerals; [exact hPA | |].
    + apply raw_term_eval_numeral.
    + apply hull_eval_pairTerm_numerals; [exact hPA | |].
      * apply raw_term_eval_numeral.
      * apply hull_eval_argumentVector_numerals; [exact hPA |].
        intros i hi. exact (proj2 (hcodes i hi)).
  - exact hlookup.
  - exact hgraph.
Qed.

Lemma standardRowChoose_of_sat : forall target
    code value betaCode betaStep seedTerm e,
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e
    (selectorCase rank code value betaCode betaStep) ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value).
Proof.
  intros target code value betaCode betaStep seedTerm e hcode hsat.
  destruct (proj1 (raw_sat_disjunction K e _) hsat)
    as [branch [hmem hbranch]].
  apply in_map_iff in hmem.
  destruct hmem as [formulaIndex [<- hindex]].
  eapply standardRowChooseBranch_of_sat with
    (formulaIndex := formulaIndex) (code := code)
    (value := value) (betaCode := betaCode) (betaStep := betaStep)
    (seedTerm := seedTerm) (e := e);
    [|exact hcode|exact hbranch].
  apply in_seq in hindex. lia.
Qed.

Theorem standardRowWitness_of_sat_programCases : forall target
    code value betaCode betaStep seedTerm e,
  raw_term_eval K e code = rawNumeralValue K target ->
  raw_formula_sat K e
    (programCases rank code value betaCode betaStep seedTerm) ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value).
Proof.
  intros target code value betaCode betaStep seedTerm e hcode hsat.
  destruct (proj1 (raw_sat_disjunction K e _) hsat)
    as [branch [hmem hbranch]].
  cbn [In] in hmem.
  destruct hmem as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]].
  - exact (standardRowSeed_of_sat target code value betaCode betaStep
      seedTerm e hcode hbranch).
  - exact (standardRowZero_of_sat target code value betaCode betaStep
      seedTerm e hcode hbranch).
  - exact (standardRowSucc_of_sat target code value betaCode betaStep
      seedTerm e hcode hbranch).
  - exact (standardRowAdd_of_sat target code value betaCode betaStep
      seedTerm e hcode hbranch).
  - exact (standardRowMul_of_sat target code value betaCode betaStep
      seedTerm e hcode hbranch).
  - exact (standardRowChoose_of_sat target code value betaCode betaStep
      seedTerm e hcode hbranch).
Qed.

Theorem sat_programCases_of_standardRowWitness :
  formula_rank hullLtFormula <= rank ->
  forall target code value betaCode betaStep seedTerm e,
  raw_term_eval K e code = rawNumeralValue K target ->
  StandardRowWitness K rank target
    (raw_term_eval K e betaCode) (raw_term_eval K e betaStep)
    (raw_term_eval K e seedTerm) (raw_term_eval K e value) ->
  raw_formula_sat K e
    (programCases rank code value betaCode betaStep seedTerm).
Proof.
  intros hLtRank target code value betaCode betaStep seedTerm e
    hcode hwitness.
  apply (proj2 (raw_sat_disjunction K e _)).
  destruct hwitness as
    [htarget hvalue
    | htarget hvalue
    | childCode childValue htarget hlookup hvalue
    | leftCode rightCode leftValue rightValue
        htarget hleft hright hvalue
    | leftCode rightCode leftValue rightValue
        htarget hleft hright hvalue
    | formulaIndex codes values hindex htarget hlookup hgraph].
  - exists (seedCase code value seedTerm). split.
    + now left.
    + cbn [seedCase raw_formula_sat]. split.
      * rewrite hcode, htarget. symmetry.
        apply hull_eval_nodeTerm_numerals; [exact hPA | |];
          apply raw_term_eval_numeral.
      * exact hvalue.
  - exists (zeroCase code value). split.
    + now right; left.
    + cbn [zeroCase raw_formula_sat]. split.
      * rewrite hcode, htarget. symmetry.
        apply hull_eval_nodeTerm_numerals; [exact hPA | |];
          apply raw_term_eval_numeral.
      * exact hvalue.
  - exists (succCase code value betaCode betaStep). split.
    + now right; right; left.
    + apply raw_sat_succCase_of with
        (childTerm := PA.Term.numeral childCode)
        (childValue := childValue).
      * rewrite hcode, htarget. symmetry.
        apply hull_eval_nodeTerm_numerals; [exact hPA | |];
          apply raw_term_eval_numeral.
      * rewrite raw_term_eval_numeral, hcode, htarget.
        apply hull_rawLt_numeralValue_of_lt; [exact hPA | exact hLtRank |].
        apply polynomialNode_payload_lt.
      * now rewrite raw_term_eval_numeral.
      * exact hvalue.
  - exists (binaryCase tagAdd PA.tAdd
      code value betaCode betaStep). split.
    + now right; right; right; left.
    + apply raw_sat_binaryCase_of with
        (opValue := raw_add K)
        (leftTerm := PA.Term.numeral leftCode)
        (rightTerm := PA.Term.numeral rightCode)
        (leftValue := leftValue) (rightValue := rightValue).
      * intros. reflexivity.
      * rewrite hcode, htarget. symmetry.
        apply hull_eval_nodeTerm_numerals; [exact hPA | |].
        -- apply raw_term_eval_numeral.
        -- apply hull_eval_pairTerm_numerals; [exact hPA | |];
             apply raw_term_eval_numeral.
      * rewrite raw_term_eval_numeral, hcode, htarget.
        apply hull_rawLt_numeralValue_of_lt; [exact hPA | exact hLtRank |].
        eapply Nat.le_lt_trans.
        -- apply polynomialPair_left_le.
        -- apply polynomialNode_payload_lt.
      * rewrite raw_term_eval_numeral, hcode, htarget.
        apply hull_rawLt_numeralValue_of_lt; [exact hPA | exact hLtRank |].
        eapply Nat.le_lt_trans.
        -- apply polynomialPair_right_le.
        -- apply polynomialNode_payload_lt.
      * now rewrite raw_term_eval_numeral.
      * now rewrite raw_term_eval_numeral.
      * exact hvalue.
  - exists (binaryCase tagMul PA.tMul
      code value betaCode betaStep). split.
    + now right; right; right; right; left.
    + apply raw_sat_binaryCase_of with
        (opValue := raw_mul K)
        (leftTerm := PA.Term.numeral leftCode)
        (rightTerm := PA.Term.numeral rightCode)
        (leftValue := leftValue) (rightValue := rightValue).
      * intros. reflexivity.
      * rewrite hcode, htarget. symmetry.
        apply hull_eval_nodeTerm_numerals; [exact hPA | |].
        -- apply raw_term_eval_numeral.
        -- apply hull_eval_pairTerm_numerals; [exact hPA | |];
             apply raw_term_eval_numeral.
      * rewrite raw_term_eval_numeral, hcode, htarget.
        apply hull_rawLt_numeralValue_of_lt; [exact hPA | exact hLtRank |].
        eapply Nat.le_lt_trans.
        -- apply polynomialPair_left_le.
        -- apply polynomialNode_payload_lt.
      * rewrite raw_term_eval_numeral, hcode, htarget.
        apply hull_rawLt_numeralValue_of_lt; [exact hPA | exact hLtRank |].
        eapply Nat.le_lt_trans.
        -- apply polynomialPair_right_le.
        -- apply polynomialNode_payload_lt.
      * now rewrite raw_term_eval_numeral.
      * now rewrite raw_term_eval_numeral.
      * exact hvalue.
  - exists (selectorCase rank code value betaCode betaStep). split.
    + now right; right; right; right; right; left.
    + apply raw_sat_selectorCase_of with
        (formulaIndex := formulaIndex) (values := values)
        (terms := fun i => PA.Term.numeral (codes i)).
      * exact hindex.
      * rewrite hcode, htarget. symmetry.
        apply hull_eval_nodeTerm_numerals; [exact hPA | |].
        -- apply raw_term_eval_numeral.
        -- apply hull_eval_pairTerm_numerals; [exact hPA | |].
           ++ apply raw_term_eval_numeral.
           ++ apply hull_eval_argumentVectorOfTerms_numerals;
                [exact hPA |].
              intros i hi. apply raw_term_eval_numeral.
      * intros i hi.
        rewrite raw_term_eval_numeral, hcode, htarget.
        apply hull_rawLt_numeralValue_of_lt; [exact hPA | exact hLtRank |].
        eapply Nat.lt_trans.
        -- apply argsCodeOfCodes_entry_lt.
           unfold standardCodeList.
           apply in_map_iff. exists i. split; [reflexivity |].
           apply (proj2 (in_seq rank 0 i)).
           split; [apply Nat.le_0_l |]. simpl. exact hi.
        -- eapply Nat.le_lt_trans.
           ++ apply polynomialPair_right_le.
           ++ apply polynomialNode_payload_lt.
      * intros i hi. rewrite raw_term_eval_numeral.
        apply hlookup. exact hi.
      * exact hgraph.
Qed.

End RowInversion.

End PAStandardTraceRows.
