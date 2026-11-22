import IPRADerivations.Analysis.RationalArithmetic
import IPRADerivations.Analysis.GaussianL1
import IPRADerivations.AnalyticNumberTheory.DivisorHyperbola
import IPRADerivations.Foundations.RealizerComposition

/-!
# Actual normalized scalar budgets for finite quadratic-tower tables

The source majorant (11.1) starts from bounds on signed numerator values
and positive denominators. The actual gcd normalizer preserves these
bounds. Original rational addition and multiplication obey the stated
one-operation amplification. A scalar code bound additionally requires
the proved canonical guard; arbitrary raw signed codes are not bounded
by their values. The numerical growth iterate below concerns these
scalar operations, not an unconstructed recursive tower multiplication.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerScalarBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf rationalCode)
open RationalIntegerNormalization (normalize divisor reducedDenominator)
open RationalNormalForm (wellFormed)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def height (q B : PTm n) : Fm PTm n :=
  le (zabs (numeratorOf q)) B ⋏ le (denominatorOf q) B
def codeCap (B : PTm n) : PTm n := succ (pairT (pairT B B) B)
def amp (B : PTm n) : PTm n := two*B*B

@[simp] theorem subst_height {k : ℕ} (σ : Fin n → PTm k) (q B : PTm n) :
    (height q B).subst σ = height (Syn.subst σ q) (Syn.subst σ B) := by
  simp [height,RationalSupMetric.numeratorOf]
@[simp] theorem subst_codeCap {k : ℕ} (σ : Fin n → PTm k) (B : PTm n) :
    Syn.subst σ (codeCap B) = codeCap (Syn.subst σ B) := by simp [codeCap]
@[simp] theorem subst_amp {k : ℕ} (σ : Fin n → PTm k) (B : PTm n) :
    Syn.subst σ (amp B) = amp (Syn.subst σ B) := by simp [amp,two,one]

theorem height_congr {q q' B B' : PTm n} (hq : Γ ⊢[PRAAx] q ≐ q')
    (hB : Γ ⊢[PRAAx] B ≐ B') (h : Γ ⊢[PRAAx] height q B) :
    Γ ⊢[PRAAx] height q' B' := by
  have hp := congrFst (congrFst hq)
  have hn := congrSnd (congrFst hq)
  have num := congrAdd (congrMonus hp hn) (congrMonus hn hp)
  exact .andI (le_congr num hB (Prf.andE₁ h))
    (le_congr (congrSucc (congrSnd hq)) hB (Prf.andE₂ h))

theorem height_mono (q B C : PTm n) (h : Γ ⊢[PRAAx] height q B)
    (hBC : Γ ⊢[PRAAx] le B C) : Γ ⊢[PRAAx] height q C :=
  .andI (le_trans (Prf.andE₁ h) hBC) (le_trans (Prf.andE₂ h) hBC)

theorem quotient_bound (x D : PTm n) (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) :
    Γ ⊢[PRAAx] le (quo x D) x :=
  le_congr (congrAp2 quoF (.eqRefl x) hD).eqSymm (.eqRefl x)
    (AnalyticNumberTheory.DivisorHyperbola.quo_le_self (pred D) x)

theorem normalized_numerator_bound (a : ZT n) (D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le (zabs (numeratorOf (normalize a D))) (zabs a) := by
  have e := (Foundations.GapDecision.zabs_congr
    (ZT.toZ_eq (RationalIntegerNormalization.normalize_numerator (Γ := Γ) a D))).eqTrans
      (RationalNormalForm.reduced_absolute a D)
  exact le_congr e.eqSymm (.eqRefl _)
    (quotient_bound _ _ (RationalIntegerNormalization.divisor_positive a D hD))

theorem normalized_denominator_bound (a : ZT n) (D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le (denominatorOf (normalize a D)) D :=
  le_congr (RationalIntegerNormalization.normalize_denominator a D hD).eqSymm (.eqRefl D)
    (quotient_bound D _ (RationalIntegerNormalization.divisor_positive a D hD))

theorem normalize_height (a : ZT n) (D B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (ha : Γ ⊢[PRAAx] le (zabs a) B)
    (hDB : Γ ⊢[PRAAx] le D B) : Γ ⊢[PRAAx] height (normalize a D) B :=
  .andI (le_trans (normalized_numerator_bound a D hD) ha)
    (le_trans (normalized_denominator_bound a D hD) hDB)

theorem recode_height (q B : PTm n) (h : Γ ⊢[PRAAx] height q B) :
    Γ ⊢[PRAAx] height (RationalArithmetic.recode q) B :=
  normalize_height _ _ _ (RationalNormalForm.denominator_positive q) (Prf.andE₁ h) (Prf.andE₂ h)

theorem negative_height (q B : PTm n) (h : Γ ⊢[PRAAx] height q B) :
    Γ ⊢[PRAAx] height (RationalArithmetic.negative q) B :=
  normalize_height _ _ _ (RationalNormalForm.denominator_positive q)
    (le_congr (Foundations.GapDecision.zabs_neg _).eqSymm (.eqRefl _) (Prf.andE₁ h)) (Prf.andE₂ h)

theorem multiply_height (q r B : PTm n) (hq : Γ ⊢[PRAAx] height q B)
    (hr : Γ ⊢[PRAAx] height r B) :
    Γ ⊢[PRAAx] height (RationalArithmetic.multiply q r) (B*B) :=
  normalize_height _ _ _ (RationalArithmetic.product_denominator_positive q r)
    (le_congr (GaussianL1.abs_multiply _ _).eqSymm (.eqRefl _)
      (le_mul_mono (Prf.andE₁ hq) (Prf.andE₁ hr)))
    (le_mul_mono (Prf.andE₂ hq) (Prf.andE₂ hr))

theorem square_le_amp (B : PTm n) : Γ ⊢[PRAAx] le (B*B) (amp B) :=
  le_congr (.eqRefl _) (by unfold amp; ipra_ring)
    (le_add_right (B*B) (B*B))

theorem add_numerator_bound (q r B : PTm n) (hq : Γ ⊢[PRAAx] height q B)
    (hr : Γ ⊢[PRAAx] height r B) :
    Γ ⊢[PRAAx] le (zabs (RationalArithmetic.addNumerator q r)) (amp B) := by
  have tri := Foundations.GapDecision.zabs_tri (Γ := Γ)
    (u := numeratorOf q*ZT.ofNat (denominatorOf r))
    (v := numeratorOf r*ZT.ofNat (denominatorOf q))
    (w := RationalArithmetic.addNumerator q r) (by simp only [RationalArithmetic.addNumerator,ZT.toZ_add])
  have left := le_congr (RationalNormalForm.absolute_scale_right _ _).eqSymm (.eqRefl (B*B))
    (le_mul_mono (Prf.andE₁ hq) (Prf.andE₂ hr))
  have right := le_congr (RationalNormalForm.absolute_scale_right _ _).eqSymm (.eqRefl (B*B))
    (le_mul_mono (Prf.andE₁ hr) (Prf.andE₂ hq))
  exact le_trans tri (le_congr (.eqRefl _) (by unfold amp; ipra_ring) (add_le_add₂ left right))

theorem add_height (q r B : PTm n) (hq : Γ ⊢[PRAAx] height q B)
    (hr : Γ ⊢[PRAAx] height r B) :
    Γ ⊢[PRAAx] height (RationalArithmetic.add q r) (amp B) :=
  normalize_height _ _ _ (RationalArithmetic.product_denominator_positive q r)
    (add_numerator_bound q r B hq hr)
    (le_trans (le_mul_mono (Prf.andE₂ hq) (Prf.andE₂ hr)) (square_le_amp B))

theorem canonical_parts_bound (q B : PTm n) (hq : Γ ⊢[PRAAx] wellFormed q)
    (h : Γ ⊢[PRAAx] height q B) :
    Γ ⊢[PRAAx] le (numeratorOf q).pos B ⋏ le (numeratorOf q).neg B := by
  have parts := RationalNormalForm.unmixed_parts (numeratorOf q) (Prf.andE₁ (Prf.andE₂ hq))
  have abs : Γ ⊢[PRAAx] zabs (numeratorOf q) ≐ (numeratorOf q).pos+(numeratorOf q).neg :=
    congrAdd (Prf.andE₁ parts) (Prf.andE₂ parts)
  have total := le_congr abs (.eqRefl B) (Prf.andE₁ h)
  exact .andI (le_trans (le_add_right _ _) total) (le_trans (le_add_left _ _) total)

theorem canonical_code_bound (q B : PTm n) (hq : Γ ⊢[PRAAx] wellFormed q)
    (h : Γ ⊢[PRAAx] height q B) : Γ ⊢[PRAAx] lt q (codeCap B) := by
  have parts := canonical_parts_bound q B hq h
  have hd := RationalIntegerNormalization.positive_form
    (RationalNormalForm.denominator_positive (Γ := Γ) q)
  have pd : Γ ⊢[PRAAx] le (pred (denominatorOf q)) B :=
    le_trans (le_congr (.eqRefl _) hd.eqSymm (le_succ_self _)) (Prf.andE₂ h)
  have bound := Foundations.RealizerComposition.pair_mono
    (Foundations.RealizerComposition.pair_mono (Prf.andE₁ parts) (Prf.andE₂ parts)) pd
  have raw : Γ ⊢[PRAAx] le q (pairT (pairT B B) B) :=
    le_congr (Prf.andE₁ hq).eqSymm (.eqRefl _) bound
  exact lt_of_le_of_lt raw (le_refl _)

theorem recode_code_bound (q B : PTm n) (h : Γ ⊢[PRAAx] height q B) :
    Γ ⊢[PRAAx] lt (RationalArithmetic.recode q) (codeCap B) :=
  canonical_code_bound _ _ (RationalArithmetic.recode_guard q) (recode_height q B h)

def growthBase : PTm 1 := var 0
def growthStep : PTm 3 := amp (var 1)
def growthF : PR 2 := rec2 growthBase growthStep
def growth (t B : PTm n) : PTm n := ap2 growthF t B
def majorant (t B : PTm n) : PTm n := pw (two*B+two) (pw two t)
def growthLaw (t B : PTm n) : Fm PTm n := le (two*growth t B) (majorant t B)

@[simp] theorem subst_growth {k : ℕ} (σ : Fin n → PTm k) (t B : PTm n) :
    Syn.subst σ (growth t B) = growth (Syn.subst σ t) (Syn.subst σ B) := by simp [growth]
@[simp] theorem subst_majorant {k : ℕ} (σ : Fin n → PTm k) (t B : PTm n) :
    Syn.subst σ (majorant t B) = majorant (Syn.subst σ t) (Syn.subst σ B) := by
  simp [majorant,two,one]
@[simp] theorem subst_growthLaw {k : ℕ} (σ : Fin n → PTm k) (t B : PTm n) :
    (growthLaw t B).subst σ = growthLaw (Syn.subst σ t) (Syn.subst σ B) := by
  simp [growthLaw,two,one]

theorem growth_zero (B : PTm n) : Γ ⊢[PRAAx] growth zero B ≐ B := by
  simpa [growth,growthF,growthBase] using rec2_zero (Γ := Γ) growthBase growthStep B
theorem growth_succ (t B : PTm n) : Γ ⊢[PRAAx] growth (succ t) B ≐ amp (growth t B) := by
  simpa [growth,growthF,growthStep] using rec2_succ (Γ := Γ) growthBase growthStep t B
theorem majorant_zero (B : PTm n) : Γ ⊢[PRAAx] majorant zero B ≐ two*B+two :=
  (congrAp2 powF (pw_zero two) (.eqRefl _)).eqTrans (pw_one _)
theorem majorant_succ (t B : PTm n) : Γ ⊢[PRAAx]
    majorant (succ t) B ≐ majorant t B*majorant t B := by
  have e : Γ ⊢[PRAAx] pw two (succ t) ≐ pw two t+pw two t :=
    (pw_succ two t).eqTrans (by ipra_ring)
  exact (congrAp2 powF e (.eqRefl _)).eqTrans (pw_add _ _ _)

theorem growth_law_zero (B : PTm n) : Γ ⊢[PRAAx] growthLaw zero B :=
  le_congr (congrMul (.eqRefl _) (growth_zero B)).eqSymm (majorant_zero B).eqSymm
    (le_add_right (two*B) two)
theorem growth_law_step (t B : PTm n) (h : Γ ⊢[PRAAx] growthLaw t B) :
    Γ ⊢[PRAAx] growthLaw (succ t) B := by
  have e : Γ ⊢[PRAAx] two*growth (succ t) B ≐ (two*growth t B)*(two*growth t B) :=
    (congrMul (.eqRefl _) (growth_succ t B)).eqTrans (by unfold amp; ipra_ring)
  exact le_congr e.eqSymm (majorant_succ t B).eqSymm (le_mul_mono h h)

/-- Atomic QF induction proves the source's scalar double-exponential
majorant with the necessary factor two retained in the invariant. -/
theorem growth_bound (t B : PTm n) : Γ ⊢[PRAAx] growthLaw t B := by
  have all : Γ ⊢[PRAAx] .all (growthLaw (var 0) (Syn.shift B)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_growthLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact growth_law_zero B
    · simp only [subst_growthLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact growth_law_step _ _ Prf.hyp0
  simpa only [subst_growthLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
theorem growth_le_majorant (t B : PTm n) : Γ ⊢[PRAAx] le (growth t B) (majorant t B) :=
  le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right (growth t B) (growth t B)))
    (growth_bound t B)

def budgetOutput (t B : PTm n) : PTm n := pairT (growth t B)
  (pairT (majorant t B) (codeCap (growth t B)))
def budgetOutputF : PR 2 := PTm.toPR (budgetOutput (var 0) (var 1))
def run (t B : PTm n) : PTm n := ap2 budgetOutputF t B
@[simp] theorem subst_budgetOutput {k : ℕ} (σ : Fin n → PTm k) (t B : PTm n) :
    Syn.subst σ (budgetOutput t B) = budgetOutput (Syn.subst σ t) (Syn.subst σ B) := by
  simp [budgetOutput]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (t B : PTm n) :
    Syn.subst σ (run t B) = run (Syn.subst σ t) (Syn.subst σ B) := by simp [run]
theorem program_at (t B : PTm n) : Γ ⊢[PRAAx] run t B ≐ budgetOutput t B := by
  simpa [run,budgetOutputF,ap2] using toPR_eq (Γ := Γ) (budgetOutput (var 0) (var 1) : PTm 2) ![t,B]
theorem returned_growth (t B : PTm n) : Γ ⊢[PRAAx] fstT (run t B) ≐ growth t B :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_majorant (t B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run t B)) ≐ majorant t B :=
  (congrFst ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_code_cap (t B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run t B)) ≐ codeCap (growth t B) :=
  (congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_bound (t B : PTm n) : Γ ⊢[PRAAx] le (two*fstT (run t B)) (fstT (sndT (run t B))) :=
  le_congr (congrMul (.eqRefl _) (returned_growth t B)).eqSymm
    (returned_majorant t B).eqSymm (growth_bound t B)

theorem actual_normalized_scalar_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (zabs (⟨var 0,var 1⟩ : ZT 4)) (var 3) ⟶ le (var 2) (var 3) ⟶
      height (normalize (⟨var 0,var 1⟩ : ZT 4) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (normalize_height _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_recoded_scalar_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (height (var 0) (var 1) ⟶ height (RationalArithmetic.recode (var 0)) (var 1)) :=
  closeUniv 2 (.impI (recode_height _ _ Prf.hyp0))
theorem actual_negative_scalar_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (height (var 0) (var 1) ⟶ height (RationalArithmetic.negative (var 0)) (var 1)) :=
  closeUniv 2 (.impI (negative_height _ _ Prf.hyp0))
theorem actual_product_scalar_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (height (var 0) (var 2) ⟶ height (var 1) (var 2) ⟶
      height (RationalArithmetic.multiply (var 0) (var 1)) (var 2*var 2)) :=
  closeUniv 3 (.impI (.impI (multiply_height _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_sum_scalar_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (height (var 0) (var 2) ⟶ height (var 1) (var 2) ⟶
      height (RationalArithmetic.add (var 0) (var 1)) (amp (var 2))) :=
  closeUniv 3 (.impI (.impI (add_height _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_canonical_scalar_code_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (wellFormed (var 0) ⟶ height (var 0) (var 1) ⟶ lt (var 0) (codeCap (var 1))) :=
  closeUniv 2 (.impI (.impI (canonical_code_bound _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_raw_scalar_recode_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (height (var 0) (var 1) ⟶ lt (RationalArithmetic.recode (var 0)) (codeCap (var 1))) :=
  closeUniv 2 (.impI (recode_code_bound _ _ Prf.hyp0))
theorem actual_scalar_growth_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (growth (succ (var 0)) (var 1) ≐ amp (growth (var 0) (var 1))) := closeUniv 2 (growth_succ _ _)
theorem actual_scalar_growth_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (two*growth (var 0) (var 1)) (majorant (var 0) (var 1))) := closeUniv 2 (growth_bound _ _)
theorem actual_scalar_budget_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ budgetOutput (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_scalar_growth_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (two*fstT (run (var 0) (var 1))) (fstT (sndT (run (var 0) (var 1))))) :=
  closeUniv 2 (returned_bound _ _)

end LeanProofs.IPRA.Algebra.QuadraticTowerScalarBudget
