import IPRADerivations.Analysis.GaussianGeneralCoefficientNames
import IPRADerivations.Analysis.GaussianNonmonicStepBound
import IPRADerivations.Foundations.BoundedSyntaxBackwardInduction
import IPRADerivations.Analysis.GaussianRationalAllCoefficientPerturbation
import IPRADerivations.Analysis.GaussianGeneralFTAConstants

/-!
# Actual general descending polynomial samples

Every stored coefficient, including the leading one, is the original
observation a(N-i,s,x). No monic coefficient is inserted. The actual
length, all lookup equations and evaluation at zero are derived. Genuine
coefficient coherence and the original h+2 apartness test provide the
tail nonconstancy and exact original coefficient input for the proved
finite travel theorem. All numerical degrees and precisions are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames
  (generalCN apart tailApart referencePrecision lambdaDenominator)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N s x : PTm n) : PTm n := pairT N (pairT s x)
def sampleBody (a : PR 3) : PTm 2 := ap3 a (monus (fstT (var 1)) (var 0))
  (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def sample (a : PR 3) (N s x : PTm n) : PTm n := sequence (sampleBody a) (succ N) (data N s x)
def sourceInput (a : PR 3) (N k h x : PTm n) : Fm PTm n :=
  generalCN a N x ⋏ (le one k ⋏ (le k N ⋏ apart a k h x))
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N s x : PTm n) :
    Syn.subst σ (data N s x) = data (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N s x : PTm n) :
    Syn.subst σ (sample a N s x) = sample a (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ x) := by simp [sample]
@[simp] theorem subst_sourceInput {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N k h x : PTm n) :
    (sourceInput a N k h x).subst σ = sourceInput a (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ h) (Syn.subst σ x) := by simp [sourceInput]

theorem sample_body_at (a : PR 3) (N s x i : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody a) i (data N s x) ≐ ap3 a (monus N i) s x := by
  have fields := congrAp3 (Γ := Γ) a (congrMonus (fst_pair N (pairT s x)) (.eqRefl i))
    ((congrFst (snd_pair N (pairT s x))).eqTrans (fst_pair s x))
    ((congrSnd (snd_pair N (pairT s x))).eqTrans (snd_pair s x))
  simpa only [inst2,sampleBody,subst_ap3,PTm.subst_monus,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,data] using fields

theorem sample_length (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx] length (sample a N s x) ≐ succ N :=
  sequence_length _ _ _

theorem sample_lookup (a : PR 3) (N s x i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (sample a N s x) i ≐ ap3 a (monus N i) s x :=
  (sequence_decode (sampleBody a) ((succ_monus_succ _ _).eqTrans hi)).eqTrans (sample_body_at a N s x i)

theorem sample_leading (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx]
    entry (sample a N s x) zero ≐ ap3 a N s x :=
  (sample_lookup a N s x zero (zero_le N)).eqTrans (congrAp3 a (monus_zero N) (.eqRefl _) (.eqRefl _))
theorem sample_constant (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx]
    entry (sample a N s x) N ≐ ap3 a zero s x :=
  (sample_lookup a N s x N (le_refl N)).eqTrans (congrAp3 a (monus_self N) (.eqRefl _) (.eqRefl _))

theorem ascending_coefficient (a : PR 3) (N s x k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.coefficient (sample a N s x) N k ≐ ap3 a k s x :=
  (sample_lookup a N s x (monus N k) (GaussianMonicResidualRadius.monus_le_left N k)).eqTrans
    (congrAp3 a (Foundations.BoundedSyntaxBackwardInduction.reverse_complement N k hk) (.eqRefl _) (.eqRefl _))

/-- The evaluator normalizes the original constant sample's value; it
does not falsely identify a raw stored coefficient with a canonical code. -/
theorem evaluation_zero (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx]
    evaluate (sample a N s x) qzero ≐ GaussianTranslatedNonconstant.recode (ap3 a zero s x) :=
  (congrAp3 GaussianRationalHorner.hornerF (sample_length a N s x) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalHorner.horner_succ _ qzero N).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (GaussianRationalSyntheticDivision.qmul_zero_right _)
        (sample_constant a N s x)))

theorem sample_coherence (a : PR 3) (N s t x i : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (entry (sample a N s x) i) (entry (sample a N t x) i)
      (unit s+unit t) (unit s*unit t) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticDivision.qsub_congr (sample_lookup a N s x i hi).eqSymm (sample_lookup a N t x i hi).eqSymm)
    (.eqRefl _) (.eqRefl _)
    (GaussianGeneralCoefficientNames.coherence a N (monus N i) s t x hCN (GaussianMonicResidualRadius.monus_le_left N i))

theorem sample_coefficient_bound (a : PR 3) (N s x i : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    bounded (entry (sample a N s x) i) (monus (GaussianCoefficientNameBounds.A a (succ N) x) one) one :=
  GaussianRationalReciprocal.bound_congr (sample_lookup a N s x i hi).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.sample_bound a (succ N) x (monus N i) s hCN
      ((succ_monus_succ _ _).eqTrans (GaussianMonicResidualRadius.monus_le_left N i)))

/-- The exact source B=2+ceil(||a_0(0)||_1) bounds the actual zero
evaluation at every precision, with no supplied initial residual bound. -/
theorem sample_initial_bound (a : PR 3) (N s x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) : Γ ⊢[PRAAx]
    bounded (evaluate (sample a N s x) qzero) (GaussianGeneralFTAConstants.B a x) one := by
  have distance := GaussianCoefficientNameBounds.sample_zero_distance a (succ N) x zero s hCN (zero_lt_succ N)
  have bound := GaussianReconstructionRoots.norm_from_distance _ _ two one (GaussianGeneralFTAConstants.ceilL1 (ap3 a zero zero x)) one
    (le_refl one) (le_refl one) distance (GaussianGeneralFTAConstants.ceil_norm_bound _)
  have actual : Γ ⊢[PRAAx] bounded (ap3 a zero s x) (GaussianGeneralFTAConstants.B a x) one :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _)
      (by unfold GaussianGeneralFTAConstants.B GaussianGeneralFTAConstants.initial; ipra_ring) (one_mul one) bound
  have value := (GaussianRationalProductWitness.qnormSq_congr (evaluation_zero (Γ := Γ) a N s x)).eqTrans
    (GaussianRationalRelativeTwoTerm.norm_recode _)
  exact RationalArgmin.rationalLE_congr value.eqSymm (.eqRefl _) actual

theorem sample_lower (a : PR 3) (N k h s x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hkN : Γ ⊢[PRAAx] le k N)
    (hApart : Γ ⊢[PRAAx] apart a k h x) (hs : Γ ⊢[PRAAx] le (referencePrecision h) s) : Γ ⊢[PRAAx]
    GaussianNonmonicTravelCoefficientBound.lowerBound (sample a N s x) N k one (lambdaDenominator h) :=
  RationalArgmin.rationalLE_congr (.eqRefl _)
    (GaussianRationalProductWitness.qnormSq_congr (ascending_coefficient a N s x k hkN)).eqSymm
    (GaussianGeneralCoefficientNames.apart_tail a N k h s x hCN hkN hApart hs)

theorem sample_nonconstant (a : PR 3) (N k h s x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hApart : Γ ⊢[PRAAx] apart a k h x) (hs : Γ ⊢[PRAAx] le (referencePrecision h) s) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.nonconstant (sample a N s x) N :=
  GaussianNonmonicTravelCoefficientBound.original_nonconstant _ _ _ _ _ hk hkN (le_refl one)
    (GaussianGeneralCoefficientNames.lambda_denominator_positive h) (sample_lower a N k h s x hCN hkN hApart hs)

theorem sample_coefficient_input (a : PR 3) (N k h s x z U V : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hApart : Γ ⊢[PRAAx] apart a k h x) (hs : Γ ⊢[PRAAx] le (referencePrecision h) s)
    (hV : Γ ⊢[PRAAx] le one V) (hVU : Γ ⊢[PRAAx] le V U) (hz : Γ ⊢[PRAAx] bounded z U V) : Γ ⊢[PRAAx]
    GaussianNonmonicStepBound.coefficientInput (sample a N s x) N z U V k one (lambdaDenominator h) :=
  .andI (.andI (sample_length a N s x) (.andI (le_trans hk hkN) (.andI hV (.andI hVU hz))))
    (.andI hk (.andI hkN (.andI (le_refl one) (.andI (GaussianGeneralCoefficientNames.lambda_denominator_positive h)
      (sample_lower a N k h s x hCN hkN hApart hs)))))

/-- All N+1 coefficient comparisons, including the actual leading sample,
instantiate the proved general Horner perturbation interface. -/
theorem all_coefficient_coherence (a : PR 3) (N s t x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) : Γ ⊢[PRAAx]
    GaussianRationalAllCoefficientPerturbation.coefficientErrors (sample a N s x) (sample a N t x) N
      (unit s+unit t) (unit s*unit t) := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] generalCN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralCoefficientNames.subst_generalCN,Syn.shift] using hCN.shift
  simpa only [Syn.shift,subst_sample,GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul] using
    sample_coherence a (Syn.shift N) (Syn.shift s) (Syn.shift t) (Syn.shift x) (var 0) hs.wk Prf.hyp0

theorem tail_lower (a : PR 3) (N k h s x : PTm n)
    (hInput : Γ ⊢[PRAAx] sourceInput a N k h x) (hs : Γ ⊢[PRAAx] le (referencePrecision h) s) : Γ ⊢[PRAAx]
    GaussianNonmonicTravelCoefficientBound.lowerBound (sample a N s x) N k one (lambdaDenominator h) :=
  sample_lower a N k h s x (Prf.andE₁ hInput) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hInput)))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hInput))) hs
theorem tail_nonconstant (a : PR 3) (N k h s x : PTm n)
    (hInput : Γ ⊢[PRAAx] sourceInput a N k h x) (hs : Γ ⊢[PRAAx] le (referencePrecision h) s) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.nonconstant (sample a N s x) N :=
  sample_nonconstant a N k h s x (Prf.andE₁ hInput) (Prf.andE₁ (Prf.andE₂ hInput))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hInput))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hInput))) hs
theorem tail_coefficient_input (a : PR 3) (N k h s x z U V : PTm n)
    (hInput : Γ ⊢[PRAAx] sourceInput a N k h x) (hs : Γ ⊢[PRAAx] le (referencePrecision h) s)
    (hV : Γ ⊢[PRAAx] le one V) (hVU : Γ ⊢[PRAAx] le V U) (hz : Γ ⊢[PRAAx] bounded z U V) : Γ ⊢[PRAAx]
    GaussianNonmonicStepBound.coefficientInput (sample a N s x) N z U V k one (lambdaDenominator h) :=
  sample_coefficient_input a N k h s x z U V (Prf.andE₁ hInput) (Prf.andE₁ (Prf.andE₂ hInput))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hInput))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hInput))) hs hV hVU hz

def sampleF (a : PR 3) : PR 3 := PTm.toPR (sample a (var 0) (var 1) (var 2))
theorem program_at (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx] ap3 (sampleF a) N s x ≐ sample a N s x := by
  simpa [sampleF,ap3] using toPR_eq (Γ := Γ) (sample a (var 0) (var 1) (var 2) : PTm 3) ![N,s,x]
theorem returned_length (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx] length (ap3 (sampleF a) N s x) ≐ succ N :=
  (congrFst (program_at a N s x)).eqTrans (sample_length a N s x)
theorem returned_lookup (a : PR 3) (N s x i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (ap3 (sampleF a) N s x) i ≐ ap3 a (monus N i) s x :=
  (Foundations.SequenceComposition.entry_congr (program_at a N s x) (.eqRefl _)).eqTrans (sample_lookup a N s x i hi)
theorem returned_leading (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx]
    entry (ap3 (sampleF a) N s x) zero ≐ ap3 a N s x :=
  (Foundations.SequenceComposition.entry_congr (program_at a N s x) (.eqRefl _)).eqTrans (sample_leading a N s x)
theorem returned_evaluation_zero (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx]
    evaluate (ap3 (sampleF a) N s x) qzero ≐ GaussianTranslatedNonconstant.recode (ap3 a zero s x) :=
  (GaussianRationalTranslation.evaluate_congr (program_at a N s x) (.eqRefl _)).eqTrans (evaluation_zero a N s x)

theorem sampled_general_polynomial_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (sample a (var 0) (var 1) (var 2)) ≐ succ (var 0)) ⋏
      ((entry (sample a (var 0) (var 1) (var 2)) zero ≐ ap3 a (var 0) (var 1) (var 2)) ⋏
        (le (var 3) (var 0) ⟶ entry (sample a (var 0) (var 1) (var 2)) (var 3) ≐
          ap3 a (monus (var 0) (var 3)) (var 1) (var 2)))) :=
  closeUniv 4 (.andI (sample_length _ _ _ _) (.andI (sample_leading _ _ _ _) (.impI (sample_lookup _ _ _ _ _ Prf.hyp0))))
theorem sampled_general_zero_evaluation_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (sample a (var 0) (var 1) (var 2)) qzero ≐ GaussianTranslatedNonconstant.recode (ap3 a zero (var 1) (var 2))) :=
  closeUniv 3 (evaluation_zero _ _ _ _)
theorem sampled_general_initial_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (generalCN a (var 0) (var 2) ⟶ bounded (evaluate (sample a (var 0) (var 1) (var 2)) qzero)
      (GaussianGeneralFTAConstants.B a (var 2)) one) :=
  closeUniv 3 (.impI (sample_initial_bound _ _ _ _ Prf.hyp0))
theorem sampled_general_nonconstant_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 4) ⟶ le (referencePrecision (var 2)) (var 3) ⟶
      GaussianBalancedRadiusSyntax.nonconstant (sample a (var 0) (var 3) (var 4)) (var 0)) :=
  closeUniv 5 (.impI (.impI (tail_nonconstant _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem sampled_general_step_coefficient_input_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (sourceInput a (var 0) (var 1) (var 2) (var 4) ⟶ le (referencePrecision (var 2)) (var 3) ⟶
      le one (var 7) ⟶ le (var 7) (var 6) ⟶ bounded (var 5) (var 6) (var 7) ⟶
      GaussianNonmonicStepBound.coefficientInput (sample a (var 0) (var 3) (var 4)) (var 0) (var 5) (var 6) (var 7)
        (var 1) one (lambdaDenominator (var 2))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (tail_coefficient_input _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem sampled_general_coherence_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (generalCN a (var 0) (var 3) ⟶ GaussianRationalAllCoefficientPerturbation.coefficientErrors
      (sample a (var 0) (var 1) (var 3)) (sample a (var 0) (var 2) (var 3)) (var 0)
        (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2))) :=
  closeUniv 4 (.impI (all_coefficient_coherence _ _ _ _ _ Prf.hyp0))
theorem general_sample_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (sampleF a) (var 0) (var 1) (var 2) ≐ sample a (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _ _)
theorem returned_general_lookup_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 0) ⟶ entry (ap3 (sampleF a) (var 0) (var 1) (var 2)) (var 3) ≐ ap3 a (monus (var 0) (var 3)) (var 1) (var 2)) :=
  closeUniv 4 (.impI (returned_lookup _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples
