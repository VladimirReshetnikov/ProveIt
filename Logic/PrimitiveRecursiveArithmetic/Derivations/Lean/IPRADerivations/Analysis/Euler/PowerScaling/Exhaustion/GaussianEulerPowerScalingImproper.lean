import IPRADerivations.Analysis.Euler.PowerScaling.Observations.GaussianEulerPowerScalingCofinalObservation

/-!
# The improper Euler integral with positive rational power damping

The sampler evaluates the original ordinary compact pullback at the
cofinal cutoffs and at its paid clock. It agrees at independent
observation indices with the actual Gamma name at the rescaled argument,
multiplied by the inverse power of the damping constant and by f/e.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingImproper

open_ipra
open GaussianEulerPowerChartCofinalSchedule (source)
open GaussianEulerPowerScalingCofinalObservation (observation grid)
open GaussianEulerCompactExhaustionNormalization (referenceClock)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianPositiveRationalLogarithm (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev resultF : PR 2 := GaussianEulerCompactExhaustionNormalization.nameF
abbrev resultData (z R B A e f d h L Q : PTm n) : PTm n :=
  GaussianEulerCompactExhaustionNormalization.data z R B A e f d h L Q

def sample (p z R B A e f d h L Q S : PTm n) : PTm n :=
  observation (referenceClock p L) z R B A e f d h L Q S

def data (z R B A e f d h L Q S : PTm n) : PTm n :=
  Foundations.BoundedSyntax.pack (![z,R,B,A,e,f,d,h,L,Q,S] : Fin 11 → PTm n)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B A e f d h L Q S : PTm n) :
    Syn.subst σ (data z R B A e f d h L Q S) = data (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d)
      (Syn.subst σ h) (Syn.subst σ L) (Syn.subst σ Q) (Syn.subst σ S) := by
  unfold data
  rw [Foundations.BoundedSyntax.subst_pack]
  congr 1
  funext i
  fin_cases i <;> rfl

ipra_subst resultData [GaussianEulerCompactExhaustionNormalization.data,
    GaussianEulerCompactExhaustionScaled.referenceData, GaussianEulerPowerScalingParameter.scaled]

ipra_subst source [GaussianEulerPowerScalingParameter.source]

private theorem subst_grid_span_clock {m : ℕ} (σ : Fin n → PTm m) (s z R B A e f d h L Q S : PTm n) :
    let G := grid s z R B A e f d h L Q S
    let G' := grid (Syn.subst σ s) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A)
      (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ L) (Syn.subst σ Q) (Syn.subst σ S)
    Syn.subst σ G.stage = G'.stage ∧
      Syn.subst σ G.span = G'.span ∧ Syn.subst σ G.lower = G'.lower ∧ Syn.subst σ G.upper = G'.upper := by
  simp [grid,GaussianEulerPowerChartCofinalSchedule.cutoffSize,GaussianEulerPowerChartCofinalSchedule.samplingIndex,
    GaussianEulerPowerChartCofinalEndpoints.width,GaussianEulerPowerChartCofinalEndpoints.lowerDenominator,
    GaussianEulerPowerChartCofinalEndpoints.upperNumerator,GaussianGammaIntegralCutoffs.etaDen,
    GaussianGammaIntegralCutoffs.top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient,
    GaussianEulerCompactExhaustionScaled.cutoff,GaussianEulerCompactExhaustionScaled.clock,
    GaussianEulerCompactExhaustionScaled.cutoffGain,GaussianEulerCompactExhaustionScaled.samplingGain,
    GaussianEulerCompactExhaustion.budget,GaussianEulerPowerScalingCell.scaleBound,GaussianEulerPowerScalingParameter.scaled,
    GaussianEulerPositivePowerChartImageSchedule.target,GaussianEulerPositivePowerChartImageSchedule.boost,
    GaussianEulerPositivePowerChartImageBudget.meshBudget,GaussianEulerPositivePowerChartImageBudget.tiltBudget,
    GaussianEulerPositivePowerChartImageBudget.observationBudget,GaussianEulerPositivePowerChartImageName.panelTop,
    GaussianEulerPositivePowerChartImageName.panelModulus]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B A e f d h L Q S : PTm n) :
    Syn.subst σ (sample p z R B A e f d h L Q S) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d)
      (Syn.subst σ h) (Syn.subst σ L) (Syn.subst σ Q) (Syn.subst σ S) := by
  have clock : Syn.subst σ (referenceClock p L) = referenceClock (Syn.subst σ p) (Syn.subst σ L) :=
    GaussianBoundedConstantProductName.subst_clock σ p L
  have fields := subst_grid_span_clock σ (referenceClock p L) z R B A e f d h L Q S
  rw [clock] at fields
  simp only [sample,observation,GaussianEulerPowerScalingCompactName.data,subst_ap2,
    GaussianCompactRiemannName.subst_data,GaussianEulerPowerScalingCompactRate.subst_lipschitz,
    GaussianEulerPowerScalingCompactName.subst_fixedData,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]

private def fields (p x : PTm n) : Fin 12 → PTm n :=
  Fin.cases p (fun j => Foundations.BoundedFormulas.at1 (Foundations.BoundedSyntax.projections 11 j) x)
private def body : PTm 12 :=
  sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
def reader (f : PTm 12) (p x : PTm n) : PTm n := Syn.subst (fields p x) f
def nameF : PR 2 := PTm.toPR (reader body (var 0) (var 1))

theorem reader_at (g : PTm 12) (p z R B A e f d h L Q S : PTm n) :
    Γ ⊢[PRAAx] ap2 (PTm.toPR (reader g (var 0) (var 1))) p (data z R B A e f d h L Q S) ≐
      Syn.subst (Fin.cases p (![z,R,B,A,e,f,d,h,L,Q,S] : Fin 11 → PTm n)) g := by
  let xs : Fin 11 → PTm n := ![z,R,B,A,e,f,d,h,L,Q,S]
  let x := data z R B A e f d h L Q S
  have compiled : Syn.subst (![p,x] : Fin 2 → PTm n) (reader g (var 0) (var 1)) = reader g p x := by
    unfold reader
    rw [Syn.subst_subst]
    congr 1
    funext i
    cases i using Fin.cases with
    | zero => simp [fields]
    | succ i =>
      simp only [fields,Fin.cases_succ,Foundations.BoundedFormulas.at1,Syn.subst_subst]
      congr 1
      funext j
      fin_cases j
      rfl
  have readable : Γ ⊢[PRAAx] ap2 (PTm.toPR (reader g (var 0) (var 1))) p x ≐ reader g p x := by
    simpa only [ap2,compiled] using toPR_eq (Γ := Γ) (reader g (var 0) (var 1) : PTm 2) ![p,x]
  refine readable.eqTrans (Prf.eqCongr g (fun i => ?_))
  cases i using Fin.cases with
  | zero => exact .eqRefl _
  | succ i => exact Foundations.BoundedSyntax.projections_pack xs i

theorem name_at (p z R B A e f d h L Q S : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B A e f d h L Q S) ≐ sample p z R B A e f d h L Q S := by
  have decode : Syn.subst (Fin.cases p (![z,R,B,A,e,f,d,h,L,Q,S] : Fin 11 → PTm n)) body =
      sample p z R B A e f d h L Q S := by
    simp only [body,subst_sample,Syn.subst_var]
    rfl
  simpa only [nameF,decode] using reader_at body p z R B A e f d h L Q S

theorem original_observations (p q z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A e f d h L Q S)) (ap2 resultF q (resultData z R B A e f d h L Q))
      (unit p+unit q) (unit p*unit q) :=
  distance_congr (name_at p z R B A e f d h L Q S).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianEulerPowerScalingCofinalObservation.original_observations p q z R B A e f d h L Q S hs)

theorem original_cross (z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) : Γ ⊢[PRAAx]
    crossEquivalent nameF resultF (data z R B A e f d h L Q S) (resultData z R B A e f d h L Q) := by
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A)
      (sh e) (sh f) (sh d) (sh h) (sh L) (sh Q) (sh S) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,Syn.shift,subst_data,subst_resultData,sh] using
    original_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh A) (sh e) (sh f) (sh d) (sh h) (sh L) (sh Q) (sh S) ss

theorem name_regular (z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B A e f d h L Q S) := by
  have identification := original_cross z R B A e f d h L Q S hs
  exact cross_trans _ _ _ _ _ _ identification (cross_symm _ _ _ _ identification)

abbrev formulaF : PR 2 := multiplyF constantF GaussianEulerCompactExhaustionScaled.referenceF
def formulaData (z R B A e f d h L Q : PTm n) : PTm n :=
  multiplyData constantF GaussianEulerCompactExhaustionScaled.referenceF (fraction f e)
    (GaussianEulerCompactExhaustionScaled.referenceData z R B A e f d h L Q)

/-- The target is the actual product of the rational coefficient f/e and
the original inverse-power/Gamma product at the rescaled argument. -/
theorem original_Gamma_formula (z R B A e f d h L Q S : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q S) : Γ ⊢[PRAAx]
    crossEquivalent nameF formulaF (data z R B A e f d h L Q S) (formulaData z R B A e f d h L Q) := by
  have reference := GaussianEulerCompactExhaustionScaled.reference_regular
    z R B A e f d h L Q hs.andE₁ hs.andE₂.andE₂.andE₁
  have inverse := GaussianEulerCompactExhaustionNormalization.inverse_bound e f L
    hs.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  exact cross_trans _ _ _ _ _ _ (original_cross z R B A e f d h L Q S hs)
    (GaussianBoundedConstantProductName.ordinary_product_identity GaussianEulerCompactExhaustionScaled.referenceF L
      (fraction f e) (GaussianEulerCompactExhaustionScaled.referenceData z R B A e f d h L Q) (.andI reference inverse))

def positiveSource (z R B A e f d h : PTm n) : Fm PTm n :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏ ((le one e ⋏ le one f) ⋏ (le one d ⋏ le one h))

theorem positive_source (z R B A e f d h : PTm n) (hs : Γ ⊢[PRAAx] positiveSource z R B A e f d h) :
    Γ ⊢[PRAAx] source z R B A e f d h f e d := by
  have he := hs.andE₂.andE₁.andE₁
  have hf := hs.andE₂.andE₁.andE₂
  have hd := hs.andE₂.andE₂.andE₁
  have hh := hs.andE₂.andE₂.andE₂
  have hfa : Γ ⊢[PRAAx] le f (f*e) := le_congr (one_mul f) (mul_comm e f) (mul_le_mul_right f he)
  have hea : Γ ⊢[PRAAx] le e (e*f) := le_congr (one_mul e) (mul_comm f e) (mul_le_mul_right e hf)
  have hda : Γ ⊢[PRAAx] le d (d*h) := le_congr (one_mul d) (mul_comm h d) (mul_le_mul_right d hh)
  exact .andI (.andI hs.andE₁ (.andI he (.andI hf (.andI hf (.andI he (.andI hfa hea))))))
    (.andI (.andI he hf) (.andI (.andI hd hh) (.andI (.andI he hd) (.andI hea hda))))

theorem actual_original_rational_power_damped_Euler_improper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      crossEquivalent nameF resultF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
        (var 8) (var 9) (var 10)) (resultData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))) :=
  closeUniv 11 (.impI (original_cross _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_positive_rational_power_damped_Euler_improper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (positiveSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      crossEquivalent nameF resultF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
        (var 5) (var 4) (var 6)) (resultData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 5) (var 4))) :=
  closeUniv 8 (.impI (original_cross _ _ _ _ _ _ _ _ _ _ _ (positive_source _ _ _ _ _ _ _ _ Prf.hyp0)))

theorem actual_original_positive_rational_power_damped_Euler_is_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (positiveSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      crossEquivalent nameF formulaF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
        (var 5) (var 4) (var 6)) (formulaData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
        (var 5) (var 4))) :=
  closeUniv 8 (.impI (original_Gamma_formula _ _ _ _ _ _ _ _ _ _ _ (positive_source _ _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingImproper
