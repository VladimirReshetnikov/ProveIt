import IPRADerivations.Analysis.Euler.PowerScaling.Named.GaussianEulerNamedPowerScalingFormulaFrozen
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerCompactPaid
import IPRADerivations.Analysis.Euler.PowerScaling.Observations.GaussianEulerPowerScalingUniformObservation
import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativePrecision

/-!
# Comparing the actual named cutoff sampler to the named Gamma formula

Each observation uses the ordinary named compact sampler on a physical
panel determined before either parameter is frozen. A uniform rational
comparison on this panel transfers to the named formula with two
independent dyadic observation errors.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingCutoff

open_ipra
open GaussianEulerNamedPowerScalingFormula (source powerF powerData)
open GaussianEulerNamedPowerScalingFormulaFrozen (freezeClock frozenData)
open GaussianEulerNamedPowerScalingPowerFrozen (powerClock frozenPowerData frozen_sample_bound)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator width)
open GaussianEulerPowerChartUniformSchedule (cutoffIndex)
open GaussianNamedDampingPowerCompactPaid (parameterClock rationalNameData)
open GaussianEulerPowerScalingImproper (formulaF)
open GaussianEulerPowerScalingKernel (scaleExpF)
open GaussianFastValueCut (exponent query_budget)
open GaussianNameBounds (U)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem frozen_power_bound (F G : PR 2) (k z R B A x E T y H J : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J)
    (hk : Γ ⊢[PRAAx] le (powerClock F G zero z R B x E y H) k) :
    Γ ⊢[PRAAx] sampleBound scaleExpF (frozenPowerData F G k z B x y)
      (U (powerF F G) (powerData F G z R B x E y H)+num 3) := by
  have lin := GaussianEulerNamedPowerScalingParameter.regular G z R B A y H J hs.andE₁
  have log := GaussianNamedPositiveLogarithm.name_regular F x E T hs.andE₂
  have exp := GaussianNameRingLaws.negative_fast _ _ (GaussianNameArithmetic.multiply_fast _ _ _ _ lin log)
  have reg : Γ ⊢[PRAAx] pointCN (powerF F G) (powerData F G z R B x E y H) :=
    GaussianRadiusExponentialName.name_regular _ _ _
      (GaussianGammaFiniteApproximantName.exponential_input _ _ exp)
  exact frozen_sample_bound _ _ _ _ zero reg
    (GaussianEulerNamedPowerScalingPowerFrozen.original_independent_rate F G zero k z R B A x E T y H J hs hk)

def outputPrecision (p : PTm n) : PTm n := exponent (num 6) p

def panelSize (s R A H J M : PTm n) : PTm n :=
  GaussianEulerPowerChartCofinalSchedule.cutoffSize (cutoffIndex s (J*A) (H*R) H M) (J*A) (H*R)

def compactData (s z R B A x E T y H J M : PTm n) : PTm n :=
  let V := panelSize s R A H J M
  GaussianNamedDampingPowerCompact.data z R B x y T J one (width H E T V)
    (lowerDenominator T V H) (upperNumerator E V H)

def rationalCompactData (F G : PR 2) (s k z R B A x E T y H J M : PTm n) : PTm n :=
  GaussianEulerPowerScalingUniformObservation.compactData s z R B A
    (GaussianNamedPositiveLogarithm.numerator G k y) (GaussianNamedPositiveLogarithm.denominator G k y)
    (GaussianNamedPositiveLogarithm.numerator F k x) (GaussianNamedPositiveLogarithm.denominator F k x) H J T E M

def sample (F G : PR 2) (p z R B A x E T y H J M : PTm n) : PTm n :=
  ap2 (GaussianNamedDampingPowerCompact.nameF F G) (outputPrecision p)
    (compactData (outputPrecision p) z R B A x E T y H J M)

def data (z R B A x E T y H J M : PTm n) : PTm n :=
  Foundations.BoundedSyntax.pack (![z,R,B,A,x,E,T,y,H,J,M] : Fin 11 → PTm n)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B A x E T y H J M : PTm n) :
    Syn.subst σ (data z R B A x E T y H J M) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A)
      (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ y) (Syn.subst σ H) (Syn.subst σ J)
      (Syn.subst σ M) := by
  unfold data
  rw [Foundations.BoundedSyntax.subst_pack]
  congr 1
  funext i
  fin_cases i <;> rfl

ipra_subst panelSize [GaussianEulerPowerChartCofinalSchedule.cutoffSize, GaussianGammaIntegralCutoffs.etaDen,
    GaussianGammaIntegralCutoffs.top, GaussianGammaIntegralCutoffs.height,
    GaussianGammaIntegralCutoffs.tailCoefficient]

ipra_subst compactData [width, lowerDenominator, upperNumerator]

ipra_subst rationalCompactData [GaussianNamedPositiveLogarithm.numerator, GaussianNamedPositiveLogarithm.denominator]

ipra_subst sample [outputPrecision]

private def fields (p x : PTm n) : Fin 12 → PTm n :=
  Fin.cases p (fun j => Foundations.BoundedFormulas.at1 (Foundations.BoundedSyntax.projections 11 j) x)
private def body (F G : PR 2) : PTm 12 :=
  sample F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
private def reader (f : PTm 12) (p x : PTm n) : PTm n := Syn.subst (fields p x) f
def nameF (F G : PR 2) : PR 2 := PTm.toPR (reader (body F G) (var 0) (var 1))

private theorem reader_at (g : PTm 12) (p z R B A x E T y H J M : PTm n) :
    Γ ⊢[PRAAx] ap2 (PTm.toPR (reader g (var 0) (var 1))) p (data z R B A x E T y H J M) ≐
      Syn.subst (Fin.cases p (![z,R,B,A,x,E,T,y,H,J,M] : Fin 11 → PTm n)) g := by
  let xs : Fin 11 → PTm n := ![z,R,B,A,x,E,T,y,H,J,M]
  let w := data z R B A x E T y H J M
  have compiled : Syn.subst (![p,w] : Fin 2 → PTm n) (reader g (var 0) (var 1)) = reader g p w := by
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
  have readable : Γ ⊢[PRAAx] ap2 (PTm.toPR (reader g (var 0) (var 1))) p w ≐ reader g p w := by
    simpa only [ap2,compiled] using toPR_eq (Γ := Γ) (reader g (var 0) (var 1) : PTm 2) ![p,w]
  refine readable.eqTrans (Prf.eqCongr g (fun i => ?_))
  cases i using Fin.cases with
  | zero => exact .eqRefl _
  | succ i => exact Foundations.BoundedSyntax.projections_pack xs i

theorem name_at (F G : PR 2) (p z R B A x E T y H J M : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF F G) p (data z R B A x E T y H J M) ≐ sample F G p z R B A x E T y H J M := by
  have decode : Syn.subst (Fin.cases p (![z,R,B,A,x,E,T,y,H,J,M] : Fin 11 → PTm n)) (body F G) =
      sample F G p z R B A x E T y H J M := by
    simp only [body,subst_sample,Syn.subst_var]
    rfl
  simpa only [nameF,decode] using reader_at (body F G) p z R B A x E T y H J M

theorem compact_source (F G : PR 2) (s z R B A x E T y H J M : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J) : Γ ⊢[PRAAx]
    GaussianNamedDampingPowerCompact.source F G z R B x y E T H J one (width H E T (panelSize s R A H J M))
      (lowerDenominator T (panelSize s R A H J M) H) (upperNumerator E (panelSize s R A H J M) H) := by
  let V := panelSize s R A H J M
  let t := cutoffIndex s (J*A) (H*R) H M
  have d := GaussianNamedPositiveLogarithm.decoded_domain F zero x E T hs.andE₂
  have hT := GaussianDominantScalarOrder.factor_positive_left T (GaussianNamedPositiveLogarithm.denominator F zero x)
    (le_trans d.andE₁.andE₁ d.andE₂.andE₂)
  have hV : Γ ⊢[PRAAx] le two V := (GaussianEulerPowerChartCofinalSchedule.cutoff_guards t (J*A) (H*R)).andE₁
  have cert := GaussianEulerPowerChartUniformEndpoints.uniform_physical_panel T H E V hT
    hs.andE₁.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₁ hV
  have base := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  exact .andI (.andI (.andI base.andE₁ (.andI cert.andE₁ base.andE₂))
    (.andI (le_refl one) (le_congr cert.andE₂.andE₂.andE₂.eqSymm (mul_comm _ _) (le_refl _))))
    (.andI hs.andE₂ hs.andE₁.andE₂.andE₂)

def frozenIndex (F G : PR 2) (s z R B A x E T y H J M : PTm n) : PTm n :=
  let V := panelSize s R A H J M
  parameterClock s R T J (lowerDenominator T V H) (upperNumerator E V H)+
    freezeClock F G s z R B A x E y H J+powerClock F G zero z R B x E y H

ipra_subst frozenIndex [parameterClock, GaussianNamedDampingPowerFrozen.budget, lowerDenominator, upperNumerator, GaussianNamedDampingPowerIntegrand.gain, GaussianNamedDampingPowerIntegrand.decayBound, GaussianNamedDampingPowerChart.gain, GaussianNamedDampingPowerChart.majorant, GaussianCompactLogarithmBounds.radius, one]

theorem freeze_power_clock (F G : PR 2) (s z R B A x E T y H J M : PTm n) : Γ ⊢[PRAAx]
    le (powerClock F G zero z R B x E y H) (frozenIndex F G s z R B A x E T y H J M) := le_add_left _ _

def rationalInputAt (F G : PR 2) (s z R B A x E T y H J M : PTm n) : Fm PTm n :=
  let k := frozenIndex F G s z R B A x E T y H J M
  independentRate GaussianEulerPowerScalingCompactName.nameF formulaF
    (rationalCompactData F G s k z R B A x E T y H J M) (frozenData F G k z R B A x y H J) one (unit s)

def rationalInput (F G : PR 2) (z R B A x E T y H J M : PTm n) : Fm PTm n := .all
  (rationalInputAt F G (var 0) (shift z) (shift R) (shift B) (shift A) (shift x) (shift E) (shift T)
    (shift y) (shift H) (shift J) (shift M))

ipra_subst rationalInputAt

ipra_subst rationalInput [Syn.subst_shift, Syn.shift_subst]

private theorem rational_input_at (F G : PR 2) (s z R B A x E T y H J M : PTm n)
    (hr : Γ ⊢[PRAAx] rationalInput F G z R B A x E T y H J M) : Γ ⊢[PRAAx]
    rationalInputAt F G s z R B A x E T y H J M := by
  simpa only [rationalInput,subst_rationalInputAt,Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift]
    using hr.allE s

theorem original_observations (F G : PR 2) (p q z R B A x E T y H J M : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J)
    (hr : Γ ⊢[PRAAx] rationalInputAt F G (outputPrecision p) z R B A x E T y H J M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF F G) p (data z R B A x E T y H J M))
      (ap2 (GaussianEulerNamedPowerScalingFormula.nameF F G) q (GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J))
      (unit p+unit q) (unit p*unit q) := by
  let s := outputPrecision p
  let V := panelSize s R A H J M
  let D := lowerDenominator T V H
  let T' := upperNumerator E V H
  let W := width H E T V
  let a := parameterClock s R T J D T'
  let b := freezeClock F G s z R B A x E y H J
  let c := powerClock F G zero z R B x E y H
  let k := frozenIndex F G s z R B A x E T y H J M
  let Y := rationalCompactData F G s k z R B A x E T y H J M
  let X := frozenData F G k z R B A x y H J
  let N := GaussianEulerNamedPowerScalingFormula.nameF F G
  let u := GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J
  let S := unit s
  let Q := unit q
  let L := S*Q
  have hS := unit_positive (Γ := Γ) s
  have hQ := unit_positive (Γ := Γ) q
  have hL := positive_product _ _ hS hQ
  have ka : Γ ⊢[PRAAx] le a k := le_trans (le_add_right a b) (le_add_right (a+b) c)
  have kb : Γ ⊢[PRAAx] le b k := le_trans (le_add_left b a) (le_add_right (a+b) c)
  have A₀ := GaussianNamedDampingPowerCompactPaid.original_paid_observations F G s k z R B x y E T H J one W D T'
    (compact_source F G s z R B A x E T y H J M hs) ka
  have A₁ := distance_congr (name_at F G p z R B A x E T y H J M).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) A₀
  have numB : Γ ⊢[PRAAx] le (num 9*S) (unit (s+num 6)) := by
    have wide := GaussianEulerDerivativePrecision.total_budget (Γ := Γ) s
    have small : Γ ⊢[PRAAx] le (num 9*S) (num 13*S) :=
      mul_le_mul_right S (le_of_eq_add (d := num 4) (by ipra_ring))
    exact le_trans small wide
  have left := distance_radius_mono _ _ _ _ Q L (unit_positive (s+num 6)) hL
    (le_congr (by dsimp only [L]; ipra_ring) (by ipra_ring) (mul_le_mul_right Q numB)) A₁
  have mid₀ := rate_at GaussianEulerPowerScalingCompactName.nameF formulaF Y X one S s s hr
  have middle := distance_radius_mono _ _ _ _ (num 3*Q) L
    (denominator_positive _ _ _ hS) hL
    (le_of_eq_add (d := zero) (by dsimp only [L,S,rateNumerator,rateDenominator]; ipra_ring)) mid₀
  have right₀ := rate_at N formulaF u X one S q s
    (GaussianEulerNamedPowerScalingFormulaFrozen.original_independent_rate F G s k z R B A x E T y H J hs kb)
  have right₁ := distance_symmetric _ _ _ _ (denominator_positive _ _ _ hS) right₀
  have right := distance_radius_mono _ _ _ _ (two*Q+S) L
    (denominator_positive _ _ _ hS) hL
    (le_of_eq_add (d := zero) (by dsimp only [L,S,Q,rateNumerator,rateDenominator]; ipra_ring)) right₁
  have joined := distance_triangle_same _ _ _ _ _ L hL (distance_triangle_same _ _ _ _ _ L hL left middle) right
  exact distance_radius_mono _ _ _ _ _ _ hL (positive_product _ _ (unit_positive p) hQ) (by
    dsimp only [L,S,Q,s,outputPrecision]
    ipra_le 𝔞(unit q*unit q)*sl (query_budget (num 6) p)) joined

theorem original_cross (F G : PR 2) (z R B A x E T y H J M : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z R B A x E T y H J)
    (hr : Γ ⊢[PRAAx] rationalInput F G z R B A x E T y H J M) : Γ ⊢[PRAAx]
    crossEquivalent (nameF F G) (GaussianEulerNamedPowerScalingFormula.nameF F G) (data z R B A x E T y H J M)
      (GaussianEulerNamedPowerScalingFormula.data F G z R B A x E y H J) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have hs' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source F G (sh z) (sh R) (sh B) (sh A) (sh x) (sh E) (sh T)
      (sh y) (sh H) (sh J) := by simpa [Fm.shift,Syn.shift,sh] using hs.shift.shift
  have hr' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] rationalInput F G (sh z) (sh R) (sh B) (sh A) (sh x) (sh E) (sh T)
      (sh y) (sh H) (sh J) (sh M) := by simpa [Fm.shift,Syn.shift,sh] using hr.shift.shift
  simpa only [crossEquivalent,Syn.shift,subst_data,GaussianEulerNamedPowerScalingFormulaFrozen.subst_named_data,sh] using
    original_observations F G (var 1) (var 0) (sh z) (sh R) (sh B) (sh A) (sh x) (sh E) (sh T) (sh y) (sh H) (sh J) (sh M)
      hs' (rational_input_at F G _ _ _ _ _ _ _ _ _ _ _ _ hr')

theorem conditional_named_power_damped_Euler_is_Gamma_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      ((source F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏
        rationalInput F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)) ⟶
        crossEquivalent (nameF F G) (GaussianEulerNamedPowerScalingFormula.nameF F G)
          (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
          (GaussianEulerNamedPowerScalingFormula.data F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
            (var 7) (var 8) (var 9))) :=
  closeUniv 11 (.impI (original_cross F G _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingCutoff
