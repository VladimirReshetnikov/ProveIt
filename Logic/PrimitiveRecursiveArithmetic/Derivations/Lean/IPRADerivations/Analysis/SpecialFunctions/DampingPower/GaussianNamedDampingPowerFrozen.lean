import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerIntegrand
import IPRADerivations.Analysis.Names.Approximation.GaussianNamedRationalApproximation

/-!
# Exact frozen rational comparison for the named damped Euler kernel

Freeze both named positive parameters at the same requested index,
using the decoded numerator and denominator of each literal observation.
The original rational power-damped kernel agrees with this frozen
instance. Its error from the named kernel is uniform in the compact
time interval and retains both independent observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerFrozen

open_ipra
open GaussianNamedDampingPowerIntegrand (source nameF data gain)
open GaussianNamedPositiveLogarithm (numerator denominator)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (canonical)
open GaussianNamedInverseRate (independentRate)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (F : PR 2) (k x : PTm n) : PTm n := fraction (numerator F k x) (denominator F k x)
def budget (Rz C R E T : PTm n) : PTm n := gain Rz C R E T one one zero
def rationalData (F G : PR 2) (k z B x y C a b : PTm n) : PTm n :=
  GaussianEulerPowerScalingCompactRate.data z B (numerator G k y) (denominator G k y)
    (numerator F k x) (denominator F k x) C a b

private def sampleGuard (q E T : PTm n) : Fm PTm n :=
  canonical q ⋏ GaussianPositiveCompactInputDecoding.source q E T

@[simp] private theorem subst_sampleGuard {m : ℕ} (σ : Fin n → PTm m) (q E T : PTm n) :
    (sampleGuard q E T).subst σ = sampleGuard (Syn.subst σ q) (Syn.subst σ E) (Syn.subst σ T) := by simp [sampleGuard]

private theorem constant_source (q E T : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] sampleGuard q E T) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source constantF q E T := by
  refine .andI (constant_regular q) (.andI hE (.allI ?_))
  let sh (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] sampleGuard (sh q) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,subst_sampleGuard,sh] using h.shift
  have eq := constant_at (Γ := Γ.map Fm.shift) (var 0) (sh q)
  have bound : Γ.map Fm.shift ⊢[PRAAx] sampleGuard (ap2 constantF (var 0) (sh q)) (sh E) (sh T) := by
    simpa only [subst_sampleGuard,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqSubst1 (sampleGuard (var 0) (Syn.shift (sh E)) (Syn.shift (sh T))) eq.eqSymm
        (by simpa only [subst_sampleGuard,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hs)
  exact bound

theorem frozen_parameter_source (F : PR 2) (k x E T : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x E T) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source constantF (value F k x) E T := by
  have old : Γ ⊢[PRAAx] sampleGuard (ap2 F k x) E T := GaussianNamedPositiveLogarithm.admissible_at F k x E T hs
  have eq := GaussianNamedPositiveLogarithm.decoded_value F k x E T hs
  apply constant_source _ _ _ hs.andE₂.andE₁
  simpa only [subst_sampleGuard,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,value] using
    Prf.eqSubst1 (sampleGuard (var 0) (Syn.shift E) (Syn.shift T)) eq.eqSymm
      (by simpa only [subst_sampleGuard,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using old)

theorem frozen_parameter_rate (F : PR 2) (k x E T : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x E T) :
    Γ ⊢[PRAAx] independentRate F constantF x (value F k x) one (unit k) := by
  let q := ap2 F k x
  let y := value F k x
  have r := GaussianNamedRationalApproximation.frozen_constant_rate F x k hs.andE₁
  have eq : Γ ⊢[PRAAx] GaussianFastValueCut.recode q ≐ y :=
    (GaussianExponentialReference.recode_fixed q (GaussianNamedPositiveLogarithm.admissible_at F k x E T hs).andE₁).eqTrans
      (GaussianNamedPositiveLogarithm.decoded_value F k x E T hs).eqSymm
  simpa only [GaussianNamedInverseRate.subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 (independentRate F constantF (Syn.shift x) (var 0) (Syn.shift one) (Syn.shift (unit k))) eq
      (by simpa only [GaussianNamedInverseRate.subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using r)

private theorem positive_upper (a b T : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hu : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] le one T := by
  refine .orE (zero_or_succ T) ?_ ?_
  · have z : (T ≐ zero)::Γ ⊢[PRAAx] T*b ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl b)).eqTrans (zero_mul b)
    exact not_succ_le_self zero _ (le_congr (.eqRefl one) z (le_trans ha.wk hu.wk))
  · exact Order.zero_lt_of_eq_succ Prf.hyp0

theorem actual_rational_source (F G : PR 2) (k z Rz B x y C₀ C R₀ R E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R E T a b) :
    Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source (numerator G k y) (denominator G k y)
      (numerator F k x) (denominator F k x) R C E T a b := by
  have lc := GaussianNamedPositiveLogarithm.decoded_domain F k x C₀ C hs.andE₂.andE₁
  have lr := GaussianNamedPositiveLogarithm.decoded_domain G k y R₀ R hs.andE₂.andE₂.andE₁
  have qc := positive_upper _ _ _ lc.andE₁.andE₁ lc.andE₂.andE₂
  have qr := positive_upper _ _ _ lr.andE₁.andE₁ lr.andE₂.andE₂
  exact .andI (.andI lr.andE₁ (.andI lc.andE₁ (.andI (.andI qr qc)
    (.andI lr.andE₂.andE₂ lc.andE₂.andE₂)))) hs.andE₂.andE₂.andE₂

theorem original_frozen_rate (F G : PR 2) (k z Rz B x y C₀ C R₀ R E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R E T a b) :
    Γ ⊢[PRAAx] independentRate (nameF F G) GaussianEulerPowerScalingCompactRate.nameF
      (data F G z B x y a b) (rationalData F G k z B x y C a b) (budget Rz C R E T) (unit k) := by
  let x₀ := value F k x
  let y₀ := value G k y
  let A := data F G z B x y a b
  let B₀ := data constantF constantF z B x₀ y₀ a b
  let D := unit k
  let chart := GaussianNamedDampingPowerChart.data F G x y a b
  have hc := hs.andE₂.andE₁
  have hr := hs.andE₂.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := unit_positive k
  have frozen : Γ ⊢[PRAAx] source constantF constantF z Rz B x₀ y₀ C₀ C R₀ R E T a b :=
    .andI hs.andE₁ (.andI (frozen_parameter_source F k x C₀ C hc)
      (.andI (frozen_parameter_source G k y R₀ R hr) hs.andE₂.andE₂.andE₂))
  have rate : Γ ⊢[PRAAx] independentRate (nameF F G) (nameF constantF constantF) A B₀ (budget Rz C R E T) D :=
    GaussianNamedDampingPowerIntegrand.original_rate F G constantF constantF z Rz B x y x₀ y₀ C₀ C R₀ R E T a b a b
      one one zero D hs frozen hD (frozen_parameter_rate F k x C₀ C hc) (frozen_parameter_rate G k y R₀ R hr)
      (GaussianRationalPowerDifference.distance_refl_zero (fraction a b) D hD)
  have regular := GaussianEulerDampedNamedIntegrand.name_regular (GaussianNamedDampingPowerChart.nameF F G) z B a b chart
    (GaussianNamedDampingPowerChart.name_regular F G x y C₀ C R₀ R E T a b hs.andE₂)
    (.andI hs.andE₁.andE₁ hs.andE₂.andE₂.andE₂.andE₂.andE₁)
  have old := GaussianNamedDampingPowerIntegrand.actual_rational_specialization z B (numerator G k y) (denominator G k y)
    (numerator F k x) (denominator F k x) R C E T a b hs.andE₁.andE₁
    (actual_rational_source F G k z Rz B x y C₀ C R₀ R E T a b hs)
  exact GaussianNamedRateTransport.transport _ _ _ _ A B₀ A _ _ D hD rate (cross_refl _ _ regular)
    (cross_symm _ _ _ _ old)

theorem actual_original_named_damped_Euler_frozen_parameter_rate_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      (source F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
        (var 10) (var 11) (var 12) (var 13) ⟶
        independentRate (nameF F G) GaussianEulerPowerScalingCompactRate.nameF
          (data F G (var 1) (var 3) (var 4) (var 5) (var 12) (var 13))
          (rationalData F G (var 0) (var 1) (var 3) (var 4) (var 5) (var 7) (var 12) (var 13))
          (budget (var 2) (var 7) (var 9) (var 10) (var 11)) (unit (var 0))) :=
  closeUniv 14 (.impI (original_frozen_rate F G _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerFrozen
