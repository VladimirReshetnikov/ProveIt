import IPRADerivations.Analysis.Barnes.CanonicalProducts.FiniteProducts.GaussianBarnesCanonicalBase
import IPRADerivations.Analysis.Trigonometry.Cyclic.ExponentialRoots.GaussianCyclicExponentialSamples

/-!
# Exact zeros and late lower bounds of original Barnes factors

The actual power and exponential observations propagate the native lower
bound of the base at their original clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFactorApartness

open_ipra
open GaussianBarnesCanonicalFactor (base correction exponentialData exponentRadius clock powerValue nameF data source)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaCanonicalExponent (constantF)
open GaussianCoefficientNameBounds (unit)
open GaussianBarnesCanonicalBase (base_lower)
open ComplexLogarithmRemainder (normSq oneCode)
open GaussianRationalHorner (ofGaussian_represents positive_product)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation product_lower)
open GaussianRationalReciprocal (power power_zero power_succ)
open GaussianCyclicExponentialSamples (inverseBudget sampleBound exponential_lower)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (R D k : PTm n) : PTm n := pw D k*(two*sampleBound (exponentRadius R))
def minimumClock (R : PTm n) : PTm n :=
  GaussianRootSchedule.binaryLength (two*inverseBudget (exponentRadius R))

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (R D k : PTm n) :
    Syn.subst σ (denominator R D k) = denominator (Syn.subst σ R) (Syn.subst σ D) (Syn.subst σ k) := by
  simp [denominator,exponentRadius,two]

@[simp] theorem subst_minimumClock {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (minimumClock R) = minimumClock (Syn.subst σ R) := by
  simp [minimumClock,exponentRadius,two]

/-- Retain the sharp rational denominator of an actual internal power. -/
theorem power_lower (q D k : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] lower q one D) : Γ ⊢[PRAAx] lower (power q k) one (pw D k) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] lower (Syn.shift q) one (Syn.shift D) := by
    simpa [Fm.shift,Syn.shift,one] using hq.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by
    simpa [Fm.shift,Syn.shift,one] using hD.shift
  have all : Γ ⊢[PRAAx] .all (lower (power (Syn.shift q) (var 0)) one (pw (Syn.shift D) (var 0))) := by
    ipra_qfind (le_QF _ _) [GaussianRationalLowerBounds.subst_lower, GaussianRationalReciprocal.subst_power, subst_ap2, one]
    · apply lower_congr (power_zero q).eqSymm (.eqRefl _) (pw_zero D).eqSymm
      exact lower_from_representation _ oneCode one one one (le_refl _) (le_refl _)
        (ofGaussian_represents _ _ (le_refl _))
        (le_congr (by ipra_ring) (congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqSymm (le_refl _))
    · let Q := power (Syn.shift q) (var 0)
      let D' := pw (Syn.shift D) (var 0)
      let Δ := lower Q one D' :: Γ.map Fm.shift
      have hD' : Δ ⊢[PRAAx] le one D' := GaussianFactorBudget.power_positive _ _ ds.wk
      have product := product_lower Q (Syn.shift q) one D' one (Syn.shift D) hD' ds.wk Prf.hyp0 hs.wk
      exact lower_congr (power_succ _ _).eqSymm (one_mul one) (pw_succ _ _).eqSymm product
  simpa only [GaussianRationalLowerBounds.subst_lower,GaussianRationalReciprocal.subst_power,
    subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using all.allE k

private theorem exp_den_positive (R : PTm n) : Γ ⊢[PRAAx] le one (two*sampleBound R) :=
  positive_product _ _ (le_succ_self one)
    (RationalNonnegativePowers.denominator_positive (num 3) R
      (le_trans (le_succ_self one) (le_succ_self two)))

theorem denominator_positive (R D k : PTm n) (hd : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (denominator R D k) :=
  positive_product _ _ (GaussianFactorBudget.power_positive _ _ hd) (exp_den_positive (exponentRadius R))

theorem sample_lower (p z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k)
    (hz : Γ ⊢[PRAAx] le one (normSq (translated z B k))) (hp : Γ ⊢[PRAAx] le (minimumClock R) p) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (data z R B k)) one (denominator R (B*k) k) := by
  let gh := exponentRadius R
  let s := clock p z R B k
  have hps : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have hU : Γ ⊢[PRAAx] le (two*inverseBudget gh) (unit (minimumClock R)) :=
    (GaussianRootSchedule.binary_length_correct (Γ := Γ) (two*inverseBudget gh)).andE₁
  have hMargin := le_trans hU
    (GaussianBalancedRadiusArithmetic.unit_monotone (minimumClock R) s (le_trans hp hps))
  have ex := exponential_lower constantF gh (correction z B k) s
    (GaussianBarnesCanonicalFactor.exponential_input z R B k h) hMargin
  have hd := positive_product _ _ h.andE₁ h.andE₂.andE₁
  have hpower := power_lower (base z B k) (B*k) k hd (base_lower z B k h.andE₁ h.andE₂.andE₁ hz)
  exact lower_congr (GaussianBarnesCanonicalFactor.sample_at p z R B k).eqSymm (one_mul one) (.eqRefl _)
    (product_lower (powerValue z B k) _ one _ one _ (GaussianFactorBudget.power_positive _ _ hd)
      (exp_den_positive gh) hpower ex)

theorem actual_Barnes_factor_late_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 1) (var 2) (var 3) (var 4) ⋏
      (le one (normSq (translated (var 1) (var 3) (var 4))) ⋏ le (minimumClock (var 2)) (var 0))) ⟶
      lower (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4))) one
        (denominator (var 2) (var 3*var 4) (var 4))) :=
  closeUniv 5 (.impI (sample_lower _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFactorApartness
