import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.FrozenInputs.GaussianGammaMinimumFreezeRational
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.OrderedNames.GaussianHarmonicLogarithmName
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.Stirling.Telescoping.FiniteTelescopes.GaussianStirlingRationalTelescopers

/-!
# Common rational observations of named two-shift inputs

A single provable late clock freezes the three original real input
programs. Their actual observations are placed in a common positive
rational chart. The original named logarithm and both original named
log-Gamma programs retain independent rates to the exact rational
programs evaluated in that chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedFreeze

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaMinimumFreezeRational (numerator denominator frozen_rational_domain fraction_at)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData gammaLogMargin)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "S" => GaussianNamedGammaPositiveLower.source
local notation "RS" => GaussianStirlingGammaLogarithm.source
local notation "GF" => GaussianGammaMinimumFreeze.nameF
local notation "GD" => GaussianGammaMinimumFreeze.data
local notation "HF" => GaussianHarmonicLogarithmName.nameF
local notation "HD" => GaussianHarmonicLogarithmName.data

def source (f g h : PR 2) (x y z M : PTm n) : Fm PTm n := S f x M ⋏ (S g y M ⋏ S h z M)

def baseLogF (f : PR 2) : PR 2 := GaussianNamedPositiveLogarithm.nameF (retimedF f)
def baseLogData (x M : PTm n) : PTm n :=
  GaussianNamedPositiveLogarithm.data (retimedData x M) (two*M)

def gammaClock (f : PR 2) (s x M : PTm n) : PTm n :=
  succ (GaussianGammaHalfPlaneInputContinuity.modulus s (radius f x) (two*M))

def delay (g h : PR 2) (s y z M : PTm n) : PTm n := s+gammaClock g s y M+gammaClock h s z M
def clock (g h : PR 2) (s y z M : PTm n) : PTm n := delay g h s y z M+threshold M

def chartDenominator (f g h : PR 2) (k x y z : PTm n) : PTm n :=
  denominator f k x*(denominator g k y*denominator h k z)

def baseNumerator (f g h : PR 2) (k x y z : PTm n) : PTm n :=
  numerator f k x*(denominator g k y*denominator h k z)

def leftNumerator (f g h : PR 2) (k x y z : PTm n) : PTm n :=
  numerator g k y*(denominator f k x*denominator h k z)

def rightNumerator (f g h : PR 2) (k x y z : PTm n) : PTm n :=
  numerator h k z*(denominator f k x*denominator g k y)

ipra_subst source

ipra_subst baseLogData [two]

ipra_subst clock [delay, gammaClock, two]

ipra_subst chartDenominator

ipra_subst baseNumerator

ipra_subst leftNumerator

ipra_subst rightNumerator

theorem baseLog_input (f : PR 2) (x M : PTm n) (hs : Γ ⊢[PRAAx] S f x M) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source (retimedF f) (retimedData x M) (two*M) (radius f x) :=
  GaussianNamedPositiveLateLogSource.positive_source f x M hs.andE₁ hs.andE₂

theorem baseLog_regular (f : PR 2) (x M : PTm n) (hs : Γ ⊢[PRAAx] S f x M) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN (baseLogF f) (baseLogData x M) :=
  GaussianNamedPositiveLogarithm.name_regular _ _ _ _ (baseLog_input f x M hs)

private theorem rescaled_rational_source (f : PR 2) (k x M E B : PTm n)
    (hs : Γ ⊢[PRAAx] S f x M) (hk : Γ ⊢[PRAAx] le (threshold M) k)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] denominator f k x*E ≐ B) :
    Γ ⊢[PRAAx] RS (numerator f k x*E) B := by
  have hp := (frozen_rational_domain f k x M hs hk).andE₁
  exact .andI (positive_product _ _ hp.andE₁ hE)
    (le_congr (.eqRefl _) hB (positive_product _ _ hp.andE₂ hE))

theorem charts (f g h : PR 2) (k x y z M : PTm n) (hs : Γ ⊢[PRAAx] source f g h x y z M)
    (hk : Γ ⊢[PRAAx] le (threshold M) k) :
    Γ ⊢[PRAAx] RS (baseNumerator f g h k x y z) (chartDenominator f g h k x y z) ⋏
      (RS (leftNumerator f g h k x y z) (chartDenominator f g h k x y z) ⋏
        RS (rightNumerator f g h k x y z) (chartDenominator f g h k x y z)) := by
  have hx := (frozen_rational_domain f k x M hs.andE₁ hk).andE₁.andE₂
  have hy := (frozen_rational_domain g k y M hs.andE₂.andE₁ hk).andE₁.andE₂
  have hz := (frozen_rational_domain h k z M hs.andE₂.andE₂ hk).andE₁.andE₂
  refine .andI (rescaled_rational_source f k x M _ _ hs.andE₁ hk (positive_product _ _ hy hz) (.eqRefl _))
    (.andI (rescaled_rational_source g k y M _ _ hs.andE₂.andE₁ hk (positive_product _ _ hx hz) ?_)
      (rescaled_rational_source h k z M _ _ hs.andE₂.andE₂ hk (positive_product _ _ hx hy) ?_))
  all_goals unfold chartDenominator; ipra_ring

theorem values (f g h : PR 2) (k x y z M : PTm n) (hs : Γ ⊢[PRAAx] source f g h x y z M)
    (hk : Γ ⊢[PRAAx] le (threshold M) k) :
    Γ ⊢[PRAAx] ap2 f k x ≐ fraction (baseNumerator f g h k x y z) (chartDenominator f g h k x y z) ⋏
      (ap2 g k y ≐ fraction (leftNumerator f g h k x y z) (chartDenominator f g h k x y z) ⋏
        ap2 h k z ≐ fraction (rightNumerator f g h k x y z) (chartDenominator f g h k x y z)) := by
  have hb := (charts f g h k x y z M hs hk).andE₁.andE₂
  have hx := (frozen_rational_domain f k x M hs.andE₁ hk).andE₁.andE₂
  have hy := (frozen_rational_domain g k y M hs.andE₂.andE₁ hk).andE₁.andE₂
  have hz := (frozen_rational_domain h k z M hs.andE₂.andE₂ hk).andE₁.andE₂
  refine .andI ((fraction_at f k x M hs.andE₁ hk).eqTrans
    (GaussianStirlingRationalTelescopers.fraction_same _ _ _ _ hx hb ?_))
    (.andI ((fraction_at g k y M hs.andE₂.andE₁ hk).eqTrans
      (GaussianStirlingRationalTelescopers.fraction_same _ _ _ _ hy hb ?_))
      ((fraction_at h k z M hs.andE₂.andE₂ hk).eqTrans
        (GaussianStirlingRationalTelescopers.fraction_same _ _ _ _ hz hb ?_)))
  all_goals simp only [chartDenominator,baseNumerator,leftNumerator,rightNumerator]; ipra_ring

theorem freeze_logGamma (f : PR 2) (s k x M a b : PTm n)
    (hs : Γ ⊢[PRAAx] S f x M) (hk : Γ ⊢[PRAAx] le (threshold M) k)
    (hg : Γ ⊢[PRAAx] le (gammaClock f s x M) k)
    (hr : Γ ⊢[PRAAx] RS a b) (hv : Γ ⊢[PRAAx] ap2 f k x ≐ fraction a b) :
    Γ ⊢[PRAAx] independentRate (GF f) logGammaF (GD x M) (logGammaData a b) gammaLogMargin (unit s) := by
  have hi : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f s k x M :=
    .andI hs.andE₁ (.andI hk hg)
  have admissible := GaussianNamedPositiveLateLogSource.late_sample_admissible f x M k hs.andE₁ hs.andE₂ hk
  have fixed := GaussianExponentialReference.recode_fixed (ap2 f k x) admissible.andE₁
  have cross := GaussianGammaPositiveRationalProperness.original_cross _ _ _ _ a b
    (GaussianNamedGammaLateInput.encoded_source f s k x M hi) hr (fixed.eqTrans hv)
  exact GaussianGammaMinimumFreeze.frozen_log_rate_at_rational f s k x M a b hs hi hr cross

theorem freeze_baseLog (f : PR 2) (s r x M a b : PTm n)
    (hs : Γ ⊢[PRAAx] S f x M) (hr : Γ ⊢[PRAAx] le s r)
    (ha : Γ ⊢[PRAAx] RS a b)
    (he : Γ ⊢[PRAAx] numerator f (r+threshold M) x*b ≐ denominator f (r+threshold M) x*a) :
    Γ ⊢[PRAAx] independentRate (baseLogF f) HF (baseLogData x M) (HD a b) (two*M) (unit s) := by
  let k := r+threshold M
  let ar := numerator f k x
  let br := denominator f k x
  let ar' := GaussianNamedPositiveLogarithm.numerator (retimedF f) r (retimedData x M)
  let br' := GaussianNamedPositiveLogarithm.denominator (retimedF f) r (retimedData x M)
  have sample := GaussianNamedPositiveLateLogSource.sample_at (Γ := Γ) f r x M
  have ea : Γ ⊢[PRAAx] ar' ≐ ar := by
    simpa only [ar',ar,numerator,GaussianNamedPositiveLogarithm.numerator,k,GaussianUnitIntervalInputDecoding.subst_numerator,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (GaussianUnitIntervalInputDecoding.numerator (var 0) : PTm 1)
        (σ := ![ap2 (retimedF f) r (retimedData x M)]) (σ' := ![ap2 f k x]) (fun i => by fin_cases i; exact sample)
  have eb : Γ ⊢[PRAAx] br' ≐ br := by
    simpa only [br',br,denominator,GaussianNamedPositiveLogarithm.denominator,k,GaussianUnitIntervalInputDecoding.subst_denominator,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (GaussianUnitIntervalInputDecoding.denominator (var 0) : PTm 1)
        (σ := ![ap2 (retimedF f) r (retimedData x M)]) (σ' := ![ap2 f k x]) (fun i => by fin_cases i; exact sample)
  have src := baseLog_input f x M hs
  have hap := (GaussianNamedPositiveLogarithm.decoded_domain _ r _ _ _ src).andE₁
  have eq : Γ ⊢[PRAAx] ar'*b ≐ br'*a := (congrMul ea (.eqRefl _)).eqTrans (he.eqTrans (congrMul eb (.eqRefl _)).eqSymm)
  have old := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper ar' br' a b hap ha eq
  have right := cross_trans _ _ _ _ _ _ old (GaussianHarmonicLogarithmName.cross_original a b ha)
  have raw := GaussianNamedPositiveLogarithm.original_frozen_rate _ r _ _ _ src
  have hU := unit_positive (Γ := Γ) r
  have moved := GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hU raw
    (cross_refl _ _ (baseLog_regular f x M hs)) (cross_symm _ _ _ _ right)
  have grow := GaussianExponentialReference.unit_monotone hr
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hU (unit_positive s)
    (by ipra_le (2*𝔞 M)*sl grow) moved

def frozenRates (f g h : PR 2) (s x y z M : PTm n) : Fm PTm n :=
  let k := clock g h s y z M
  let a := baseNumerator f g h k x y z
  let b := chartDenominator f g h k x y z
  let c := leftNumerator f g h k x y z
  let d := rightNumerator f g h k x y z
  independentRate (baseLogF f) HF (baseLogData x M) (HD a b) (two*M) (unit s) ⋏
    (independentRate (GF g) logGammaF (GD y M) (logGammaData c b) gammaLogMargin (unit s) ⋏
      independentRate (GF h) logGammaF (GD z M) (logGammaData d b) gammaLogMargin (unit s))

theorem freeze_operands (f g h : PR 2) (s x y z M : PTm n) (hs : Γ ⊢[PRAAx] source f g h x y z M) :
    Γ ⊢[PRAAx] frozenRates f g h s x y z M := by
  let r := delay g h s y z M
  let k := clock g h s y z M
  have hk : Γ ⊢[PRAAx] le (threshold M) k := le_add_left _ _
  have hsr : Γ ⊢[PRAAx] le s r := le_trans (le_add_right _ _) (le_add_right _ _)
  have hg : Γ ⊢[PRAAx] le (gammaClock g s y M) k :=
    le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have hh : Γ ⊢[PRAAx] le (gammaClock h s z M) k := le_trans (le_add_left _ _) (le_add_right _ _)
  have hc := charts f g h k x y z M hs hk
  have hv := values f g h k x y z M hs hk
  refine .andI (freeze_baseLog f s r x M _ _ hs.andE₁ hsr hc.andE₁ ?_)
    (.andI (freeze_logGamma g s k y M _ _ hs.andE₂.andE₁ hk hg hc.andE₂.andE₁ hv.andE₂.andE₁)
      (freeze_logGamma h s k z M _ _ hs.andE₂.andE₂ hk hh hc.andE₂.andE₂ hv.andE₂.andE₂))
  change Γ ⊢[PRAAx] numerator f k x*chartDenominator f g h k x y z ≐
    denominator f k x*baseNumerator f g h k x y z
  unfold chartDenominator baseNumerator
  ipra_ring

theorem actual_named_two_shift_common_operand_freeze_closed (f g h : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f g h (var 1) (var 2) (var 3) (var 4) ⟶ frozenRates f g h (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (freeze_operands f g h _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedFreeze
