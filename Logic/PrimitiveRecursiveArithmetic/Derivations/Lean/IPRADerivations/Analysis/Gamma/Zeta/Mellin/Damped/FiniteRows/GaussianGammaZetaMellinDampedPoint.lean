import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.FiniteRows.GaussianGammaZetaMellinTranspose
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingIntegrand
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialPanel
import IPRADerivations.Analysis.Trigonometry.Sinc.Series.GaussianNamedSincSamples

/-!
# Original positive-scaling observations of the Mellin decay terms

The transposed term and the Euler scaling sampler read the same
power and decay names. The two original factor clocks admit a common
dyadic estimate on a positive compact time strip.
-/

set_option autoImplicit false
set_option maxHeartbeats 720000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedPoint

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerIntegrandName (powerF powerData decayF decayData decayPoint power_regular)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianEulerPositiveScalingIntegrand (sample sample_at decay_regular)
open GaussianFastValueCut (exponent)
open GaussianGammaZetaMellinDecayPrefix (powerSample term)
open GaussianGammaZetaMellinIntegrand (factorClock)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyModulus multiply_at multiplyRaw product_distance)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qnegative_represents)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianRationalSyntheticDivision (qmul_congr)
open ComplexLogarithmRemainder (scale oneCode re)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "parameterSource" => GaussianEulerExponentCompactBounds.source
local notation "timeDomain" => GaussianCompactLogarithmBounds.domain

def observation (j p z D a b : PTm n) : PTm n :=
  qmul (powerSample p z D a b) (term j (factorClock p z D a b) a b)

def cost (R H T : PTm n) : PTm n := two*(majorant R H T+two)

ipra_subst observation [factorClock]

ipra_subst cost [majorant, GaussianEulerCompactPowerMajorant.exponentRadius, two, one]

private theorem decay_nonpositive (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT (decayPoint a b)) (natCode zero) := by
  let g := ComplexLogarithmRemainder.neg (scale a oneCode)
  have repr : Γ ⊢[PRAAx] GaussianRationalHorner.represents (decayPoint a b) g b :=
    qnegative_represents _ _ _ (GaussianRationalHorner.ofGaussian_represents _ _ hb)
  have ev : Γ ⊢[PRAAx] ZT.eq (re g) (-ZT.ofNat a) := by
    apply ZT.derive
    simp only [g,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_neg,ZT.toZ_ofNat]
    ring
  have rep := GaussianRationalHorner.scalar_congr (.eqRefl _) ev (.eqRefl _) repr.andE₁
  apply RationalArithmetic.order_of_representations _ _ _ _ b one rep (natCode_represents zero) hb (le_refl one)
  apply zle_of_toZ a
  simp only [ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem decay_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (ap2 decayF p (decayData a b)) two one := by
  let q := decayPoint a b
  let R := GaussianNameBounds.U constantF q
  exact GaussianBinetExponentialPanel.unit_bound p q R
    (GaussianGammaFiniteApproximantName.exponential_input constantF q (constant_regular q))
    (decay_nonpositive a b hb)

private theorem decay_data_unit (a b : PTm n) : Γ ⊢[PRAAx] decayData a (one*b) ≐ decayData a b := by
  simpa only [GaussianEulerDampedTimeRate.subst_decayData,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
    Prf.eqCongr1 (decayData (Syn.shift a) (var 0)) (one_mul b)

theorem point_error (j p q z R D a b H T : PTm n)
    (hz : Γ ⊢[PRAAx] parameterSource z R D H) (ht : Γ ⊢[PRAAx] timeDomain a b H T)
    (hq : Γ ⊢[PRAAx] le q p) :
    Γ ⊢[PRAAx] distanceBounded (observation j p z D a b) (sample q z D a b (succ j) one)
      (cost R H T) (unit q) := by
  let c := succ j
  let k := factorClock p z D a b
  let r := GaussianGammaZetaMellinDecayRows.clock k b
  let x := powerData z D a b
  let y := decayData (c*a) b
  let y' := decayData (c*a) (one*b)
  let s := exponent (multiplyModulus powerF decayF x y') q
  have kp : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have rk : Γ ⊢[PRAAx] le k r := le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have qk := le_trans hq kp
  have qr := le_trans qk rk
  have qs : Γ ⊢[PRAAx] le q s := le_add_right _ _
  have hx := power_regular z D a b (.andI hz.andE₁ ht.andE₁)
  have hy := decay_regular (Γ := Γ) (c*a) b
  have d₁ := GaussianNamedSincSamples.common_late_distance powerF x q k s hx qk qs
  have d₂ := GaussianNamedSincSamples.common_late_distance decayF y q r s hy qr qs
  have bound := product_distance _ _ _ _ two two (unit q) two (majorant R H T) (unit_positive q)
    d₁ d₂ (decay_bound r (c*a) b ht.andE₁.andE₂) (original_power_observation s z R D H T a b hz ht)
  have target : Γ ⊢[PRAAx] sample q z D a b c one ≐ qmul (ap2 powerF s x) (ap2 decayF s y) :=
    (sample_at q z D a b c one).eqTrans
      ((multiply_at powerF decayF x y' q).eqTrans
        ((GaussianExponentialReference.recode_fixed (multiplyRaw powerF decayF s x y') (qmul_canonical _ _)).eqTrans
          (qmul_congr (.eqRefl _) (congrAp2 decayF (.eqRefl s) (decay_data_unit (c*a) b)))))
  exact distance_congr (.eqRefl _) target.eqSymm (by unfold cost; ipra_ring) (.eqRefl _) bound

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedPoint
