import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositiveTimePowerProduct
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDilation

/-!
# Positive rational scaling of the original Euler integrand

The modified client is the original time-power name multiplied by the
original decay name evaluated at the scaled time. The unchanged Euler
name at that scaled time equals the normalized product of this client
and the original power at the fixed scale. All operation clocks and
exponential radii remain those of the actual original programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingIntegrand

open_ipra
open GaussianEulerIntegrandName (powerF powerData power_regular decayF decayData nameF data)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (B a b c d : PTm n) : Fm PTm n :=
  GaussianEulerPositiveTimePowerProduct.source B c d a b
abbrev dampedF : PR 2 := GaussianEulerIntegrandName.productF
def dampedData (z B a b c d : PTm n) : PTm n :=
  multiplyData powerF decayF (powerData z B a b) (decayData (c*a) (d*b))
def productF : PR 2 := multiplyF powerF dampedF
def productData (z B a b c d : PTm n) : PTm n :=
  multiplyData powerF dampedF (powerData z B c d) (dampedData z B a b c d)
def productClock (p z B a b c d : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus powerF dampedF (powerData z B c d) (dampedData z B a b c d)) p

ipra_subst source
ipra_subst dampedData
ipra_subst productData
ipra_subst productClock

theorem scaled_source (z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B (c*a) (d*b) :=
  .andI hs.andE₁ (GaussianHarmonicLogarithmProduct.product_source c d a b hs.andE₂)

theorem decay_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN decayF (decayData a b) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (GaussianGammaCanonicalExponent.constant_regular _))

theorem damped_regular (z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    pointCN dampedF (dampedData z B a b c d) :=
  multiply_fast powerF decayF _ _ (power_regular z B a b (.andI hs.andE₁ hs.andE₂.andE₂)) (decay_regular _ _)

theorem product_regular (z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    pointCN productF (productData z B a b c d) :=
  multiply_fast powerF dampedF _ _ (power_regular z B c d (.andI hs.andE₁ hs.andE₂.andE₁))
    (damped_regular z B a b c d hs)

/-- The original integrand at alpha*t equals alpha^(z/B-1) times the
original power at t multiplied by the original decay at alpha*t. -/
theorem original_scaling (z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    crossEquivalent nameF productF (data z B (c*a) (d*b)) (productData z B a b c d) := by
  have whole := scaled_source z B a b c d hs
  have hc := power_regular z B c d (.andI hs.andE₁ hs.andE₂.andE₁)
  have ht := power_regular z B a b (.andI hs.andE₁ hs.andE₂.andE₂)
  have hd := decay_regular (Γ := Γ) (c*a) (d*b)
  have split := GaussianEulerPositiveTimePowerProduct.original_power_product z B c d a b hs
  have multiply := GaussianGammaAdjacentCutoff.multiply_cross powerF GaussianEulerPositiveTimePowerProduct.productF decayF decayF
    (powerData z B (c*a) (d*b)) (GaussianEulerPositiveTimePowerProduct.productData z B c d a b)
    (decayData (c*a) (d*b)) (decayData (c*a) (d*b)) (power_regular z B _ _ whole)
    (multiply_fast powerF powerF _ _ hc ht) hd hd split (cross_refl _ _ hd)
  have regroup := GaussianNameRingLaws.multiply_associative powerF powerF decayF
    (powerData z B c d) (powerData z B a b) (decayData (c*a) (d*b)) hc ht hd
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianEulerIntegrandName.original_power_times_decay z B _ _ whole))
    (cross_trans _ _ _ _ _ _ multiply regroup)

theorem product_readback (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    ap2 productF p (productData z B a b c d) ≐
      qmul (ap2 powerF (productClock p z B a b c d) (powerData z B c d))
        (ap2 dampedF (productClock p z B a b c d) (dampedData z B a b c d)) :=
  (GaussianNameArithmetic.multiply_at powerF dampedF _ _ p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem original_observations (p q z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerIntegrandName.sample p z B (c*a) (d*b))
      (ap2 productF q (productData z B a b c d)) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (GaussianEulerIntegrandName.sample_at p z B _ _).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (cross_at _ _ _ _ p q (original_scaling z B a b c d hs))

/-- The modified client uses the actual original power and decay names,
and changes only the decay time to alpha*t. -/
def fixedData (z B c d : PTm n) : PTm n := pairT (pairT z B) (pairT c d)
def evaluatorTerm (p t x : PTm n) : PTm n := ap2 dampedF p
  (dampedData (fstT (fstT x)) (sndT (fstT x)) (fstT t) (sndT t) (fstT (sndT x)) (sndT (sndT x)))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def sample (p z B a b c d : PTm n) : PTm n := ap3 evaluatorF p (pairT a b) (fixedData z B c d)

ipra_subst fixedData
ipra_subst evaluatorTerm
ipra_subst sample

theorem evaluator_at (p t x : PTm n) : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
  simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem sample_at (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    sample p z B a b c d ≐ ap2 dampedF p (dampedData z B a b c d) := by
  have read := toPR_pairVector3_eq (Γ := Γ)
    (ap2 dampedF (var 0)
      (dampedData (fstT (var 2)) (sndT (var 2)) (fstT (var 1)) (sndT (var 1))
        (fstT (var 3)) (sndT (var 3))) : PTm 4) p (pairT a b) ![pairT z B, pairT c d]
  simp only [subst_ap2, subst_dampedData, subst_fstT, subst_sndT, Syn.subst_var] at read
  refine read.eqTrans (congrAp2 dampedF (.eqRefl p) ?_)
  ipra_congr (dampedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [fst_pair z B, snd_pair z B, fst_pair a b, snd_pair a b, fst_pair c d, snd_pair c d]

theorem product_evaluator_readback (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    ap2 productF p (productData z B a b c d) ≐
      qmul (ap2 powerF (productClock p z B a b c d) (powerData z B c d))
        (sample (productClock p z B a b c d) z B a b c d) :=
  (product_readback p z B a b c d).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (sample_at _ z B a b c d).eqSymm)

/-- This is the literal pullback used by the exact finite quadrature
dilation, rather than a separately chosen representation of alpha*t. -/
theorem original_pullback_observations (p q z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    distanceBounded
      (ap3 (GaussianRationalQuadratureDilation.pullF GaussianEulerIntegrandName.evaluatorF) p (pairT a b)
        (GaussianRationalQuadratureDilation.pullData c d (GaussianEulerIntegrandName.fixedData z B)))
      (qmul (ap2 powerF (productClock q z B a b c d) (powerData z B c d))
        (sample (productClock q z B a b c d) z B a b c d)) (unit p+unit q) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr
    (GaussianRationalQuadratureDilation.pull_fraction_at GaussianEulerIntegrandName.evaluatorF p a b c d
      (GaussianEulerIntegrandName.fixedData z B)).eqSymm
    (product_evaluator_readback q z B a b c d) (.eqRefl _) (.eqRefl _)
    (original_observations p q z B a b c d hs)

theorem actual_original_positive_rational_integrand_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ crossEquivalent nameF productF
      (data (var 0) (var 1) (var 4*var 2) (var 5*var 3))
      (productData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_scaling _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_positive_rational_integrand_pullback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded
        (ap3 (GaussianRationalQuadratureDilation.pullF GaussianEulerIntegrandName.evaluatorF) (var 0) (pairT (var 4) (var 5))
          (GaussianRationalQuadratureDilation.pullData (var 6) (var 7) (GaussianEulerIntegrandName.fixedData (var 2) (var 3))))
        (qmul (ap2 powerF (productClock (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
          (powerData (var 2) (var 3) (var 6) (var 7)))
          (sample (productClock (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
            (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (original_pullback_observations _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingIntegrand
