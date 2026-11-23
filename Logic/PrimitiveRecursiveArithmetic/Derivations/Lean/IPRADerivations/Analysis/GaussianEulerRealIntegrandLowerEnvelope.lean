import IPRADerivations.Analysis.GaussianEulerRealIntegrandNonnegative
import IPRADerivations.Analysis.GaussianEulerDecayLowerEnvelope
import IPRADerivations.Analysis.RationalHalfNinthProductLower

/-!
# The original real Euler integrand is at least one eighteenth on [1,2]

The actual power and decay factors are evaluated at the literal
normalized-product clock. Their two lower envelopes feed the genuine
rational product lemma. One auxiliary-query gap then transports the
bound to the unchanged original integrand evaluator at its requested
observation, with just that observation's single dyadic allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerRealIntegrandLowerEnvelope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (powerF powerData decayF decayData productF productData nameF data sample)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul positive_product)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lower : PTm n := GaussianEuclideanDistanceName.fraction one (num 18)
def auxiliary (j : PTm n) : PTm n := GaussianFastValueCut.exponent (num 18) j
def productClock (p z B a b : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus powerF decayF (powerData z B a b) (decayData a b)) p
def productObservation (p z B a b : PTm n) : PTm n := ap2 productF p (productData z B a b)

theorem product_clock_later (p z B a b : PTm n) : Γ ⊢[PRAAx] le p (productClock p z B a b) := le_add_right _ _
theorem auxiliary_later (j : PTm n) : Γ ⊢[PRAAx] le j (auxiliary j) := le_add_right _ _

theorem product_clock_large (j z B a b : PTm n) : Γ ⊢[PRAAx] le (num 18) (unit (productClock (auxiliary j) z B a b)) := by
  have first : Γ ⊢[PRAAx] le (num 18) (num 18*unit j) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (num 18) (unit_positive j))
  exact le_trans first (le_trans (GaussianFastValueCut.query_budget (num 18) j)
    (GaussianExponentialReference.unit_monotone (product_clock_later (auxiliary j) z B a b)))

theorem product_at (p z B a b : PTm n) : Γ ⊢[PRAAx]
    productObservation p z B a b ≐
      qmul (ap2 powerF (productClock p z B a b) (powerData z B a b))
        (ap2 decayF (productClock p z B a b) (decayData a b)) :=
  (GaussianNameArithmetic.multiply_at powerF decayF (powerData z B a b) (decayData a b) p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem product_real_part (p z B a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    fstT (productObservation p z B a b) ≐ RationalArithmetic.multiply
      (fstT (ap2 powerF (productClock p z B a b) (powerData z B a b)))
      (fstT (ap2 decayF (productClock p z B a b) (decayData a b))) :=
  (congrFst (product_at p z B a b)).eqTrans
    (GaussianPositiveExponentialProduct.real_product _ _ (GaussianEulerDecayRealSamples.original_observation_axis _ a b hb))

theorem actual_product_lower (j z R B a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerRealPowerLowerOrder.source z R B a b)
    (hab : Γ ⊢[PRAAx] le a (two*b)) : Γ ⊢[PRAAx]
    upper (lower : PTm n) (fstT (productObservation (auxiliary j) z B a b)) one (unit j) := by
  let p := auxiliary j
  let s := productClock p z B a b
  have pc := GaussianRadiusExponentialName.sample_canonical (Γ := Γ) GaussianEulerIntegrandName.powerExponentF
    (GaussianEulerIntegrandName.powerRadius z B a b) s (GaussianEulerIntegrandName.powerExponentData z B a b)
  have dc := GaussianRadiusExponentialName.sample_canonical (Γ := Γ) GaussianGammaCanonicalExponent.constantF
    (GaussianNameBounds.U GaussianGammaCanonicalExponent.constantF (GaussianEulerIntegrandName.decayPoint a b)) s (GaussianEulerIntegrandName.decayPoint a b)
  have old := RationalHalfNinthProductLower.product_lower _ _ (unit s) (product_clock_large j z B a b)
    pc.andE₂.andE₁ dc.andE₂.andE₁
    (GaussianEulerRealPowerLowerOrder.original_half_lower s z R B a b h hab)
    (GaussianEulerDecayLowerEnvelope.original_decay_lower s a b h.andE₂.andE₂.andE₁.andE₂ hab)
  have actual := upper_congr (.eqRefl _) (product_real_part p z B a b h.andE₂.andE₂.andE₁.andE₂).eqSymm (.eqRefl _) (.eqRefl _) old
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ)
    (le_trans (auxiliary_later j) (product_clock_later p z B a b))
  exact upper_mono _ _ _ _ _ _ (unit_positive s) actual (le_congr (by ipra_ring) (by ipra_ring) grow)

theorem original_lower_budget (p j z R B a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerRealPowerLowerOrder.source z R B a b)
    (hab : Γ ⊢[PRAAx] le a (two*b)) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack lower (fstT (ap2 nameF p (data z B a b))) one (unit p) two j := by
  let v := auxiliary j
  let J := unit j
  let V := unit v
  let P := unit p
  have hd := positive_product (Γ := Γ) _ _ (unit_positive v) (unit_positive p)
  have compare := GaussianNameEquivalence.cross_at productF nameF (productData z B a b) (data z B a b) v p
    (GaussianEulerIntegrandName.original_power_times_decay z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁))
  have near := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hd compare)
  have joined := upper_triangle _ _ _ one J (V+P) (V*P) (actual_product_lower j z R B a b h hab) near
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (auxiliary_later j)
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive j) hd) joined
  dsimp only [J,V,P,v]
  ipra_le (Groth.ι (IPRA.Q.mk Γ (unit p*unit p*unit j)))*sl grow

theorem original_name_lower (p z R B a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerRealPowerLowerOrder.source z R B a b)
    (hab : Γ ⊢[PRAAx] le a (two*b)) : Γ ⊢[PRAAx]
    upper lower (fstT (ap2 nameF p (data z B a b))) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ two
    (original_lower_budget p (GaussianNamedRealOrderTransport.precision lower (fstT (ap2 nameF p (data z B a b))) (unit p) two)
      z R B a b h hab)

/-- Original native half-plane and realness source, original evaluator,
and its independent requested observation precision. -/
theorem original_integrand_lower (p z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hi : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.im z) (ZT.ofNat ConciseIPRA.PTm.zero))
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le b a)
    (hab : Γ ⊢[PRAAx] le a (two*b)) : Γ ⊢[PRAAx]
    upper lower (fstT (sample p z B a b)) one (unit p) :=
  upper_congr (.eqRefl _) (congrFst (GaussianEulerIntegrandName.sample_at p z B a b)).eqSymm (.eqRefl _) (.eqRefl _)
    (original_name_lower p z R B a b (GaussianEulerRealIntegrandNonnegative.power_source_of_margin z R B A a b h hi ht) hab)

theorem original_real_Euler_integrand_one_eighteenth_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((GaussianEulerLowerPowerCoefficients.source (var 1) (var 2) (var 3) (var 4) ⋏
      (ZT.eq (ComplexLogarithmRemainder.im (var 1)) (ZT.ofNat ConciseIPRA.PTm.zero) ⋏
        ((GaussianPositiveRationalLogarithm.source (var 5) (var 6) ⋏ le (var 6) (var 5)) ⋏ le (var 5) (two*var 6)))) ⟶
      upper lower (fstT (sample (var 0) (var 1) (var 3) (var 5) (var 6))) one (unit (var 0))) :=
  closeUniv 7 (.impI (original_integrand_lower _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerRealIntegrandLowerEnvelope
