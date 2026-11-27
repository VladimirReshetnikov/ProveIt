import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailScalar
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailPointwise

/-!
# The actual monomial-decay name has the exact factorial half-decay majorant

The monomial is the literal canonical rational (a/b)^d, with numerical d.
Only existing constant/product/decay programs are used. The actual named
half-decay factorization and one finite-gap removal retain the exact
2^d*d! majorant, without replacing d by d+1 or assuming a power law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianMonomialDecayMajorant

open_ipra
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEulerUpperTailPointwise (majorantTop majorantBottom half_decay_product_bound)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr power)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianDominantPairAlgebra (radiusPoint radius_power)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedSmallPerturbationTransport (productClock product_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (a b : PTm n) : Fm PTm n := le one b ⋏ le b a
def monomial (d a b : PTm n) : PTm n := radiusPoint (pw a d) (pw b d)
def nameF : PR 2 := multiplyF constantF decayF
def data (d a b : PTm n) : PTm n := multiplyData constantF decayF (monomial d a b) (decayData a b)
def sample (p d a b : PTm n) : PTm n := ap2 nameF p (data d a b)
def halfWeightedF : PR 2 := multiplyF constantF decayF
def halfWeightedData (d a b : PTm n) : PTm n := multiplyData constantF decayF (monomial d a b) (decayData a (two*b))
def halfIntegrandF : PR 2 := multiplyF halfWeightedF decayF
def halfIntegrandData (d a b : PTm n) : PTm n := multiplyData halfWeightedF decayF (halfWeightedData d a b) (decayData a (two*b))
ipra_subst source
ipra_subst monomial
ipra_subst data [decayData, GaussianGammaFiniteApproximantName.exponentialInputData]
ipra_subst sample

theorem half_factorization (d a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    crossEquivalent halfIntegrandF nameF (halfIntegrandData d a b) (data d a b) := by
  let P := monomial d a b
  let D := decayData a (two*b)
  let E := decayData a b
  let D2 := GaussianEulerHalfDecayProduct.halfProductData a b
  have hp := constant_regular (Γ := Γ) P
  have hd := GaussianEulerHalfDecayProduct.decay_regular (Γ := Γ) a (two*b)
  have he := GaussianEulerHalfDecayProduct.decay_regular (Γ := Γ) a b
  have hs := GaussianNameArithmetic.multiply_fast decayF decayF D D hd hd
  exact cross_trans _ _ _ _ _ _
    (GaussianNameRingLaws.multiply_associative constantF decayF decayF P D D hp hd hd)
    (GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (multiplyF decayF decayF) decayF
      P P D2 E hp hp hs he (cross_refl constantF P hp) (GaussianEulerHalfDecayProduct.original_decay_as_half_product a b hb))

theorem half_weighted_bound (p d a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    bounded (ap2 halfWeightedF p (halfWeightedData d a b))
      (majorant d*unit p+GaussianEulerWeightedHalfDecay.slack a d) (unit p) := by
  let P := monomial d a b
  let D := decayData a (two*b)
  let s := productClock constantF decayF P D p
  have hb := h.andE₁
  have ha := le_trans hb h.andE₂
  have h2 := (le_succ_self (Γ := Γ) one)
  have fraction := (GaussianDominantPairAlgebra.radius_congr (mul_comm two a) (mul_comm two b)).eqTrans
    (GaussianEulerWeightedHalfDecay.radius_rescale a b two hb h2)
  have weight : Γ ⊢[PRAAx] power (radiusPoint (two*a) (two*b)) d ≐ P :=
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl d) fraction).eqTrans (radius_power a b d hb)
  have raw := bound_congr (qmul_congr weight (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianEulerDecayFactorBounds.original_half_decay_factor_bound a (two*b) d s ha (positive_product _ _ h2 hb))
  have e := (product_at (Γ := Γ) constantF decayF P D p).eqTrans
    (qmul_congr (constant_at s P) (.eqRefl _))
  have grow : Γ ⊢[PRAAx] le (unit p) (unit s) := GaussianExponentialReference.unit_monotone (le_add_right p _)
  have compare : Γ ⊢[PRAAx] le ((majorant d*unit s+GaussianEulerWeightedHalfDecay.slack a d)*unit p)
      ((majorant d*unit p+GaussianEulerWeightedHalfDecay.slack a d)*unit s) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (majorant d*unit p*unit s))
        (mul_le_mul_right (GaussianEulerWeightedHalfDecay.slack a d) grow))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (unit_positive s) (unit_positive p) compare raw)

theorem original_upper_tail_pointwise (p q d a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] bounded (sample p d a b) (majorantTop p q d a b) (majorantBottom p q a b) :=
  half_decay_product_bound halfWeightedF nameF (halfWeightedData d a b) (data d a b)
    p q a b (majorant d) (GaussianEulerWeightedHalfDecay.slack a d) h.andE₁ (half_factorization d a b h.andE₁)
    (fun t => half_weighted_bound t d a b h)

theorem actual_literal_monomial_decay_factorial_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 3) (var 4) ⟶ bounded (sample (var 0) (var 2) (var 3) (var 4))
      (majorantTop (var 0) (var 1) (var 2) (var 3) (var 4)) (majorantBottom (var 0) (var 1) (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_upper_tail_pointwise _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianMonomialDecayMajorant
