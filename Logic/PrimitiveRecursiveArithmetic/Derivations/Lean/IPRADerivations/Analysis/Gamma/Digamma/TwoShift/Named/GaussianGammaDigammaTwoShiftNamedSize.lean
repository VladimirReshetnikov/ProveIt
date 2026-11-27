import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedWindow
import IPRADerivations.Analysis.Euler.PowerScaling.Named.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddCoefficients

/-!
# The named quadratic shift size and its finite relative-error guard

The actual normalized arithmetic evaluates 4 A(A+1). A compact radius
of the original shift name controls the independent error against the
same quadratic expression computed exactly on each frozen chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedSize

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaTwoShiftNamedWindow (onePoint constant_self_rate sum_rate constant_one_fraction)
open GaussianGammaDigammaTwoShiftRationalWindow (coefficient)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast multiply_at multiplyRaw recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedFrozenScalarOrder (finite_order clear_common_chart)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRightHalfPlane (radius)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open RationalValueBounds (upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "U" => GaussianNameBounds.U
local notation "P" => GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator

def fourPoint : PTm n := fraction (num 4) one
def plusF (j : PR 2) : PR 2 := addF j constantF
def plusData (w : PTm n) : PTm n := addData w onePoint
def productF (j : PR 2) : PR 2 := multiplyF j (plusF j)
def productData (j : PR 2) (w : PTm n) : PTm n := multiplyData j (plusF j) w (plusData w)
def nameF (j : PR 2) : PR 2 := multiplyF constantF (productF j)
def data (j : PR 2) (w : PTm n) : PTm n := multiplyData constantF (productF j) fourPoint (productData j w)
def budget (j : PR 2) (w : PTm n) : PTm n := num 4*(U (plusF j) (plusData w)+radius j w)
def guardBudget (j : PR 2) (w : PTm n) : PTm n := budget j w+one

@[simp] theorem subst_fourPoint {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (fourPoint : PTm n) = (fourPoint : PTm m) := by simp [fourPoint,one]
@[simp] theorem subst_plusData {m : ℕ} (σ : Fin n → PTm m) (w : PTm n) :
    Syn.subst σ (plusData w) = plusData (Syn.subst σ w) := by simp [plusData]
@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (j : PR 2) (w : PTm n) :
    Syn.subst σ (productData j w) = productData j (Syn.subst σ w) := by simp [productData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (j : PR 2) (w : PTm n) :
    Syn.subst σ (data j w) = data j (Syn.subst σ w) := by simp [data]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (j : PR 2) (w : PTm n) :
    Syn.subst σ (budget j w) = budget j (Syn.subst σ w) := by simp [budget,GaussianNamedRightHalfPlane.radius]
@[simp] theorem subst_guardBudget {m : ℕ} (σ : Fin n → PTm m) (j : PR 2) (w : PTm n) :
    Syn.subst σ (guardBudget j w) = guardBudget j (Syn.subst σ w) := by simp [guardBudget,one]

theorem name_regular (j : PR 2) (w : PTm n) (h : Γ ⊢[PRAAx] pointCN j w) :
    Γ ⊢[PRAAx] pointCN (nameF j) (data j w) :=
  multiply_fast _ _ _ _ (constant_regular _) (multiply_fast _ _ _ _ h (add_fast _ _ _ _ h (constant_regular _)))

private theorem constant_product_sample (p a c : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyF constantF constantF) p (multiplyData constantF constantF a c) ≐ qmul a c := by
  let t := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF constantF a c) p
  exact (multiply_at constantF constantF a c p).eqTrans
    ((recode_congr (qmul_congr (constant_at t a) (constant_at t c))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qmul_canonical a c)))

theorem constant_product (a c v : PTm n) (h : Γ ⊢[PRAAx] qmul a c ≐ v) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF constantF constantF) constantF (multiplyData constantF constantF a c) v := by
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] qmul (sh a) (sh c) ≐ sh v :=
    by simpa [Fm.shift, Syn.shift, Δ, sh] using h.shift.shift
  apply GaussianNameEquivalence.transport_by_sample_eq (cross_refl constantF v (constant_regular v))
  · simpa [Δ, sh, Syn.shift] using
      (constant_product_sample (var 1) (sh a) (sh c)).eqTrans (hs.eqTrans (constant_at (var 1) (sh v)).eqSymm)
  · exact .eqRefl _

theorem plus_rate (j : PR 2) (w L b D : PTm n)
    (hj : Γ ⊢[PRAAx] pointCN j w) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] independentRate j constantF w (fraction L b) one D) :
    Γ ⊢[PRAAx] independentRate (plusF j) constantF (plusData w) (fraction (L+b) b) one D := by
  have eq := (qadd_congr (.eqRefl (fraction L b)) (constant_one_fraction b hb)).eqTrans
    (GaussianRationalQuadratureSquareCells.fraction_add_same L b b hb)
  have raw := sum_rate j constantF w onePoint (fraction L b) onePoint (fraction (L+b) b) one zero D hj
    (constant_regular _) hD hr (constant_self_rate _ _ hD) eq
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ (one+zero) D one D (add_zero _) (.eqRefl _) raw

theorem frozen_rate (j : PR 2) (w L b D : PTm n)
    (hj : Γ ⊢[PRAAx] pointCN j w) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D)
    (hR : Γ ⊢[PRAAx] le L (radius j w*b))
    (hr : Γ ⊢[PRAAx] independentRate j constantF w (fraction L b) one D) :
    Γ ⊢[PRAAx] independentRate (nameF j) constantF (data j w) (fraction (coefficient b L) (b*b)) (budget j w) D := by
  let R := radius j w
  let M := U (plusF j) (plusData w)
  let x := fraction L b
  let y := fraction (L+b) b
  let v := fraction (L*(L+b)) (b*b)
  let w' := fraction (coefficient b L) (b*b)
  have hp : Γ ⊢[PRAAx] pointCN (plusF j) (plusData w) := add_fast _ _ _ _ hj (constant_regular _)
  have hP : Γ ⊢[PRAAx] pointCN (productF j) (productData j w) := multiply_fast _ _ _ _ hj hp
  have hR' := GaussianEulerExponentCompactBounds.fraction_bound L b R hb hR
  have raw := P j (plusF j) constantF constantF w (plusData w) x y one one D M R hD hj hp
    (constant_regular x) (constant_regular y) (GaussianNameBounds.all_samples_bounded _ _ hp)
    (GaussianEulerNamedPowerScalingPowerFrozen.constant_bound x R hR') hr (plus_rate j w L b D hj hb hD hr)
  have middle : Γ ⊢[PRAAx] independentRate (productF j) constantF (productData j w) v (M+R) D :=
    GaussianNamedRateTransport.transport (productF j) (multiplyF constantF constantF) (productF j) constantF
      (productData j w) (multiplyData constantF constantF x y) (productData j w) v (M+R) D hD
      (GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ (M+R) D (by ipra_ring) (.eqRefl _) raw)
      (cross_refl _ _ hP)
      (cross_symm _ _ _ _ (constant_product x y v (GaussianStirlingOddCoefficients.fraction_product L b (L+b) b hb hb)))
  let W := U (productF j) (productData j w)
  have fourBound := GaussianEulerExponentCompactBounds.fraction_bound (Γ := Γ) (num 4) one (num 4)
    (le_refl _) (le_congr (.eqRefl _) (by ipra_ring) (le_refl (num 4)))
  have top := P constantF (productF j) constantF constantF fourPoint (productData j w) fourPoint v
    zero (M+R) D W (num 4) hD (constant_regular _) hP (constant_regular _) (constant_regular _)
    (GaussianNameBounds.all_samples_bounded _ _ hP) (GaussianEulerNamedPowerScalingPowerFrozen.constant_bound fourPoint (num 4) fourBound)
    (constant_self_rate _ _ hD) middle
  have hb₂ := positive_product _ _ hb hb
  have e : Γ ⊢[PRAAx] qmul (fourPoint : PTm n) v ≐ w' :=
    (GaussianStirlingOddCoefficients.fraction_product (num 4) one (L*(L+b)) (b*b) (le_refl _) hb₂).eqTrans
      (GaussianStirlingRationalTelescopers.fraction_same _ _ _ _ (positive_product _ _ (le_refl one) hb₂) hb₂
        (by dsimp only [coefficient]; ipra_ring))
  exact GaussianNamedRateTransport.transport (nameF j) (multiplyF constantF constantF) (nameF j) constantF
    (data j w) (multiplyData constantF constantF fourPoint v) (data j w) w' (budget j w) D hD
    (GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (by dsimp only [budget,M,R]; ipra_ring) (.eqRefl _) top)
    (cross_refl _ _ (name_regular j w hj)) (cross_symm _ _ _ _ (constant_product fourPoint v w' e))

theorem relative_guard (f j : PR 2) (x w a L b e s : PTm n)
    (hj : Γ ⊢[PRAAx] pointCN j w) (hb : Γ ⊢[PRAAx] le one b) (he : Γ ⊢[PRAAx] b ≐ e*unit s)
    (hR : Γ ⊢[PRAAx] le L (radius j w*b))
    (hjRate : Γ ⊢[PRAAx] independentRate j constantF w (fraction L b) one (unit s))
    (hfRate : Γ ⊢[PRAAx] independentRate f constantF x (fraction a b) one (unit s))
    (ho : Γ ⊢[PRAAx] realOrder (nameF j) f (data j w) x) :
    Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftWindowBuffer.relativeInput a b L e (guardBudget j w) (radius j w) := by
  have hD := unit_positive (Γ := Γ) s
  have hb₂ := positive_product _ _ hb hb
  have hG := frozen_rate j w L b (unit s) hj hb hD hR hjRate
  have finite := finite_order (nameF j) f (data j w) x (fraction (coefficient b L) (b*b)) (fraction a b)
    (budget j w) one (unit s) hD hG hfRate ho
  have e' := (congrMul he (.eqRefl b)).eqTrans (by ipra_ring : Γ ⊢[PRAAx] e*unit s*b ≐ (e*b)*unit s)
  have fractionEq := GaussianStirlingRationalTelescopers.fraction_same a b (a*b) (b*b) hb hb₂ (by ipra_ring)
  have size := clear_common_chart (coefficient b L) (a*b) (b*b) (e*b) (guardBudget j w) (unit s)
    hb₂ hD e' (upper_congr (.eqRefl _) (congrFst fractionEq) (.eqRefl _) (.eqRefl _) finite)
  have small : Γ ⊢[PRAAx] le e b := le_congr (.eqRefl _) he.eqSymm (by ipra_le 𝔞 e*sl hD)
  exact .andI small (.andI hR (le_congr (.eqRefl _) (by ipra_ring) size))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedSize
