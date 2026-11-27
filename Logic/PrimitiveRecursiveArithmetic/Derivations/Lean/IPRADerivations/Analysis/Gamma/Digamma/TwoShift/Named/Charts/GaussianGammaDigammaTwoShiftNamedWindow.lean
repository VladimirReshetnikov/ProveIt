import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedFrozenScalarOrder
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.Windows.GaussianGammaDigammaTwoShiftWindowBuffer
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Integration.Quadrature.SquareSubstitution.GaussianRationalQuadratureSquareCells
import IPRADerivations.Analysis.Stirling.Telescoping.FiniteTelescopes.GaussianStirlingRationalTelescopers

/-!
# Ordinary real orders imply the finite two-shift window guards

The named hypotheses express 1 ≤ A, 2A+1 ≤ x and the two-sided
shift bounds using the original normalized addition. Given a common
late chart and its dyadic pitch, these hypotheses certify the exact
arithmetic deficits used by the closed-window repair.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedWindow

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedFrozenScalarOrder (finite_order clear_common_chart)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalQuadratureSquareCells (fraction_add_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianNamedGammaPositiveLower.source

def onePoint : PTm n := fraction one one

def baseWindowF (j : PR 2) : PR 2 := addF (addF j j) constantF
def baseWindowData (w : PTm n) : PTm n := addData (addData w w) onePoint

def endpointWindow (f g j : PR 2) (x y w : PTm n) : Fm PTm n :=
  realOrder f (addF g j) x (addData y w) ⋏ realOrder g (addF f j) y (addData x w)

def orders (f g h j : PR 2) (x y z w : PTm n) : Fm PTm n :=
  realOrder constantF j onePoint w ⋏
    (realOrder (baseWindowF j) f (baseWindowData w) x ⋏
      (endpointWindow f g j x y w ⋏ endpointWindow f h j x z w))

def source (f g h j : PR 2) (x y z w M : PTm n) : Fm PTm n :=
  S f x M ⋏ (S g y M ⋏ (S h z M ⋏ S j w M))

def frozen (f g h j : PR 2) (x y z w a b c d L D : PTm n) : Fm PTm n :=
  independentRate f constantF x (fraction a b) one D ⋏
    (independentRate g constantF y (fraction c b) one D ⋏
      (independentRate h constantF z (fraction d b) one D ⋏ independentRate j constantF w (fraction L b) one D))

@[simp] theorem subst_onePoint {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (onePoint : PTm n) = (onePoint : PTm m) := by simp [onePoint,one]

@[simp] theorem subst_baseWindowData {m : ℕ} (σ : Fin n → PTm m) (w : PTm n) :
    Syn.subst σ (baseWindowData w) = baseWindowData (Syn.subst σ w) := by simp [baseWindowData]

@[simp] theorem subst_endpointWindow {m : ℕ} (σ : Fin n → PTm m) (f g j : PR 2) (x y w : PTm n) :
    (endpointWindow f g j x y w).subst σ = endpointWindow f g j (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ w) := by
  simp [endpointWindow]

@[simp] theorem subst_orders {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (x y z w : PTm n) :
    (orders f g h j x y z w).subst σ = orders f g h j (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) := by
  simp [orders]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (x y z w M : PTm n) :
    (source f g h j x y z w M).subst σ =
      source f g h j (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ M) := by
  simp [source]

@[simp] theorem subst_frozen {m : ℕ} (σ : Fin n → PTm m) (f g h j : PR 2) (x y z w a b c d L D : PTm n) :
    (frozen f g h j x y z w a b c d L D).subst σ =
      frozen f g h j (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ a)
        (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ D) := by
  simp [frozen,one]

theorem constant_self_rate (c D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] independentRate constantF constantF c c zero D :=
  GaussianNamedRateRadius.weaken constantF constantF c c zero one zero D (le_refl one) hD (by ipra_le 0)
    (GaussianNamedDifferenceRate.self_rate constantF c (constant_regular c))

theorem sum_rate (f g : PR 2) (x y a c v A B D : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hD : Γ ⊢[PRAAx] le one D)
    (ha : Γ ⊢[PRAAx] independentRate f constantF x a A D) (hc : Γ ⊢[PRAAx] independentRate g constantF y c B D)
    (he : Γ ⊢[PRAAx] qadd a c ≐ v) :
    Γ ⊢[PRAAx] independentRate (addF f g) constantF (addData x y) v (A+B) D := by
  have raw := GaussianNamedAddRate.independent_rate f g constantF constantF x y a c A D B D hD hD ha hc
  have rate : Γ ⊢[PRAAx] independentRate (addF f g) (addF constantF constantF) (addData x y) (addData a c) (A+B) D :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ (A+B) D (positive_product _ _ hD hD) hD
      (le_of_eq_add (d := zero) (by simp only [GaussianNamedRateComposition.leadingNumerator]; ipra_ring)) raw
  exact GaussianNamedRateTransport.transport (addF f g) (addF constantF constantF) (addF f g) constantF
    (addData x y) (addData a c) (addData x y) v (A+B) D hD rate
      (cross_refl _ _ (add_fast f g x y hf hg))
      (cross_symm _ _ _ _ (GaussianNamedGammaHalfShift.constant_sum a c v he))

theorem constant_one_fraction (b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] onePoint ≐ fraction b b := by
  exact GaussianStirlingRationalTelescopers.fraction_same one one b b (le_refl _) hb (by ipra_ring)

private theorem datum_sum_rate (f g : PR 2) (x y a c b D : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] le one D) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hr : Γ ⊢[PRAAx] independentRate f constantF x (fraction a b) one D)
    (hs : Γ ⊢[PRAAx] independentRate g constantF y (fraction c b) one D) :
    Γ ⊢[PRAAx] independentRate (addF f g) constantF (addData x y) (fraction (a+c) b) two D :=
  GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ (one+one) D two D
    (by ipra_ring) (.eqRefl _)
    (sum_rate f g x y (fraction a b) (fraction c b) (fraction (a+c) b) one one D hf hg hD hr hs
      (fraction_add_same a c b hb))

theorem base_window_rate (j : PR 2) (w L b D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D) (hj : Γ ⊢[PRAAx] pointCN j w)
    (hr : Γ ⊢[PRAAx] independentRate j constantF w (fraction L b) one D) :
    Γ ⊢[PRAAx] independentRate (baseWindowF j) constantF (baseWindowData w) (fraction (two*L+b) b) two D := by
  let u := fraction (L+L) b
  let v := fraction (two*L+b) b
  have hTwo := datum_sum_rate j j w w L L b D hb hD hj hj hr hr
  have e : Γ ⊢[PRAAx] qadd u (onePoint : PTm n) ≐ v :=
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (constant_one_fraction b hb)).eqTrans
      ((fraction_add_same (L+L) b b hb).eqTrans
        (GaussianStirlingRationalTelescopers.fraction_same (L+L+b) b (two*L+b) b hb hb (by ipra_ring)))
  have raw := sum_rate (addF j j) constantF (addData w w) onePoint u onePoint v two zero D
    (add_fast _ _ _ _ hj hj) (constant_regular _) hD hTwo (constant_self_rate _ _ hD) e
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ (two+zero) D two D (add_zero _) (.eqRefl _) raw

private theorem endpoint_guards (f g j : PR 2) (x y w a c L b e s : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (he : Γ ⊢[PRAAx] b ≐ e*unit s)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hj : Γ ⊢[PRAAx] pointCN j w)
    (fr : Γ ⊢[PRAAx] independentRate f constantF x (fraction a b) one (unit s))
    (gr : Γ ⊢[PRAAx] independentRate g constantF y (fraction c b) one (unit s))
    (jr : Γ ⊢[PRAAx] independentRate j constantF w (fraction L b) one (unit s))
    (ho : Γ ⊢[PRAAx] endpointWindow f g j x y w) :
    Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftWindowBuffer.approximateWindow a L c e := by
  have hD := unit_positive (Γ := Γ) s
  have r₁ := datum_sum_rate g j y w c L b (unit s) hb hD hg hj gr jr
  have r₂ := datum_sum_rate f j x w a L b (unit s) hb hD hf hj fr jr
  have l := finite_order f (addF g j) x (addData y w) (fraction a b) (fraction (c+L) b) one two (unit s) hD fr r₁ ho.andE₁
  have r := finite_order g (addF f j) y (addData x w) (fraction c b) (fraction (a+L) b) one two (unit s) hD gr r₂ ho.andE₂
  have E₁ := clear_common_chart a (c+L) b e (one+two) (unit s) hb hD he l
  have E₂ := clear_common_chart c (a+L) b e (one+two) (unit s) hb hD he r
  exact .andI (le_congr (.eqRefl _) (by unfold GaussianGammaDigammaTwoShiftWindowBuffer.enlarged; ipra_ring) E₁)
    (le_congr (.eqRefl _) (by unfold GaussianGammaDigammaTwoShiftWindowBuffer.enlarged; ipra_ring) E₂)

theorem approximate_window (f g h j : PR 2) (x y z w M a b c d L e s : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w)
    (ha : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) (he : Γ ⊢[PRAAx] b ≐ e*unit s)
    (hr : Γ ⊢[PRAAx] frozen f g h j x y z w a b c d L (unit s)) :
    Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftWindowBuffer.approximateInput a b c d L e := by
  have hf := hs.andE₁.andE₁.andE₁
  have hg := hs.andE₂.andE₁.andE₁.andE₁
  have hh := hs.andE₂.andE₂.andE₁.andE₁.andE₁
  have hj := hs.andE₂.andE₂.andE₂.andE₁.andE₁
  have hU := unit_positive (Γ := Γ) s
  have hb := ha.andE₂
  have fr := hr.andE₁
  have gr := hr.andE₂.andE₁
  have hhRate := hr.andE₂.andE₂.andE₁
  have jr := hr.andE₂.andE₂.andE₂
  have raw := constant_self_rate (Γ := Γ) (onePoint : PTm n) (unit s) hU
  have eq := constant_one_fraction b hb
  have oneRate : Γ ⊢[PRAAx] independentRate constantF constantF onePoint (fraction b b) zero (unit s) :=
    GaussianNamedRateTransport.transport constantF constantF constantF constantF onePoint onePoint onePoint (fraction b b)
      zero (unit s) hU raw (cross_refl _ _ (constant_regular _))
      (GaussianSignedNameExponentialOrder.constant_equal_cross (fraction b b) onePoint eq.eqSymm)
  have first := finite_order constantF j onePoint w (fraction b b) (fraction L b) zero one (unit s) hU oneRate jr ho.andE₁
  have low := clear_common_chart b L b e (zero+one) (unit s) hb hU he first
  have br := base_window_rate j w L b (unit s) hb hU hj jr
  have next := finite_order (baseWindowF j) f (baseWindowData w) x (fraction (two*L+b) b) (fraction a b)
    two one (unit s) hU br fr ho.andE₂.andE₁
  have base := clear_common_chart (two*L+b) a b e (two+one) (unit s) hb hU he next
  exact .andI ha (.andI (le_congr (.eqRefl _) (by ipra_ring) low)
    (.andI (le_congr (.eqRefl _) (by ipra_ring) base)
      (.andI (endpoint_guards f g j x y w a c L b e s hb he hf hg hj fr gr jr ho.andE₂.andE₂.andE₁)
        (endpoint_guards f h j x z w a d L b e s hb he hf hh hj fr hhRate jr ho.andE₂.andE₂.andE₂))))

theorem actual_two_shift_named_window_guards_closed (f g h j : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      (source f g h j (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ orders f g h j (var 0) (var 1) (var 2) (var 3) ⟶
        GaussianStirlingGammaLogarithm.source (var 5) (var 6) ⟶ var 6 ≐ var 10*unit (var 11) ⟶
        frozen f g h j (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9) (unit (var 11)) ⟶
        GaussianGammaDigammaTwoShiftWindowBuffer.approximateInput (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)) :=
  closeUniv 12 (.impI (.impI (.impI (.impI (.impI
    (approximate_window f g h j _ _ _ _ _ _ _ _ _ _ _ _
      (Prf.hyp0.wk.wk.wk.wk) (Prf.hyp0.wk.wk.wk) (Prf.hyp0.wk.wk) (Prf.hyp0.wk) Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedWindow
