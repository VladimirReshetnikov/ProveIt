import IPRADerivations.Analysis.Stirling.AllOrders.Logarithms.GaussianStirlingAllOrderLogRateTransport
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsStrictOrder
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartTimeOrder

/-!
# Both strict sign branches imply the original logarithm rate

The sharp rational bound can have its own numerator and denominator.
A cleared comparison enlarges it to the exact radius consumed by
the existing multiplicative error program.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderLogRateFromStrict

open_ipra
open GaussianStirlingAllOrderLogRateTransport (upperPoint lowerPoint errorOrders original_rate)
open GaussianStirlingAllOrderTruncationHorner (hornerErrorData)
open GaussianStirlingAllOrderLogTruncation (errorF)
open GaussianStirlingExpansionConditionalError (logRate)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianStirlingNames (source)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (qnegative)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open RationalArithmetic (recode negative)
open RationalArgmin (rationalLE rationalLE_congr denominator_positive)
open RationalValueBounds (upper_of_order upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem fixed_scalar_order (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE (fstT a) (fstT b)) :
    Γ ⊢[PRAAx] realOrder constantF constantF a b := by
  refine .allI (.allI ?_)
  let u := Syn.shift (Syn.shift a)
  let v := Syn.shift (Syn.shift b)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have r : Δ ⊢[PRAAx] rationalLE (fstT u) (fstT v) := by simpa [Δ,u,v,Fm.shift,Syn.shift] using h.shift.shift
  have w := upper_of_order (fstT u) (fstT v) (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0)) r
  simpa [realOrder,Δ,u,v,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    upper_congr (congrFst (constant_at (var 1) u)).eqSymm (congrFst (constant_at (var 0) v)).eqSymm
      (.eqRefl _) (.eqRefl _) w

private theorem scalar_readback (R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] fstT (upperPoint R D) ≐ fraction R D := by
  let a := fraction R D
  have d := denominator_positive (Γ := Γ) a
  refine (fst_pair (recode a) _).eqTrans ?_
  exact RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.recode_guard a)
    (RationalNormalForm.normalize_well_formed _ _ hD)
    (RationalArithmetic.recode_value a) (RationalRepresentations.represents_self a) d d (.eqRefl _)

private theorem negative_scalar_readback (R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] fstT (lowerPoint R D) ≐ negative (fraction R D) :=
  (fst_pair (negative (fstT (upperPoint R D))) _).eqTrans
    (RationalAlgebra.negative_congr (scalar_readback R D hD))

private theorem zero_lower (R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] realOrder constantF constantF (lowerPoint R D) qzero := by
  apply fixed_scalar_order
  apply rationalLE_congr (negative_scalar_readback R D hD).eqSymm RationalGaussianRealPart.real_zero.eqSymm
  apply RationalArithmetic.order_of_representations _ _ _ _ D one
    (RationalRepresentations.represents_negative _ _ _ (fraction_represents R D hD))
    (fraction_represents zero one (le_refl one)) hD (le_refl one)
  apply zle_of_toZ R
  simp only [ZT.toZ_neg,ZT.toZ_ofNat,ZT.toZ_mul]
  ipra_simps
  ring

private theorem zero_upper (R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] realOrder constantF constantF qzero (upperPoint R D) :=
  fixed_scalar_order _ _
    (rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (scalar_readback R D hD).eqSymm
      (fraction_order zero one R D (le_refl one) hD (by ipra_le Groth.ι (IPRA.Q.mk Γ R))))

theorem positive_orders (d : ℕ) (A B x R D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (lo : Γ ⊢[PRAAx] strictOrder constantF errorF qzero (hornerErrorData d A B x))
    (hi : Γ ⊢[PRAAx] strictOrder errorF constantF (hornerErrorData d A B x) (upperPoint R D)) :
    Γ ⊢[PRAAx] errorOrders d A B x R D :=
  .andI (order_trans _ _ _ _ _ _ (zero_lower R D hD) lo.andE₁) hi.andE₁

theorem negative_orders (d : ℕ) (A B x R D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (lo : Γ ⊢[PRAAx] strictOrder constantF errorF (lowerPoint R D) (hornerErrorData d A B x))
    (hi : Γ ⊢[PRAAx] strictOrder errorF constantF (hornerErrorData d A B x) qzero) :
    Γ ⊢[PRAAx] errorOrders d A B x R D :=
  .andI lo.andE₁ (order_trans _ _ _ _ _ _ hi.andE₁ (zero_upper R D hD))

theorem log_rate_weaken (d : ℕ) (A B x R D C : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] le (R*pw A (succ (num d))) ((C*pw B (succ (num d)))*D))
    (h : Γ ⊢[PRAAx] errorOrders d A B x R D) : Γ ⊢[PRAAx] logRate d A B x C :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hD
    (GaussianFactorBudget.power_positive _ _ hs.andE₁) hr (original_rate d A B x R D hs hD h)

theorem positive_log_rate (d : ℕ) (A B x R D C : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] le (R*pw A (succ (num d))) ((C*pw B (succ (num d)))*D))
    (lo : Γ ⊢[PRAAx] strictOrder constantF errorF qzero (hornerErrorData d A B x))
    (hi : Γ ⊢[PRAAx] strictOrder errorF constantF (hornerErrorData d A B x) (upperPoint R D)) :
    Γ ⊢[PRAAx] logRate d A B x C :=
  log_rate_weaken d A B x R D C hs hD hr (positive_orders d A B x R D hD lo hi)

theorem negative_log_rate (d : ℕ) (A B x R D C : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] le (R*pw A (succ (num d))) ((C*pw B (succ (num d)))*D))
    (lo : Γ ⊢[PRAAx] strictOrder constantF errorF (lowerPoint R D) (hornerErrorData d A B x))
    (hi : Γ ⊢[PRAAx] strictOrder errorF constantF (hornerErrorData d A B x) qzero) :
    Γ ⊢[PRAAx] logRate d A B x C :=
  log_rate_weaken d A B x R D C hs hD hr (negative_orders d A B x R D hD lo hi)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderLogRateFromStrict
