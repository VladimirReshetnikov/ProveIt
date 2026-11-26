import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalThirdLogarithmCofinal
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderEnvelope
import IPRADerivations.Analysis.Names.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsCaps
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsLog

/-!
# Named strict positivity and far-axis decay of the original cubic series

The exact first summand stays below every actual cofinal observation.
It proves strict positivity of the name itself. The same evaluator has
a dyadic upper bound at every observation once x≥4*2^q.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalThirdLogarithmCofinal (data nameF regular source)
open GaussianBarnesCanonicalThirdLogarithmRows (denominator denominator_positive numerator row)
open GaussianBarnesCanonicalThirdLogarithmCauchy (gain)
open GaussianBarnesCanonicalThirdLogarithmSeries (decayNumerator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open RationalValueBounds (upper upper_of_order)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem floor_at (p A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (row A B zero)))
      (fstT (ap2 nameF p (data A B))) zero (unit p) :=
  RationalValueBounds.upper_congr (congrFst (constant_at p (row A B zero))).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (upper_of_order _ _ _ _ (GaussianBarnesCanonicalThirdLogarithmCofinal.first_floor p A B h))

theorem named_floor (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] realOrder constantF nameF (row A B zero) (data A B) := by
  apply order_from_envelope constantF nameF (row A B zero) (data A B) zero (constant_regular _) (regular A B h)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  have hs : Γ.map Fm.shift ⊢[PRAAx] source a b := by
    simpa only [a,b,Fm.shift,Syn.shift,GaussianBarnesCanonicalThirdLogarithmCofinal.subst_source] using h.shift
  simpa only [envelope,a,b,Syn.shift,GaussianBarnesCanonicalThirdLogarithmRows.subst_row,
    GaussianBarnesCanonicalThirdLogarithmCofinal.subst_data,ConciseIPRA.PTm.subst_zero] using floor_at (var 0) a b hs

theorem floor_strict (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF constantF qzero (row A B zero) := by
  let P := numerator B zero
  let D := denominator A B zero
  have hD := denominator_positive A B zero h.andE₁
  have hP : Γ ⊢[PRAAx] le one P :=
    positive_product _ _ (positive_product _ _ (le_succ_self one) (le_refl one))
      (GaussianFactorBudget.power_positive _ _ h.andE₂)
  have sep : Γ ⊢[PRAAx] lt (D*zero) (P*one) :=
    lt_congr (by ipra_ring) (by ipra_ring) hP
  have f : Γ ⊢[PRAAx] strictOrder constantF constantF (fraction zero one) (fraction P D) :=
    .andI (GaussianStirlingMultiplicativeBoundsLog.constant_order _ _
      (GaussianStirlingMultiplicativeBoundsLog.fractions_order zero one P D (le_refl one) hD (le_of_lt sep)))
      (GaussianStirlingMultiplicativeBoundsCaps.strict_fractions zero one P D (le_refl one) hD sep)
  exact strict_transport _ _ _ _ _ _ _ _
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point zero one (le_refl one)).eqSymm)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point P D hD)) f

theorem strict_positive (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF nameF qzero (data A B) :=
  GaussianNamedStrictOrderDifference.trans_weak _ _ _ _ _ _ (floor_strict A B h) (named_floor A B h)

theorem far_decay (p q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A)
    (hfar : Γ ⊢[PRAAx] le ((gain*unit q)*B) A) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data A B)) one (unit q) := by
  have hA := le_trans hB hBA
  have first : Γ ⊢[PRAAx] le (decayNumerator A B*unit q) (((gain*unit q)*B)*A) := by
    ipra_le 2*𝔞(B)*𝔞(unit q)*sl hBA using
      dsimp only [gain,decayNumerator]
      ipra_simps
      ring
  have other : Γ ⊢[PRAAx] le (((gain*unit q)*B)*A) (one*(A*A)) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (mul_le_mul_right A hfar)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hA hA) (unit_positive q) (le_trans first other)
    (GaussianBarnesCanonicalThirdLogarithmCofinal.decay_bound p A B hB hBA)

theorem actual_Barnes_cubic_logarithm_cofinal_strict_positive_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶ strictOrder constantF nameF qzero (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (strict_positive _ _ Prf.hyp0))

theorem actual_Barnes_cubic_logarithm_far_decay_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let p := var 0
       let q := var 1
       let A := var 2
       let B := var 3
       (le one B ⋏ (le B A ⋏ le ((gain*unit q)*B) A)) ⟶ bounded (ap2 nameF p (data A B)) one (unit q)) :=
  closeUniv 4 (.impI (far_decay _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmOrder
