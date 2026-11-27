import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementObservations
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementLogGap
import IPRADerivations.Analysis.Stirling.Bounds.Logarithmic.GaussianStirlingGlobalBoundsTranslatedRate

/-!
# The native log-gamma fractional increment estimate

The neighboring integer chords squeeze the increment between scaled
harmonic logarithms. Their finite mesh gap is at most 1/(i-1).
An explicit cofinal precision removes the auxiliary normalization
errors while preserving the stated rate at independent input queries.
-/

set_option autoImplicit false
set_option maxHeartbeats 820000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrement

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (point_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product qmul qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianStirlingGammaFractionalIncrementConvexity (pred_positive)
open GaussianStirlingGammaFractionalIncrementLogGap (log_gap)
open GaussianStirlingGammaFractionalIncrementObservations
  (upperCost lowerCost slopeCost scalar_upper slope_raw_error fraction_contracts upper_observation lower_observation)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData)
open GaussianStirlingGlobalBoundsShiftArguments
  (deltaF deltaData slopeF slopeData shiftedNumerator delta_regular slope_regular)
open GaussianStirlingGlobalBoundsTranslatedRate
  (incrementRate first_order_from_increment rational_robbins_from_increment)
open RationalValueBounds (upper upper_mono upper_congr upper_triangle radius_of_upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "δ" p:arg i:arg r:arg b:arg => ap2 deltaF p (deltaData i r b)
local notation "σ" p:arg i:arg r:arg b:arg => ap2 slopeF p (slopeData i r b)

def cofinalCost (i r b : PTm n) : PTm n :=
  upperCost i r b+lowerCost i r b+slopeCost i r b+slopeCost (pred i) r b

theorem upper_cofinal (i r b t : PTm n) (hi : Γ ⊢[PRAAx] le two i)
    (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le one r) (hrb : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] upperSlack (fstT (δ t i r b)) (fstT (σ t i r b)) one (pred i) (cofinalCost i r b) t := by
  have ii := le_trans RationalAlgebra.two_positive hi
  apply upper_mono _ _ _ _ _ _ (unit_positive t) (upper_observation i r b t ii hb hr hrb)
  apply le_of_eq_add (d := unit t*unit t+
    (lowerCost i r b+slopeCost i r b+slopeCost (pred i) r b)*pred i*unit t)
  dsimp [cofinalCost]
  ipra_ring

theorem lower_cofinal (i r b t : PTm n) (hi : Γ ⊢[PRAAx] le two i)
    (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le one r) (hrb : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] upperSlack (fstT (σ t i r b)) (fstT (δ t i r b)) one (pred i) (cofinalCost i r b) t := by
  let k := pred i
  let u := unit t
  have hp := unit_positive (Γ := Γ) t
  have hk := pred_positive i hi
  have ii := le_trans RationalAlgebra.two_positive hi
  have left := scalar_upper _ _ _ _ hp (slope_raw_error i r b t ii)
  have center := scalar_upper _ _ _ _ hk (fraction_contracts r b _ _ _ _ hb hrb hk (log_gap i t hi))
  have right := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp (slope_raw_error k r b t hk))
  have lower := lower_observation i r b t hi hb hr hrb
  have joined := upper_triangle _ _ _ _ _ _ _
    (upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left center) right) lower
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ hp hk) hp) hp) joined
  apply le_of_eq_add (d := upperCost i r b*k*k*u*u*u)
  dsimp [cofinalCost,k,u]
  ipra_ring

theorem named_upper_at (F H : PR 2) (x y D K p q : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hH : Γ ⊢[PRAAx] pointCN H y)
    (hD : Γ ⊢[PRAAx] le one D)
    (cofinal : ∀ t : PTm n, Γ ⊢[PRAAx] upperSlack (fstT (ap2 F t x)) (fstT (ap2 H t y)) one D K t) :
    Γ ⊢[PRAAx] upper (fstT (ap2 F p x)) (fstT (ap2 H q y)) (rateNumerator one D p q) (rateDenominator D p q) := by
  let C := K+two
  let t := precision (fstT (ap2 F p x)) (fstT (ap2 H q y)) (rateDenominator D p q) C
  have pp := unit_positive (Γ := Γ) p
  have pq := unit_positive (Γ := Γ) q
  have pt := unit_positive (Γ := Γ) t
  have left := scalar_upper _ _ _ _ (positive_product _ _ pp pt) (point_at F x p t hF)
  have right := scalar_upper _ _ _ _ (positive_product _ _ pt pq) (point_at H y t q hH)
  have center := cofinal t
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left center) right
  apply remove_upper_slack _ _ _ _ C
  apply upper_mono _ _ _ _ _ _ (positive_product _ _
    (positive_product _ _ (positive_product _ _ pp pt) (positive_product _ _ hD pt))
    (positive_product _ _ pt pq)) joined
  apply le_of_eq_add (d := zero)
  dsimp only [upperSlack,rateNumerator,rateDenominator,C,t]
  ipra_ring

theorem delta_real (i r b : PTm n) : Γ ⊢[PRAAx] realSamples deltaF (deltaData i r b) :=
  GaussianStirlingNames.add_real _ _ _ _
    (GaussianStirlingNames.log_gamma_real (shiftedNumerator i r b) b)
    (GaussianNamedDampingPowerRealSamples.negative_real _ _ (GaussianStirlingNames.log_gamma_real i one))

theorem slope_real (i r b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realSamples slopeF (slopeData i r b) :=
  GaussianStirlingNames.multiply_real _ _ _ _
    (GaussianStirlingNames.constant_real (fraction r b) (GaussianRationalHorner.ofGaussian_canonical _ _ hb)
      (GaussianStirlingNames.fraction_axis r b hb))
    (GaussianStirlingNames.log_x_real i one)

theorem increment_at (i r b p q : PTm n) (hi : Γ ⊢[PRAAx] le two i)
    (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le one r) (hrb : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] distanceBounded (δ p i r b) (σ q i r b)
      (rateNumerator one (pred i) p q) (rateDenominator (pred i) p q) := by
  let k := pred i
  let D := rateDenominator k p q
  let A := rateNumerator one k p q
  let x := deltaData i r b
  let y := slopeData i r b
  have kk := pred_positive i hi
  have ii := le_trans RationalAlgebra.two_positive hi
  have dx := delta_regular i r b ii hb
  have sy := slope_regular i r b ii
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (positive_product _ _ kk (unit_positive p)) (unit_positive q)
  have hs := named_upper_at deltaF slopeF x y k (cofinalCost i r b) p q dx sy kk
    (fun t => upper_cofinal i r b t hi hb hr hrb)
  have ht := named_upper_at slopeF deltaF y x k (cofinalCost i r b) q p sy dx kk
    (fun t => lower_cofinal i r b t hi hb hr hrb)
  have ht' : Γ ⊢[PRAAx] upper (fstT (σ q i r b)) (fstT (δ p i r b)) A D :=
    upper_congr (.eqRefl _) (.eqRefl _) (by dsimp [A,rateNumerator]; ipra_ring)
      (by dsimp [D,rateDenominator]; ipra_ring) ht
  have rho := radius_of_upper _ _ _ _ hs ht'
  have hx := real_sample_at deltaF x p (delta_real (Γ := Γ) i r b)
  have hy := real_sample_at slopeF y q (slope_real i r b hb)
  exact distance_congr (RationalGaussianEmbedding.canonical_axis_roundtrip _ hx.andE₁ hx.andE₂)
    (RationalGaussianEmbedding.canonical_axis_roundtrip _ hy.andE₁ hy.andE₂) (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ A D hD rho)

theorem increment_rate (i r b : PTm n) (hi : Γ ⊢[PRAAx] le two i)
    (hb : Γ ⊢[PRAAx] le one b) (hr : Γ ⊢[PRAAx] le one r) (hrb : Γ ⊢[PRAAx] le r b) :
    Γ ⊢[PRAAx] incrementRate i r b := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let I := Syn.shift (Syn.shift i)
  let R := Syn.shift (Syn.shift r)
  let B := Syn.shift (Syn.shift b)
  refine .allI (.allI ?_)
  have hI : Δ ⊢[PRAAx] le two I := by simpa [Δ,I,Fm.shift,Syn.shift] using hi.shift.shift
  have hB : Δ ⊢[PRAAx] le one B := by simpa [Δ,B,Fm.shift,Syn.shift] using hb.shift.shift
  have hR : Δ ⊢[PRAAx] le one R := by simpa [Δ,R,Fm.shift,Syn.shift] using hr.shift.shift
  have hRB : Δ ⊢[PRAAx] le R B := by simpa [Δ,R,B,Fm.shift,Syn.shift] using hrb.shift.shift
  simpa [incrementRate,independentRate,I,R,B,Δ,Syn.shift] using
    increment_at (Γ := Δ) I R B (var 1) (var 0) hI hB hR hRB

theorem original_first_order (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianStirlingGlobalBounds.firstOrderBounds GaussianStirlingGlobalBounds.remainderF a b
      (GaussianStirlingGlobalBounds.remainderData a b x) :=
  first_order_from_increment a b x hs increment_rate

theorem original_rational_robbins (a b x : PTm n)
    (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] GaussianStirlingRobbins.bounds GaussianStirlingGlobalBounds.remainderF a b
      (GaussianStirlingGlobalBounds.remainderData a b x) :=
  rational_robbins_from_increment a b x hs hba increment_rate

theorem original_positive_series_remainder (N a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent GaussianStirlingGlobalBoundsRemainder.sumF
      GaussianStirlingGlobalBounds.remainderF (GaussianStirlingGlobalBoundsRemainder.sumData N a b x)
      (GaussianStirlingGlobalBounds.remainderData a b x) ⋏
      (GaussianNamedPositiveExponentialOrder.realOrder GaussianGammaCanonicalExponent.constantF
        GaussianStirlingGlobalBounds.remainderF qzero
        (GaussianStirlingGlobalBounds.remainderData (GaussianStirlingTelescope.shifted a b N) b x) ⋏
        GaussianNamedPositiveExponentialOrder.realOrder GaussianStirlingGlobalBounds.remainderF
          GaussianGammaCanonicalExponent.constantF
          (GaussianStirlingGlobalBounds.remainderData (GaussianStirlingTelescope.shifted a b N) b x)
          (GaussianStirlingRationalTelescopers.upperValue (GaussianStirlingTelescope.shifted a b N) b)) :=
  GaussianStirlingGlobalBoundsTranslatedRate.positive_series_remainder N a b x hs increment_rate

theorem actual_log_gamma_fractional_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le two (var 0) ⋏ (le one (var 2) ⋏ (le one (var 1) ⋏ le (var 1) (var 2)))) ⟶
      incrementRate (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (increment_rate _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

theorem actual_positive_rational_first_order_Stirling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ GaussianStirlingGlobalBounds.firstOrderBounds
      GaussianStirlingGlobalBounds.remainderF (var 0) (var 1)
      (GaussianStirlingGlobalBounds.remainderData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_first_order _ _ _ Prf.hyp0))

theorem actual_positive_rational_Robbins_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⋏ le (var 1) (var 0) ⟶ GaussianStirlingRobbins.bounds
      GaussianStirlingGlobalBounds.remainderF (var 0) (var 1)
      (GaussianStirlingGlobalBounds.remainderData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_rational_robbins _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_positive_rational_Stirling_series_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) ⟶
      GaussianNameEquivalence.crossEquivalent GaussianStirlingGlobalBoundsRemainder.sumF
        GaussianStirlingGlobalBounds.remainderF (GaussianStirlingGlobalBoundsRemainder.sumData (var 0) (var 1) (var 2) (var 3))
        (GaussianStirlingGlobalBounds.remainderData (var 1) (var 2) (var 3)) ⋏
      (GaussianNamedPositiveExponentialOrder.realOrder GaussianGammaCanonicalExponent.constantF
        GaussianStirlingGlobalBounds.remainderF qzero
        (GaussianStirlingGlobalBounds.remainderData (GaussianStirlingTelescope.shifted (var 1) (var 2) (var 0)) (var 2) (var 3)) ⋏
      GaussianNamedPositiveExponentialOrder.realOrder GaussianStirlingGlobalBounds.remainderF
        GaussianGammaCanonicalExponent.constantF
        (GaussianStirlingGlobalBounds.remainderData (GaussianStirlingTelescope.shifted (var 1) (var 2) (var 0)) (var 2) (var 3))
        (GaussianStirlingRationalTelescopers.upperValue (GaussianStirlingTelescope.shifted (var 1) (var 2) (var 0)) (var 2)))) :=
  closeUniv 4 (.impI (original_positive_series_remainder _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrement
