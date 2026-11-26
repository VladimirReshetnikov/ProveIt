import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelPanelNameContinuity
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelPanelRescaling
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffAlignment
import IPRADerivations.Analysis.RationalArithmetic.RationalNativeFractionDisplacement
import IPRADerivations.AnalyticNumberTheory.PowerTransfer

/-!
# Endpoint continuity of the actual unit quadrature at different denominators

The native displacement premise bounds the cross products of each pair
of endpoints. Positive rescaling puts both representations at the common
denominator E*H. Exact rate transport then returns to the two original
compact programs at their independently requested output precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelRationalPanelContinuity

open_ipra
open GaussianEulerUnitKernelCompactName (nameF data)
open GaussianEulerUnitKernelPanelContinuity (leading)
open GaussianEulerUnitKernelPanelRescaling (source_rescaling original_rescaling)
open GaussianAffinePanelDisplacement (endpointSource)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (fraction)
open RationalValueBounds (radius)
open RationalNativeFractionDisplacement (native_absolute)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer (maxT le_maxT_l le_maxT_r maxT_cases)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (le_add_ad)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev panelSource (z R B a C E G : PTm n) : Fm PTm n := GaussianEulerUnitKernelCompactName.source z R B a C E G

def source (z R B a C E b D H G A : PTm n) : Fm PTm n :=
  panelSource z R B a C E G ⋏ (panelSource z R B b D H G ⋏ endpointSource (H*a) (H*C) (E*b) (E*D) A)

private theorem source_congr (z R B a C E E' G : PTm n) (e : Γ ⊢[PRAAx] E ≐ E')
    (h : Γ ⊢[PRAAx] panelSource z R B a C E G) : Γ ⊢[PRAAx] panelSource z R B a C E' G :=
  .andI h.andE₁ (.andI (le_congr (.eqRefl _) e h.andE₂.andE₁)
    (.andI (le_congr e (.eqRefl _) h.andE₂.andE₂.andE₁)
      (le_congr (congrAdd (.eqRefl _) e) (congrMul (.eqRefl _) e) h.andE₂.andE₂.andE₂)))

private theorem data_congr (z R B a C E E' G : PTm n) (e : Γ ⊢[PRAAx] E ≐ E') :
    Γ ⊢[PRAAx] data z R B a C E G ≐ data z R B a C E' G :=
  congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT e (.eqRefl _)))

theorem original_rate (z R B a C E b D H G A : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E b D H G A) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z R B a C E G) (data z R B b D H G) (leading R G A) (E*H) := by
  have he := h.andE₁.andE₂.andE₁
  have hh := h.andE₂.andE₁.andE₂.andE₁
  have eq : Γ ⊢[PRAAx] H*E ≐ E*H := mul_comm _ _
  have ls := source_congr _ _ _ _ _ _ _ _ eq (source_rescaling z R B a C E G H h.andE₁ hh)
  have rs := source_rescaling z R B b D H G E h.andE₂.andE₁ he
  have left := GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF _ _ _ _
    (.eqRefl _) (data_congr _ _ _ _ _ _ _ _ eq) (original_rescaling z R B a C E G H h.andE₁ hh)
  have right := original_rescaling z R B b D H G E h.andE₂.andE₁ he
  have comparison := GaussianEulerUnitKernelPanelNameContinuity.original_rate z R B (H*a) (H*C) (E*b) (E*D) (E*H) G A
    (.andI ls (.andI rs h.andE₂.andE₂))
  exact GaussianNamedRateTransport.transport nameF nameF nameF nameF _ _ _ _ _ _
    (positive_product _ _ he hh) comparison left right

theorem original_observations (p q z R B a C E b D H G A : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E b D H G A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B a C E G)) (ap2 nameF q (data z R B b D H G))
      (rateNumerator (leading R G A) (E*H) p q) (rateDenominator (E*H) p q) :=
  rate_at _ _ _ _ _ _ p q (original_rate z R B a C E b D H G A h)

theorem actual_unit_quadrature_rational_panel_endpoint_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      independentRate nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 9))
        (data (var 0) (var 1) (var 2) (var 6) (var 7) (var 8) (var 9))
        (leading (var 1) (var 9) (var 10)) (var 5*var 8)) :=
  closeUniv 11 (.impI (original_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

/-- The common cross-product displacement of the two endpoint pairs. -/
def endpointDisplacement (a C E b D H : PTm n) : PTm n :=
  maxT (ad (H*a) (E*b)) (ad (H*(a+C)) (E*(b+D)))

private theorem symmetric_native_bounds (x y K : PTm n) (h : Γ ⊢[PRAAx] le (ad x y) K) :
    Γ ⊢[PRAAx] le x (y+K) ⋏ le y (x+K) := by
  have backwards : Γ ⊢[PRAAx] le (ad y x) K :=
    le_congr (by unfold ad; ipra_ring) (.eqRefl _) h
  exact .andI (le_trans (le_add_ad x y) (add_le_add_left y h))
    (le_trans (le_add_ad y x) (add_le_add_left x backwards))

theorem native_endpoint_source (a C E b D H : PTm n) :
    Γ ⊢[PRAAx] endpointSource (H*a) (H*C) (E*b) (E*D) (endpointDisplacement a C E b D H) := by
  let K := endpointDisplacement a C E b D H
  have left : Γ ⊢[PRAAx] le (ad (H*a) (E*b)) K := le_maxT_l _ _
  have right : Γ ⊢[PRAAx] le (ad (H*(a+C)) (E*(b+D))) K := le_maxT_r _ _
  have bounds := symmetric_native_bounds (H*(a+C)) (E*(b+D)) K right
  exact .andI (symmetric_native_bounds (H*a) (E*b) K left)
    (.andI (le_congr (by ipra_ring) (by ipra_ring) bounds.andE₁)
      (le_congr (by ipra_ring) (by ipra_ring) bounds.andE₂))

theorem native_endpoint_budget (a C E b D H P Q : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hH : Γ ⊢[PRAAx] le one H)
    (hl : Γ ⊢[PRAAx] radius (fraction a E) (fraction b H) P Q)
    (hr : Γ ⊢[PRAAx] radius (fraction (a+C) E) (fraction (b+D) H) P Q) :
    Γ ⊢[PRAAx] le (Q*endpointDisplacement a C E b D H) (P*(E*H)) := by
  have left := native_absolute a E b H P Q hE hH hl
  have right := native_absolute (a+C) E (b+D) H P Q hE hH hr
  refine .orE (maxT_cases (ad (H*a) (E*b)) (ad (H*(a+C)) (E*(b+D)))) ?_ ?_
  · exact le_congr (congrMul (.eqRefl _) Prf.hyp0).eqSymm (.eqRefl _) left.wk
  · exact le_congr (congrMul (.eqRefl _) Prf.hyp0).eqSymm (.eqRefl _) right.wk

def endpointSourceRadius (z R B a C E b D H G P Q : PTm n) : Fm PTm n :=
  panelSource z R B a C E G ⋏ (panelSource z R B b D H G ⋏ (le one Q ⋏
    (radius (fraction a E) (fraction b H) P Q ⋏
      radius (fraction (a+C) E) (fraction (b+D) H) P Q)))

/-- Both endpoint bounds may share any external positive radius denominator.
The compact evaluator queries p and q keep their original exact errors. -/
theorem observations_at_radius (p q z R B a C E b D H G P Q : PTm n)
    (h : Γ ⊢[PRAAx] endpointSourceRadius z R B a C E b D H G P Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B a C E G)) (ap2 nameF q (data z R B b D H G))
      (rateNumerator (leading R G P) Q p q) (rateDenominator Q p q) := by
  let K := endpointDisplacement a C E b D H
  let L := GaussianEulerUnitKernelCompactRate.lipschitz R G+two*GaussianEulerUnitKernelCompactRate.majorant R G
  let M := E*H
  have he := h.andE₁.andE₂.andE₁
  have hh := h.andE₂.andE₁.andE₂.andE₁
  have hm : Γ ⊢[PRAAx] le one M := positive_product _ _ he hh
  have hq := h.andE₂.andE₂.andE₁
  have budget : Γ ⊢[PRAAx] le (Q*K) (P*M) :=
    native_endpoint_budget a C E b D H P Q he hh h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂
  have comparison := original_observations p q z R B a C E b D H G K
    (.andI h.andE₁ (.andI h.andE₂.andE₁ (native_endpoint_source a C E b D H)))
  refine distance_radius_mono _ _ _ _ _ _ (denominator_positive M p q hm) (denominator_positive Q p q hq) ?_ comparison
  change Γ ⊢[PRAAx] le (rateNumerator (L*K) M p q*rateDenominator Q p q)
    (rateNumerator (L*P) Q p q*rateDenominator M p q)
  unfold rateNumerator rateDenominator
  ipra_le 𝔞 L*𝔞 (unit p)^2*𝔞 (unit q)^2*sl budget

theorem actual_unit_quadrature_arbitrary_rational_endpoint_observations_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      (endpointSourceRadius (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
        (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
        distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 11)))
          (ap2 nameF (var 1) (data (var 2) (var 3) (var 4) (var 8) (var 9) (var 10) (var 11)))
          (rateNumerator (leading (var 3) (var 11) (var 12)) (var 13) (var 0) (var 1))
          (rateDenominator (var 13) (var 0) (var 1))) :=
  closeUniv 14 (.impI (observations_at_radius _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelRationalPanelContinuity
