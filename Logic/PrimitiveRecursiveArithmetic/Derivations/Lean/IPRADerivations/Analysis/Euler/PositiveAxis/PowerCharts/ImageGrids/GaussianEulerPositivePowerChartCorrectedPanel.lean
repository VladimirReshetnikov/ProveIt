import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartCorrectedImage

/-!
# Exact ordered rational panel of the corrected positive chart

The two literal decoded endpoint denominators are multiplied, rather
than identifying independently normalized codes. Native cross order
comes from original chart order and the exact index tilt. Every decoded
corrected node lies in this actual rational panel, including repeated
nodes and zero span. No positive span is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartCorrectedPanel

open_ipra
open GaussianEulerPositivePowerChartMesh (source node timeNumerator timeDenominator node_source time_domain)
open GaussianEulerPositivePowerChartCorrectedImage (input imageNumerator imageDenominator imageFraction imageData)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPositivePowerChart (majorant)
open GaussianUnitIntervalInputDecoding (numerator denominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def start (k e f d h Q S E T a C N : PTm n) : PTm n :=
  imageNumerator k zero e f d h Q S E T a C N*imageDenominator k N e f d h Q S E T a C N
def denominator (k e f d h Q S E T a C N : PTm n) : PTm n :=
  imageDenominator k zero e f d h Q S E T a C N*imageDenominator k N e f d h Q S E T a C N
def endpoint (k e f d h Q S E T a C N : PTm n) : PTm n :=
  imageNumerator k N e f d h Q S E T a C N*imageDenominator k zero e f d h Q S E T a C N
def span (k e f d h Q S E T a C N : PTm n) : PTm n := monus (endpoint k e f d h Q S E T a C N) (start k e f d h Q S E T a C N)

private theorem scalar_fraction_represents (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (fraction A B)) (ZT.ofNat A) B := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents (ComplexLogarithmRemainder.scale A ComplexLogarithmRemainder.oneCode) B hB).andE₁
  apply ZT.derive
  simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
  ring

private theorem raw_represents (k i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (node k i e f d h Q S E T a C N))
      (ZT.ofNat (numerator (node k i e f d h Q S E T a C N))) (GaussianUnitIntervalInputDecoding.denominator (node k i e f d h Q S E T a C N)) :=
  GaussianRationalHorner.scalar_congr
    (congrFst (GaussianEulerPositivePowerChartImage.fraction_exact k e f d h Q S E T _ _ (node_source i e f d h Q S E T a C N hs hi)))
    (ZT.derive rfl) (.eqRefl _) (scalar_fraction_represents _ _ (GaussianUnitIntervalInputDecoding.denominator_positive _))

/-- Every strictly later index absorbs the original two-query order slack. -/
theorem original_native_order (k i j e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hij : Γ ⊢[PRAAx] lt i j) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    le (imageNumerator k i e f d h Q S E T a C N*imageDenominator k j e f d h Q S E T a C N)
      (imageNumerator k j e f d h Q S E T a C N*imageDenominator k i e f d h Q S E T a C N) := by
  let U := unit (query k h Q E T)
  let A := numerator (node k i e f d h Q S E T a C N)
  let B := GaussianUnitIntervalInputDecoding.denominator (node k i e f d h Q S E T a C N)
  let V := numerator (node k j e f d h Q S E T a C N)
  let W := GaussianUnitIntervalInputDecoding.denominator (node k j e f d h Q S E T a C N)
  have hi := le_trans (le_trans (le_succ_self i) hij) hj
  have first := node_source i e f d h Q S E T a C N hs hi
  have second := time_domain j e f d h Q S E T a C N hs hj
  have times : Γ ⊢[PRAAx] le (timeNumerator i N a C*timeDenominator N E) (timeDenominator N E*timeNumerator j N a C) := by
    unfold timeNumerator timeDenominator
    ipra_le 𝔞(E*N*C)*sl (le_trans (le_succ_self i) hij)
  have actual := GaussianEulerPositivePowerChartOrder.original_observations (query k h Q E T) (query k h Q E T)
    e f d h Q S E T _ _ _ _ (.andI first (.andI second times))
  have upper := RationalValueBounds.upper_mono _ _ _ _ two U (positive_product _ _ (unit_positive _) (unit_positive _)) actual
    (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring))
  have signed := RationalUpperRepresentation.upper_from_representations _ _ B W two U (ZT.ofNat A) (ZT.ofNat V)
    (raw_represents k i e f d h Q S E T a C N hs hi) (raw_represents k j e f d h Q S E T a C N hs hj) upper
  have se := zle_toZ signed
  have native : Γ ⊢[PRAAx] le (U*A*W) (U*V*B+two*B*W) := by
    apply le_of_eq_add (d := PolynomialBisection.slack (ZT.ofNat (U*W)*ZT.ofNat A) (ZT.ofNat (U*B)*ZT.ofNat V+ZT.ofNat (two*B*W)))
    apply deriveNat
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at se
    simp only [PolynomialBisection.slack] at se ⊢
    ipra_simps
    linear_combination -se
  unfold imageNumerator imageDenominator
  dsimp only [U,A,B,V,W] at native ⊢
  ipra_le 𝔞(unit (query k h Q E T))*sl native+
    𝔞(two*GaussianUnitIntervalInputDecoding.denominator (node k i e f d h Q S E T a C N)*GaussianUnitIntervalInputDecoding.denominator (node k j e f d h Q S E T a C N)*unit (query k h Q E T))*sl hij

theorem native_order (k i j e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hij : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    le (imageNumerator k i e f d h Q S E T a C N*imageDenominator k j e f d h Q S E T a C N)
      (imageNumerator k j e f d h Q S E T a C N*imageDenominator k i e f d h Q S E T a C N) := by
  refine .orE (lt_or_eq_of_le hij) (original_native_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs.wk Prf.hyp0 hj.wk) ?_
  have sameA : (i ≐ j)::Γ ⊢[PRAAx] imageNumerator k i e f d h Q S E T a C N ≐ imageNumerator k j e f d h Q S E T a C N := by
    simpa only [GaussianEulerPositivePowerChartCorrectedImage.subst_imageNumerator,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
      Prf.eqCongr1 (imageNumerator (Syn.shift k) (var 0) (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h) (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift C) (Syn.shift N)) Prf.hyp0
  have sameB : (i ≐ j)::Γ ⊢[PRAAx] imageDenominator k i e f d h Q S E T a C N ≐ imageDenominator k j e f d h Q S E T a C N := by
    simpa only [GaussianEulerPositivePowerChartCorrectedImage.subst_imageDenominator,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
      Prf.eqCongr1 (imageDenominator (Syn.shift k) (var 0) (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h) (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift C) (Syn.shift N)) Prf.hyp0
  exact le_congr (.eqRefl _) (congrMul sameA sameB.eqSymm) (le_refl _)

theorem endpoint_identity (k e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    start k e f d h Q S E T a C N+span k e f d h Q S E T a C N ≐ endpoint k e f d h Q S E T a C N :=
  (eq_add_of_le (native_order k zero N e f d h Q S E T a C N hs (zero_le N) (le_refl N))).eqSymm

theorem left_endpoint (k e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    fraction (start k e f d h Q S E T a C N) (denominator k e f d h Q S E T a C N) ≐ imageFraction k zero e f d h Q S E T a C N := by
  have first := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k zero e f d h Q S E T a C N hs (zero_le N)
  have last := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k N e f d h Q S E T a C N hs (le_refl N)
  exact GaussianEulerPositivePowerChartJacobian.fraction_cancel _ _ _ first.andE₁.andE₂ last.andE₁.andE₂

theorem right_endpoint (k e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    fraction (start k e f d h Q S E T a C N+span k e f d h Q S E T a C N) (denominator k e f d h Q S E T a C N) ≐ imageFraction k N e f d h Q S E T a C N := by
  have first := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k zero e f d h Q S E T a C N hs (zero_le N)
  have last := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k N e f d h Q S E T a C N hs (le_refl N)
  exact (GaussianEulerPositivePowerChartJacobian.fraction_congr (endpoint_identity k e f d h Q S E T a C N hs.andE₁) (by unfold denominator; ipra_ring)).eqTrans
    (GaussianEulerPositivePowerChartJacobian.fraction_cancel _ _ _ last.andE₁.andE₂ first.andE₁.andE₂)

theorem panel_geometry (k e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    (le one (start k e f d h Q S E T a C N) ⋏ le one (denominator k e f d h Q S E T a C N)) ⋏
      (le (denominator k e f d h Q S E T a C N) (reciprocalMargin h Q E T*start k e f d h Q S E T a C N) ⋏
        le (start k e f d h Q S E T a C N+span k e f d h Q S E T a C N) ((majorant Q S E T+one)*denominator k e f d h Q S E T a C N)) := by
  have first := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k zero e f d h Q S E T a C N hs (zero_le N)
  have last := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k N e f d h Q S E T a C N hs (le_refl N)
  refine .andI (.andI (positive_product _ _ first.andE₁.andE₁ last.andE₁.andE₂) (positive_product _ _ first.andE₁.andE₂ last.andE₁.andE₂)) (.andI ?_ ?_)
  · exact le_congr (.eqRefl _) (by unfold start; ipra_ring) (mul_le_mul_right _ first.andE₂.andE₁)
  · exact le_congr (endpoint_identity k e f d h Q S E T a C N hs.andE₁).eqSymm (by unfold denominator; ipra_ring)
      (mul_le_mul_right _ last.andE₂.andE₂)

theorem all_inside (k i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.inside (start k e f d h Q S E T a C N) (span k e f d h Q S E T a C N)
      (denominator k e f d h Q S E T a C N) (imageData k i e f d h Q S E T a C N) := by
  have dom := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k i e f d h Q S E T a C N hs hi
  have lo := native_order k zero i e f d h Q S E T a C N hs.andE₁ (zero_le i) hi
  have up := native_order k i N e f d h Q S E T a C N hs.andE₁ hi (le_refl N)
  have lower : Γ ⊢[PRAAx] le (start k e f d h Q S E T a C N*imageDenominator k i e f d h Q S E T a C N)
      (denominator k e f d h Q S E T a C N*imageNumerator k i e f d h Q S E T a C N) :=
    le_congr (by unfold start; ipra_ring) (by unfold denominator; ipra_ring) (mul_le_mul_right (imageDenominator k N e f d h Q S E T a C N) lo)
  have upper : Γ ⊢[PRAAx] le (denominator k e f d h Q S E T a C N*imageNumerator k i e f d h Q S E T a C N)
      ((start k e f d h Q S E T a C N+span k e f d h Q S E T a C N)*imageDenominator k i e f d h Q S E T a C N) := by
    have rawUpper := mul_le_mul_right (imageDenominator k zero e f d h Q S E T a C N) up
    have leftEq : Γ ⊢[PRAAx] imageNumerator k i e f d h Q S E T a C N * imageDenominator k N e f d h Q S E T a C N *
        imageDenominator k zero e f d h Q S E T a C N ≐ denominator k e f d h Q S E T a C N * imageNumerator k i e f d h Q S E T a C N := by
      unfold denominator
      ipra_ring
    exact le_congr leftEq
      ((by unfold endpoint; ipra_ring : Γ ⊢[PRAAx] imageNumerator k N e f d h Q S E T a C N * imageDenominator k i e f d h Q S E T a C N *
        imageDenominator k zero e f d h Q S E T a C N ≐ endpoint k e f d h Q S E T a C N*imageDenominator k i e f d h Q S E T a C N).eqTrans
        (congrMul (endpoint_identity k e f d h Q S E T a C N hs.andE₁).eqSymm (.eqRefl _)))
      rawUpper
  exact .andI (le_congr (.eqRefl _) (fst_pair _ _).eqSymm dom.andE₁.andE₁)
    (.andI (le_congr (.eqRefl _) (snd_pair _ _).eqSymm dom.andE₁.andE₂)
      (.andI (le_congr (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm lower)
        (le_congr (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm upper)))

theorem actual_corrected_power_chart_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⋏
      (le (var 1) (var 2) ⋏ le (var 2) (var 13))) ⟶
      le (imageNumerator (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) *
        imageDenominator (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))
        (imageNumerator (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) *
          imageDenominator (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))) :=
  closeUniv 14 (.impI (native_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_corrected_power_chart_nodes_inside_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    ((input (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏
      le (var 1) (var 12)) ⟶ GaussianCompactRiemannName.inside
      (start (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
      (span (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
      (denominator (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
      (imageData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))) :=
  closeUniv 13 (.impI (all_inside _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartCorrectedPanel
