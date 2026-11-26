import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartUniformEndpoints
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPowerChartRoundedEndpoints

/-!
# Cofinality of the original rounded chart on a uniform physical panel

The physical endpoints are chosen from magnitude bounds. The rounded
image still encloses the required Euler interval at any precision that
pays the node correction and both chart observation allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartUniformRounded

open_ipra
open GaussianEulerPositivePowerChart (nameF data)
open GaussianEulerPowerChartCofinalEndpoints (lowerDenominator upperNumerator width)
open GaussianEulerPowerChartUniformEndpoints (source uniform_physical_panel uniform_endpoint_order uniform_reference_bounds)
open GaussianEulerPowerChartRoundedEndpoints (chartBudget)
open GaussianEulerPositivePowerChartMesh (node timeNumerator timeDenominator node_source)
open GaussianEulerPositivePowerChartImage (query)
open GaussianEulerPositivePowerChartCorrectedImage (imageNumerator imageDenominator imageFraction)
open GaussianEulerPowerChartRationalPowers (chart_proper)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_congr upper_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.CoprimeModulus (pos_of_one_le)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem uniform_mesh_source (e f d h Q S H C V N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S H C V) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S
      (lowerDenominator S V H) (upperNumerator C V H) one (width H C S V) N := by
  have physical := uniform_physical_panel S H C V hs.andE₁.andE₂.andE₂.andE₁.andE₂
    hs.andE₂.andE₁.andE₁ hs.andE₂.andE₁.andE₂ hs.andE₂.andE₂.andE₂
  exact .andI hs.andE₁ (.andI physical.andE₁ (.andI (le_refl _)
    (.andI (le_congr physical.andE₂.andE₂.andE₂.eqSymm (.eqRefl _) (le_refl _)) hN)))

private theorem grid_orders (e f d h Q S H C V N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S H C V) (hN : Γ ⊢[PRAAx] le one N) :
    let E := lowerDenominator S V H
    let W := width H C S V
    let D := timeDenominator N E
    Γ ⊢[PRAAx] realOrder nameF constantF (data e f d h S (timeNumerator zero N one W) D) (fraction d (h*(S*V))) ⋏
      realOrder constantF nameF (fraction (d*(C*V)) h) (data e f d h S (timeNumerator N N one W) D) := by
  let E := lowerDenominator S V H
  let T := upperNumerator C V H
  let W := width H C S V
  let D := timeDenominator N E
  let a := timeNumerator zero N one W
  let b := timeNumerator N N one W
  let L := fraction d (h*(S*V))
  let U := fraction (d*(C*V)) h
  have physical := uniform_physical_panel S H C V hs.andE₁.andE₂.andE₂.andE₁.andE₂
    hs.andE₂.andE₁.andE₁ hs.andE₂.andE₁.andE₂ hs.andE₂.andE₂.andE₂
  have hE : Γ ⊢[PRAAx] le one E := physical.andE₁
  have hT : Γ ⊢[PRAAx] le one T := physical.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE hN
  have ea : Γ ⊢[PRAAx] a ≐ N := by unfold a timeNumerator; ipra_ring
  have eb : Γ ⊢[PRAAx] b ≐ (T*E)*N :=
    (by unfold b timeNumerator; ipra_ring : Γ ⊢[PRAAx] b ≐ (one+W)*N).eqTrans
      (congrMul physical.andE₂.andE₂.andE₂ (.eqRefl N))
  have ha : Γ ⊢[PRAAx] le one a := le_congr (.eqRefl _) ea.eqSymm hN
  have hb : Γ ⊢[PRAAx] le one b :=
    le_congr (.eqRefl _) eb.eqSymm (positive_product _ _ (positive_product _ _ hT hE) hN)
  have el : Γ ⊢[PRAAx] a*E ≐ D*one :=
    (congrMul ea (.eqRefl E)).eqTrans (by unfold D timeDenominator; ipra_ring)
  have er : Γ ⊢[PRAAx] b*one ≐ D*T :=
    (congrMul eb (.eqRefl one)).eqTrans (by unfold D timeDenominator; ipra_ring)
  have left := chart_proper e f d h Q S a D one E hs.andE₁ (.andI ha hD) (.andI (le_refl _) hE) el
  have right := chart_proper e f d h Q S b D T one hs.andE₁ (.andI hb hD) (.andI hT (le_refl _)) er
  have ends := uniform_endpoint_order e f d h Q S H C V hs
  have self (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF constantF x x :=
    GaussianNameEquivalence.cross_refl _ _ (GaussianGammaCanonicalExponent.constant_regular _)
  exact .andI
    (GaussianNamedRealOrderTransport.transport nameF nameF constantF constantF
      (data e f d h S a D) (data e f d h S one E) L L left (self L) ends.andE₁)
    (GaussianNamedRealOrderTransport.transport constantF constantF nameF nameF
      U U (data e f d h S T one) (data e f d h S b D) (self U)
      (cross_symm _ _ _ _ right) ends.andE₂)

private theorem observation_displacement (k i e f d h Q S E T a W N : PTm n)
    (hm : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T a W N)
    (hi : Γ ⊢[PRAAx] le i N) :
    let p := query k h Q E T
    let raw := fstT (node k i e f d h Q S E T a W N)
    let corrected := fstT (imageFraction k i e f d h Q S E T a W N)
    Γ ⊢[PRAAx] upper corrected raw (two*N) (unit p) ⋏ upper raw corrected (two*N) (unit p) := by
  let p := query k h Q E T
  have eq := GaussianEulerPositivePowerChartImage.fraction_exact k e f d h Q S E T _ _
    (node_source i e f d h Q S E T a W N hm hi)
  have distance := GaussianEulerPositivePowerChartCorrectedImage.original_displacement k i e f d h Q S E T a W N hm hi
  have moved := GaussianRationalDistanceOrder.distance_congr (.eqRefl _) eq (.eqRefl _) (.eqRefl _) distance
  have hp : Γ ⊢[PRAAx] le one (unit p) := unit_positive p
  exact .andI (upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp moved))
    (upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp
      (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hp moved)))

private theorem pay_observation_errors (a b c A B p V : PTm n)
    (h₁ : Γ ⊢[PRAAx] upper a b A (unit p))
    (h₂ : Γ ⊢[PRAAx] upper b c B (unit p))
    (hk : Γ ⊢[PRAAx] le ((A+B)*V) (unit p)) :
    Γ ⊢[PRAAx] upper a c one V := by
  let U := unit p
  have combined := upper_triangle a b c A U B U h₁ h₂
  apply upper_mono _ _ _ _ _ _ (positive_product U U (unit_positive p) (unit_positive p)) combined
  exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right U hk)

private theorem cleared_allowance (a b c d V : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] upper (fstT (fraction a b)) (fstT (fraction c d)) one V) :
    Γ ⊢[PRAAx] le (V*d*a) (V*b*c+b*d) := by
  have repr (u v : PTm n) (hv : Γ ⊢[PRAAx] le one v) :
      Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction u v)) (ZT.ofNat u) v := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents (ComplexLogarithmRemainder.scale u ComplexLogarithmRemainder.oneCode) v hv).andE₁
    apply ZT.derive
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
    ring
  have signed := RationalUpperRepresentation.upper_from_representations _ _ b d one V (ZT.ofNat a) (ZT.ofNat c)
    (repr a b hb) (repr c d hd) h
  have se := zle_toZ signed
  apply le_of_eq_add (d := PolynomialBisection.slack (ZT.ofNat (V*d)*ZT.ofNat a)
    (ZT.ofNat (V*b)*ZT.ofNat c+ZT.ofNat (one*b*d)))
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at se
  simp only [PolynomialBisection.slack] at se ⊢
  ipra_simps
  linear_combination -se

def containsImage (k e f d h Q S E T base W N A B : PTm n) : Fm PTm n :=
  let a := GaussianEulerPositivePowerChartCorrectedPanel.start k e f d h Q S E T base W N
  let D := GaussianEulerPositivePowerChartCorrectedPanel.denominator k e f d h Q S E T base W N
  let L := GaussianEulerPositivePowerChartCorrectedPanel.span k e f d h Q S E T base W N
  le (a*A) D ⋏ le (B*D) (a+L)

/-- Preserve an image enclosure using bounds at the two actual grid times. -/
theorem rounded_panel_of_orders (k e f d h Q S U V E T base W N A B : PTm n)
    (mesh : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T base W N)
    (hV : Γ ⊢[PRAAx] le one V)
    (hLeft : Γ ⊢[PRAAx] le (d*V) (h*(S*V)))
    (hRight : Γ ⊢[PRAAx] le (h*V) (d*(U*V)))
    (leftOrder : Γ ⊢[PRAAx] realOrder nameF constantF
      (data e f d h S (timeNumerator zero N base W) (timeDenominator N E)) (fraction d (h*(S*V))))
    (rightOrder : Γ ⊢[PRAAx] realOrder constantF nameF (fraction (d*(U*V)) h)
      (data e f d h S (timeNumerator N N base W) (timeDenominator N E)))
    (hA : Γ ⊢[PRAAx] le (two*A) V) (hB : Γ ⊢[PRAAx] le (B+one) V)
    (hk : Γ ⊢[PRAAx] le (chartBudget N V) (unit (query k h Q E T))) :
    Γ ⊢[PRAAx] containsImage k e f d h Q S E T base W N A B := by
  let p := query k h Q E T
  let a := imageNumerator k zero e f d h Q S E T base W N
  let b := imageDenominator k zero e f d h Q S E T base W N
  let c := imageNumerator k N e f d h Q S E T base W N
  let j := imageDenominator k N e f d h Q S E T base W N
  let L := fraction d (h*(S*V))
  let R := fraction (d*(U*V)) h
  have hh := mesh.andE₁.andE₂.andE₁.andE₂
  have hS := mesh.andE₁.andE₂.andE₂.andE₁.andE₂
  have hL := positive_product h (S*V) hh (positive_product S V hS hV)
  have paid : Γ ⊢[PRAAx] le (two*N) (chartBudget N V) := by
    unfold chartBudget
    ipra_le 𝔞(two*N)*sl hV+𝔞(two*V)
  have good : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartCorrectedImage.input k e f d h Q S E T base W N :=
    .andI mesh (le_trans paid hk)
  have hb := (GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k zero e f d h Q S E T base W N
    good (zero_le N)).andE₁.andE₂
  have hj := (GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k N e f d h Q S E T base W N
    good (le_refl N)).andE₁.andE₂
  have lowerChart := upper_congr (.eqRefl _) (congrFst (constant_at p L)) (.eqRefl _) (.eqRefl _)
    (real_order_at nameF constantF _ L p p leftOrder)
  have upperChart := upper_congr (congrFst (constant_at p R)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (real_order_at constantF nameF R _ p p rightOrder)
  have sameClock : Γ ⊢[PRAAx] le ((unit p+unit p)*unit p) (two*(unit p*unit p)) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_refl _)
  have hUnits : Γ ⊢[PRAAx] le one (unit p*unit p) :=
    positive_product (unit p) (unit p) (unit_positive p) (unit_positive p)
  have before := upper_mono _ _ _ _ two (unit p) hUnits lowerChart sameClock
  have after := upper_mono _ _ _ _ two (unit p) hUnits upperChart sameClock
  have leftShift := (observation_displacement k zero e f d h Q S E T base W N mesh (zero_le N)).andE₁
  have rightShift := (observation_displacement k N e f d h Q S E T base W N mesh (le_refl N)).andE₂
  have leftError : Γ ⊢[PRAAx] upper (fstT (fraction a b)) (fstT L) one V :=
    pay_observation_errors _ _ _ (two*N) two p V leftShift before hk
  have rearranged : Γ ⊢[PRAAx] le ((two+two*N)*V) (unit p) :=
    le_congr (by unfold chartBudget; ipra_ring) (.eqRefl _) hk
  have rightError : Γ ⊢[PRAAx] upper (fstT R) (fstT (fraction c j)) one V :=
    pay_observation_errors _ _ _ two (two*N) p V after rightShift rearranged
  have lowerNative := cleared_allowance a b d (h*(S*V)) V hb hL leftError
  have lowerClear : Γ ⊢[PRAAx] le ((h*(S*V))*(V*a)) ((h*(S*V))*(two*b)) := by
    ipra_le sl lowerNative+𝔞 b*sl hLeft
  have leftCleared := le_cancel_pos (pos_of_one_le hL) lowerClear
  have low : Γ ⊢[PRAAx] le (a*A) b := by
    apply mul_le_cancel (d' := one)
    ipra_le 𝔞 a*sl hA+sl leftCleared
  have upperNative := cleared_allowance (d*(U*V)) h c j V hh hj rightError
  have upperClear : Γ ⊢[PRAAx] le (h*(V*V*j)) (h*(V*c+j)) := by
    ipra_le 𝔞(V*j)*sl hRight+sl upperNative
  have rightCleared := le_cancel_pos (pos_of_one_le hh) upperClear
  have high : Γ ⊢[PRAAx] le (B*j) c := by
    have bound : Γ ⊢[PRAAx] le (V*(B*j)+j) (V*c+j) := by
      ipra_le 𝔞(V*j)*sl hB+𝔞 j*sl hV+sl rightCleared
    exact le_cancel_pos (pos_of_one_le hV) (le_of_add_le_add_right bound)
  have lower : Γ ⊢[PRAAx] le ((a*j)*A) (b*j) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right j low)
  have upper : Γ ⊢[PRAAx] le (B*(b*j)) (c*b) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right b high)
  exact .andI lower (le_congr (.eqRefl _)
    (GaussianEulerPositivePowerChartCorrectedPanel.endpoint_identity k e f d h Q S E T base W N mesh).eqSymm upper)

def containsPanel (k e f d h Q S H C V N A B : PTm n) : Fm PTm n :=
  containsImage k e f d h Q S (lowerDenominator S V H) (upperNumerator C V H) one (width H C S V) N A B

theorem original_uniform_rounded_panel (k e f d h Q S H C V N A B : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S H C V) (hN : Γ ⊢[PRAAx] le one N)
    (hA : Γ ⊢[PRAAx] le (two*A) V) (hB : Γ ⊢[PRAAx] le (B+one) V)
    (hk : Γ ⊢[PRAAx] le (chartBudget N V)
      (unit (query k h Q (lowerDenominator S V H) (upperNumerator C V H)))) :
    Γ ⊢[PRAAx] containsPanel k e f d h Q S H C V N A B := by
  have hV : Γ ⊢[PRAAx] le one V := le_trans (le_succ_self one) hs.andE₂.andE₂.andE₂
  have mesh := uniform_mesh_source e f d h Q S H C V N hs hN
  have bounds := uniform_reference_bounds d h S C V hs.andE₁.andE₂.andE₂.andE₂.andE₂ hs.andE₂.andE₂.andE₁.andE₂
  have endpoints := grid_orders e f d h Q S H C V N hs hN
  exact rounded_panel_of_orders k e f d h Q S C V _ _ one _ N A B mesh hV
    bounds.andE₁ bounds.andE₂ endpoints.andE₁ endpoints.andE₂ hA hB hk

theorem actual_original_uniform_rounded_power_chart_panel_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (((source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏ le one (var 10)) ⋏
        ((le (two*var 11) (var 9) ⋏ le (var 12+one) (var 9)) ⋏
          le (chartBudget (var 10) (var 9)) (unit (query (var 0) (var 4) (var 5)
            (lowerDenominator (var 6) (var 9) (var 7)) (upperNumerator (var 8) (var 9) (var 7)))))) ⟶
        containsPanel (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
          (var 10) (var 11) (var 12)) :=
  closeUniv 13 (.impI (original_uniform_rounded_panel _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁.andE₁
    Prf.hyp0.andE₂.andE₁.andE₂ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartUniformRounded
