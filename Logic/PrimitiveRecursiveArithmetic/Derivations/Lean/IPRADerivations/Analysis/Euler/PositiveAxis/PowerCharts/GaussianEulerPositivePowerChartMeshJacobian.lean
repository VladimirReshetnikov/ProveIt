import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartMesh
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartJacobian

/-!
# Corrected image-cell widths versus the actual evaluated Jacobian

The exact scalar tilt normalization is retained by embedding the actual
computed corrected nodes. Its one-cell difference is exactly 2/2^query.
The original chart increment therefore supplies a source-only Jacobian
remainder with six original observation units plus two tilt units.
Repeated raw nodes have exactly the artificial tilt width; in particular
a zero physical panel is never claimed to have zero corrected width.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartMeshJacobian

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartMesh (source timeNumerator timeDenominator node correctedNode node_source time_domain)
open GaussianEulerPositivePowerChartImage (query)
open GaussianRationalHorner (qadd qmul positive_product canonical_unique)
open GaussianRationalMetric (qsub distanceBounded bounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def input (e f d h Q S E T a C N : PTm n) : Fm PTm n := source e f d h Q S E T a C N ⋏ le (((Q+one)+one)*C) (a*N)
def correctedPoint (p i e f d h Q S E T a C N : PTm n) : PTm n := RationalGaussianEmbedding.embed (correctedNode p i e f d h Q S E T a C N)
def width (p i e f d h Q S E T a C N : PTm n) : PTm n :=
  qsub (correctedPoint p (succ i) e f d h Q S E T a C N) (correctedPoint p i e f d h Q S E T a C N)
def jacobian (p i e f d h Q S E T a C N : PTm n) : PTm n :=
  GaussianEulerPositivePowerChartJacobian.run (query p h Q E T) e f d h S (timeNumerator i N a C) (timeDenominator N E)
def linearTerm (p i e f d h Q S E T a C N : PTm n) : PTm n := qmul (jacobian p i e f d h Q S E T a C N) (fraction C (timeDenominator N E))
def numerator (p h Q S E T C N : PTm n) : PTm n :=
  (E*E)*GaussianEulerPositivePowerChartJacobian.curvature Q S E T C*(unit (query p h Q E T)*unit (query p h Q E T))+
    num 8*(timeDenominator N E*timeDenominator N E)*unit (query p h Q E T)
def denominator (p h Q E T N : PTm n) : PTm n :=
  (timeDenominator N E*timeDenominator N E)*(unit (query p h Q E T)*unit (query p h Q E T))

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (e f d h Q S E T a C N : PTm n) :
    (input e f d h Q S E T a C N).subst σ = input (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h)
      (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [input]
@[simp] theorem subst_correctedPoint {m : ℕ} (σ : Fin n → PTm m) (p i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (correctedPoint p i e f d h Q S E T a C N) = correctedPoint (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [correctedPoint]
@[simp] theorem subst_width {m : ℕ} (σ : Fin n → PTm m) (p i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (width p i e f d h Q S E T a C N) = width (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [width]
@[simp] theorem subst_jacobian {m : ℕ} (σ : Fin n → PTm m) (p i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (jacobian p i e f d h Q S E T a C N) = jacobian (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [jacobian]
@[simp] theorem subst_linearTerm {m : ℕ} (σ : Fin n → PTm m) (p i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (linearTerm p i e f d h Q S E T a C N) = linearTerm (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [linearTerm]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p h Q S E T C N : PTm n) :
    Syn.subst σ (numerator p h Q S E T C N) = numerator (Syn.subst σ p) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) (Syn.subst σ N) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p h Q E T N : PTm n) :
    Syn.subst σ (denominator p h Q E T N) = denominator (Syn.subst σ p) (Syn.subst σ h) (Syn.subst σ Q)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ N) := by simp [denominator]

theorem corrected_point_at (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    correctedPoint p i e f d h Q S E T a C N ≐ qadd (node p i e f d h Q S E T a C N) (fraction (two*i) (unit (query p h Q E T))) := by
  have real := GaussianEulerPositivePowerChartLower.original_sample_real (query p h Q E T) e f d h S
    (timeNumerator i N a C) (timeDenominator N E) hs.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₁.andE₂
  exact (RationalGaussianEmbedding.embed_add _ _).eqTrans (qadd_congr
    (RationalGaussianEmbedding.canonical_axis_roundtrip _ real.andE₁ real.andE₂)
    (GaussianEulerDecayOrder.fraction_embedding _ _ (unit_positive _)))

theorem tilt_difference (i U : PTm n) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    qsub (fraction (two*succ i) U) (fraction (two*i) U) ≐ fraction two U := by
  have actual : Γ ⊢[PRAAx] GaussianRationalHorner.represents
      (qsub (fraction (two*succ i) U) (fraction (two*i) U))
      (GaussianRootAlgebra.sub (ComplexLogarithmRemainder.scale (two*succ i) ComplexLogarithmRemainder.oneCode)
        (ComplexLogarithmRemainder.scale (two*i) ComplexLogarithmRemainder.oneCode)) U :=
    GaussianRationalMetric.qsub_represents _ _ _ _ U hU
      (GaussianRationalHorner.ofGaussian_represents _ _ hU) (GaussianRationalHorner.ofGaussian_represents _ _ hU)
  apply canonical_unique _ _ (ComplexLogarithmRemainder.scale two ComplexLogarithmRemainder.oneCode) U
    (GaussianRationalMetric.qsub_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ hU) hU
    (hrv := GaussianRationalHorner.ofGaussian_represents _ _ hU)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) _ (.eqRefl _) actual
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring

/-- The complete one-cell tilt is literal, including repeated raw images. -/
theorem width_identity (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    width p i e f d h Q S E T a C N ≐
      qadd (qsub (node p (succ i) e f d h Q S E T a C N) (node p i e f d h Q S E T a C N))
        (fraction two (unit (query p h Q E T))) :=
  (qsub_congr (corrected_point_at p (succ i) e f d h Q S E T a C N hs) (corrected_point_at p i e f d h Q S E T a C N hs)).eqTrans
    ((GaussianNameArithmetic.sum_difference _ _ _ _).eqTrans (qadd_congr (.eqRefl _) (tilt_difference i _ (unit_positive _))))

theorem repeated_cell_width (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N)
    (he : Γ ⊢[PRAAx] node p (succ i) e f d h Q S E T a C N ≐ node p i e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    width p i e f d h Q S E T a C N ≐ fraction two (unit (query p h Q E T)) :=
  (width_identity p i e f d h Q S E T a C N hs).eqTrans
    ((qadd_congr ((qsub_congr he (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.ofGaussian_canonical _ _ (unit_positive _))))

theorem chart_time_congr (e f d h S a c b : PTm n) (he : Γ ⊢[PRAAx] a ≐ c) : Γ ⊢[PRAAx]
    GaussianEulerPositivePowerChart.data e f d h S a b ≐ GaussianEulerPositivePowerChart.data e f d h S c b := by
  simpa only [GaussianEulerPositivePowerChart.subst_data,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
    Prf.eqCongr1 (GaussianEulerPositivePowerChart.data (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h) (Syn.shift S) (var 0) (Syn.shift b)) he

theorem zero_physical_width (p i e f d h Q S E T a N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a zero N) : Γ ⊢[PRAAx]
    width p i e f d h Q S E T a zero N ≐ fraction two (unit (query p h Q E T)) :=
  repeated_cell_width p i e f d h Q S E T a zero N hs
    (congrAp2 GaussianEulerPositivePowerChart.nameF (.eqRefl _)
      (chart_time_congr e f d h S _ _ _ (by unfold timeNumerator; ipra_ring)))

theorem zero_physical_linear (p i e f d h Q S E T a N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a zero N) : Γ ⊢[PRAAx]
    linearTerm p i e f d h Q S E T a zero N ≐ GaussianRationalHorner.qzero := by
  let D := timeDenominator N E
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal ComplexLogarithmRemainder.zeroCode
      (ComplexLogarithmRemainder.scale zero ComplexLogarithmRemainder.oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring
  have frac : Γ ⊢[PRAAx] fraction zero D ≐ GaussianRationalHorner.qzero :=
    canonical_unique _ _ _ D (GaussianRationalHorner.ofGaussian_canonical _ _ hD) GaussianRationalSyntheticDivision.qzero_canonical hD
      (GaussianRationalHorner.ofGaussian_represents _ _ hD)
      (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _) (GaussianRationalHorner.zero_represents D))
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) frac).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)

/-- All local original Jacobian source guards are derived from the panel
and one native count/relative-step budget, independently of the row. -/
theorem original_step_source (i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    GaussianEulerPositivePowerChartJacobian.source e f d h Q S E T (timeNumerator i N a C) (timeDenominator N E) C := by
  have first := node_source i e f d h Q S E T a C N hs.andE₁ (le_trans (le_succ_self i) hi)
  have later := time_domain (succ i) e f d h Q S E T a C N hs.andE₁ hi
  have domainLater : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (timeNumerator i N a C+C) (timeDenominator N E) E T := by
    let body : Fm PTm (n+1) := GaussianCompactLogarithmBounds.domain (var 0) (Syn.shift (timeDenominator N E)) (Syn.shift E) (Syn.shift T)
    have initial : Γ ⊢[PRAAx] body.subst (Syn.inst (timeNumerator (succ i) N a C)) := by
      simpa only [body,GaussianCompactLogarithmBounds.subst_domain,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using later
    have changed := Prf.eqSubst1 body
      (by unfold timeNumerator; ipra_ring : Γ ⊢[PRAAx] timeNumerator (succ i) N a C ≐ timeNumerator i N a C+C) initial
    simpa only [body,GaussianCompactLogarithmBounds.subst_domain,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using changed
  exact .andI first (.andI domainLater (le_trans hs.andE₂ (le_add_right _ _)))

theorem raw_jacobian_bound (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (qsub (node p (succ i) e f d h Q S E T a C N) (node p i e f d h Q S E T a C N))
      (linearTerm p i e f d h Q S E T a C N)
      (GaussianEulerPositivePowerChartJacobian.numerator (query p h Q E T) (query p h Q E T) Q S E T (timeDenominator N E) C)
      (denominator p h Q E T N) := by
  have actual := GaussianEulerPositivePowerChartJacobian.original_jacobian_increment (query p h Q E T) (query p h Q E T)
    e f d h Q S E T (timeNumerator i N a C) (timeDenominator N E) C (original_step_source i e f d h Q S E T a C N hs hi)
  have next : Γ ⊢[PRAAx] node p (succ i) e f d h Q S E T a C N ≐
      ap2 GaussianEulerPositivePowerChart.nameF (query p h Q E T)
        (GaussianEulerPositivePowerChart.data e f d h S (timeNumerator i N a C+C) (timeDenominator N E)) :=
    congrAp2 _ (.eqRefl _) (chart_time_congr e f d h S _ _ _ (by unfold timeNumerator; ipra_ring))
  exact GaussianRationalDistanceOrder.distance_congr (qsub_congr next (.eqRefl _)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) actual

/-- The actual corrected image width versus the actual Jacobian times
C/(E*N), with exactly eight observation/tilt units. -/
theorem original_cell_bound (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (width p i e f d h Q S E T a C N) (linearTerm p i e f d h Q S E T a C N)
      (numerator p h Q S E T C N) (denominator p h Q E T N) := by
  let U := unit (query p h Q E T)
  let D := timeDenominator N E
  let raw := qsub (node p (succ i) e f d h Q S E T a C N) (node p i e f d h Q S E T a C N)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hs.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂.andE₂.andE₂
  have hU := unit_positive (Γ := Γ) (query p h Q E T)
  have hDen : Γ ⊢[PRAAx] le one (denominator p h Q E T N) := positive_product _ _ (positive_product _ _ hD hD) (positive_product _ _ hU hU)
  have fracBound : Γ ⊢[PRAAx] bounded (fraction two U) two U :=
    GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point two U hU).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded two U hU)
  have delta : Γ ⊢[PRAAx] distanceBounded (width p i e f d h Q S E T a C N) raw two U :=
    GaussianRationalReciprocal.bound_congr
      ((qsub_congr (width_identity p i e f d h Q S E T a C N hs.andE₁) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qadd_sub_cancel raw (fraction two U) (GaussianRationalHorner.ofGaussian_canonical _ _ hU))).eqSymm
      (.eqRefl _) (.eqRefl _) fracBound
  have lifted := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ (two*(D*D)*U) (denominator p h Q E T N) hU hDen
    (le_of_eq_add (d := zero) (by unfold denominator; dsimp only [D,U]; ipra_ring)) delta
  have joined := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hDen lifted (raw_jacobian_bound p i e f d h Q S E T a C N hs hi)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold numerator GaussianEulerPositivePowerChartJacobian.numerator; dsimp only [D,U]; ipra_ring) (.eqRefl _) joined

theorem actual_original_chart_corrected_Jacobian_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    ((input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏ lt (var 1) (var 12)) ⟶
      distanceBounded (width (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (linearTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (numerator (var 0) (var 5) (var 6) (var 7) (var 8) (var 9) (var 11) (var 12))
        (denominator (var 0) (var 5) (var 6) (var 8) (var 9) (var 12))) :=
  closeUniv 13 (.impI (original_cell_bound _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_zero_physical_panel_corrected_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) zero (var 11) ⟶
      (width (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) zero (var 11) ≐
        fraction two (unit (query (var 0) (var 5) (var 6) (var 8) (var 9))) ⋏
       linearTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) zero (var 11) ≐ GaussianRationalHorner.qzero)) :=
  closeUniv 12 (.impI (.andI (zero_physical_width _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0) (zero_physical_linear _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartMeshJacobian
