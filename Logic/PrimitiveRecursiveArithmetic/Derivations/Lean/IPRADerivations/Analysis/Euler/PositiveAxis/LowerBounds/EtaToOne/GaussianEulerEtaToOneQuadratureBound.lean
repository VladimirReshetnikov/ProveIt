import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.EtaToOne.GaussianEulerEtaToOneRowBound
import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianUniformFiniteSumBound

/-!
# Finite original eta-to-one quadrature on the transformed root grid

The actual rows are grouped by the unchanged cut program. Both genuine
panel-width inequalities discharge the existing weighted block bound;
the original finite sum then gives its uniform radius. The sole local
analytic contract is the original sampled modulus on this interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerEtaToOneQuadratureBound

open_ipra
open GaussianEulerEtaToOneRootGrid (root rootDen time timeDen totalWidth right_guard)
open GaussianEulerEtaToOneRowBound (stepScale uniform_panel_width actual_row_norm_bound)
open GaussianEulerLowerTailPartition (cutF cutData offset offset_at panelWidth)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (sampleBody sampleData sampledModulus quadrature sample_body_at)
open GaussianRationalRiemannRefinement (weight weight_bound)
open GaussianUniformFiniteSumBound (summandsBounded uniform_sum_bound)
open GaussianRationalFiniteSum (sum sum_index_congr multiplyBody multiply_body_at)
open GaussianPartitionedFiniteSum (block blockBody block_at)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaIntegralCutoffs (height)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B H k e L : PTm n) : Fm PTm n := le one H ⋏
  (le one (totalWidth H k (succ e) R) ⋏ (GaussianEulerLowerPowerCoefficients.source z R B (succ e) ⋏
    sampledModulus evaluatorF (time zero H k (succ e) R) (totalWidth H k (succ e) R)
      (timeDen H k (succ e) R) L (fixedData z B)))
def gridData (s z R B H k e : PTm n) : PTm n := sampleData s (totalWidth H k (succ e) R)
  (time zero H k (succ e) R) (totalWidth H k (succ e) R) (timeDen H k (succ e) R) (fixedData z B)
def weightedPoint (H k e R : PTm n) : PTm n :=
  weight (totalWidth H k (succ e) R) (timeDen H k (succ e) R) (totalWidth H k (succ e) R)
def originalQuadrature (s z R B H k e : PTm n) : PTm n := quadrature evaluatorF s (totalWidth H k (succ e) R)
  (time zero H k (succ e) R) (totalWidth H k (succ e) R) (timeDen H k (succ e) R) (fixedData z B)
def weightedPanelBody : PTm 2 := multiplyBody (blockBody cutF (sampleBody evaluatorF))
def panelData (s z R B H k e : PTm n) : PTm n := pairT (weightedPoint H k e R)
  (pairT (cutData H zero (height k (succ e) R) (succ e)) (gridData s z R B H k e))

@[simp] private theorem subst_root {m : ℕ} (σ : Fin n → PTm m) (i H k A R : PTm n) :
    Syn.subst σ (root i H k A R) = root (Syn.subst σ i) (Syn.subst σ H) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [root,GaussianEulerLowerTailRootGrid.rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] private theorem subst_rootDen {m : ℕ} (σ : Fin n → PTm m) (H k A R : PTm n) :
    Syn.subst σ (rootDen H k A R) = rootDen (Syn.subst σ H) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [rootDen,GaussianEulerLowerTailRootGrid.rootDenominator,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] private theorem subst_time {m : ℕ} (σ : Fin n → PTm m) (i H k A R : PTm n) :
    Syn.subst σ (time i H k A R) = time (Syn.subst σ i) (Syn.subst σ H) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [time,GaussianEulerLowerTailRootGrid.timeNumerator,GaussianEulerLowerTailRootGrid.rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] private theorem subst_timeDen {m : ℕ} (σ : Fin n → PTm m) (H k A R : PTm n) :
    Syn.subst σ (timeDen H k A R) = timeDen (Syn.subst σ H) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [timeDen,GaussianEulerLowerTailRootGrid.timeDenominator,GaussianEulerLowerTailRootGrid.rootDenominator,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] private theorem subst_width {m : ℕ} (σ : Fin n → PTm m) (H k A R : PTm n) :
    Syn.subst σ (totalWidth H k A R) = totalWidth (Syn.subst σ H) (Syn.subst σ k) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [totalWidth,GaussianEulerLowerTailPartition.totalWidth,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] private theorem subst_panelWidth {m : ℕ} (σ : Fin n → PTm m) (i H p q A : PTm n) :
    Syn.subst σ (panelWidth i H p q A) = panelWidth (Syn.subst σ i) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) := by simp [panelWidth]
ipra_subst source
ipra_subst gridData
ipra_subst weightedPoint
ipra_subst panelData [height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem literal_weight (H k e R : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hW : Γ ⊢[PRAAx] le one (totalWidth H k (succ e) R)) : Γ ⊢[PRAAx]
    bounded (weightedPoint H k e R) one (rootDen H k (succ e) R*pw (rootDen H k (succ e) R) e) := by
  let W := totalWidth H k (succ e) R
  let E := timeDen H k (succ e) R
  have hD := GaussianEulerEtaToOneRootGrid.denominator_positive H k (succ e) R hH
  have hE : Γ ⊢[PRAAx] le one E := GaussianPolynomialPerturbation.power_positive _ (succ e) hD
  have eq : Γ ⊢[PRAAx] weight W E W ≐ weight W E (W*one) := GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring)
  have ew := eq.eqTrans (GaussianCompactRiemannSplit.weight_shared W E one hW hE (le_refl one))
  exact bound_congr ew.eqSymm (.eqRefl _)
    ((by ipra_ring : Γ ⊢[PRAAx] E*one ≐ E).eqTrans (GaussianEulerLowerTailRowBound.time_den_product H k e R))
    (weight_bound one E one hE (le_refl one))

theorem literal_panel_row (i j s z R B H k e : PTm n) : Γ ⊢[PRAAx]
    inst2 (offB (sampleBody evaluatorF)) j
      (pairT (offset i H zero (height k (succ e) R) (succ e)) (gridData s z R B H k e)) ≐
      ap3 evaluatorF s (GaussianEulerEtaToOneRowBound.rowTime i j H k (succ e) R) (fixedData z B) :=
  (GaussianRationalFiniteProduct.offset_at _ _ _ _).eqTrans (sample_body_at evaluatorF _ _ _ _ _ _ _)

theorem original_panel_rows (i s z R B H k e L : PTm n) (hi : Γ ⊢[PRAAx] lt i H)
    (h : Γ ⊢[PRAAx] source z R B H k e L) : Γ ⊢[PRAAx]
    summandsBounded (offB (sampleBody evaluatorF)) (panelWidth i H zero (height k (succ e) R) (succ e))
      (pairT (offset i H zero (height k (succ e) R) (succ e)) (gridData s z R B H k e))
      (GaussianEulerLowerBlockWeight.rowNumerator (rootDen H k (succ e) R) (pw (rootDen H k (succ e) R) e)
        (pw (root (succ i) H k (succ e) R) e) (stepScale k e R) L (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDen H k (succ e) R) (pw (root (succ i) H k (succ e) R) e) (unit s)) := by
  refine .allI (.impI ?_)
  have hi' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift H) := by simpa [Fm.shift,Syn.shift] using hi.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift k) (Syn.shift e) (Syn.shift L) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have row := actual_row_norm_bound (Syn.shift i) (var 0) (Syn.shift s) (Syn.shift H) (Syn.shift k) (Syn.shift e)
    (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift L) h'.andE₁.wk hi'.wk
    (by simpa [panelWidth,height,GaussianGammaIntegralCutoffs.tailCoefficient,Syn.shift] using (Prf.hyp0 : _ ⊢[PRAAx] lt (var 0) (Syn.shift (panelWidth i H zero (height k (succ e) R) (succ e)))) )
    h'.andE₂.andE₁.wk h'.andE₂.andE₂.andE₁.wk h'.andE₂.andE₂.andE₂.wk
  simpa [summandsBounded,panelWidth,stepScale,GaussianEulerEtaToOneRowBound.rootStep,height,GaussianGammaIntegralCutoffs.tailCoefficient,Syn.shift] using
    bound_congr (literal_panel_row (Syn.shift i) (var 0) (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift H) (Syn.shift k) (Syn.shift e)).eqSymm (.eqRefl _) (.eqRefl _) row

theorem panel_norm (i s z R B H k e L : PTm n) (hi : Γ ⊢[PRAAx] lt i H)
    (h : Γ ⊢[PRAAx] source z R B H k e L) : Γ ⊢[PRAAx]
    bounded (qmul (weightedPoint H k e R)
      (block cutF (sampleBody evaluatorF) i (cutData H zero (height k (succ e) R) (succ e)) (gridData s z R B H k e)))
      (GaussianEulerLowerBlockWeight.numerator (rootDen H k (succ e) R) (stepScale k e R) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDen H k (succ e) R) (unit s)) := by
  let D := rootDen H k (succ e) R
  let U := pw D e
  let V := pw (root (succ i) H k (succ e) R) e
  let S := stepScale k e R
  let P := unit s
  let J := panelWidth i H zero (height k (succ e) R) (succ e)
  let y := gridData s z R B H k e
  let f := sampleBody evaluatorF
  let d := cutData H zero (height k (succ e) R) (succ e)
  have hD := GaussianEulerEtaToOneRootGrid.denominator_positive H k (succ e) R h.andE₁
  have hU := GaussianPolynomialPerturbation.power_positive (Γ := Γ) D e hD
  have hV := GaussianPolynomialPerturbation.power_positive (Γ := Γ) _ e (right_guard i H k (succ e) R h.andE₁ hi).andE₁
  have hJU : Γ ⊢[PRAAx] le J (S*U) := le_congr (.eqRefl _)
    (by dsimp only [S,U,D]; unfold stepScale GaussianEulerEtaToOneRowBound.widthCap; ipra_ring) (uniform_panel_width i H k e R h.andE₁ hi)
  have hJV : Γ ⊢[PRAAx] le J (S*V) := GaussianEulerLowerTailRowBound.right_width i H zero (height k (succ e) R) e
  have hs : Γ ⊢[PRAAx] GaussianEulerLowerBlockWeight.source J D U V S P :=
    .andI hD (.andI hU (.andI hV (.andI (unit_positive s) (.andI hJV hJU))))
  have eq : Γ ⊢[PRAAx] block cutF f i d y ≐ sum (offB f) J (pairT (offset i H zero (height k (succ e) R) (succ e)) y) :=
    sum_index_congr _ (congrMonus (offset_at (succ i) H zero (height k (succ e) R) (succ e)) (offset_at i H zero (height k (succ e) R) (succ e)))
      (congrPairT (offset_at i H zero (height k (succ e) R) (succ e)) (.eqRefl y))
  exact bound_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) eq).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerLowerBlockWeight.finite_block_bound (offB f) (weightedPoint H k e R) _ J D U V S L P hs
      (literal_weight H k e R h.andE₁ h.andE₂.andE₁) (original_panel_rows i s z R B H k e L hi h))

theorem weighted_panel_at (i s z R B H k e : PTm n) : Γ ⊢[PRAAx]
    inst2 weightedPanelBody i (panelData s z R B H k e) ≐ qmul (weightedPoint H k e R)
      (block cutF (sampleBody evaluatorF) i (cutData H zero (height k (succ e) R) (succ e)) (gridData s z R B H k e)) :=
  (multiply_body_at _ _ _ _).eqTrans (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (block_at _ _ _ _ _))

theorem original_weighted_panels (s z R B H k e L : PTm n) (h : Γ ⊢[PRAAx] source z R B H k e L) : Γ ⊢[PRAAx]
    summandsBounded weightedPanelBody H (panelData s z R B H k e)
      (GaussianEulerLowerBlockWeight.numerator (rootDen H k (succ e) R) (stepScale k e R) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDen H k (succ e) R) (unit s)) := by
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift k) (Syn.shift e) (Syn.shift L) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have norm := panel_norm (var 0) (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift k) (Syn.shift e) (Syn.shift L) Prf.hyp0 h'.wk
  let Δ := lt (var 0) (Syn.shift H) :: Γ.map Fm.shift
  have value := weighted_panel_at (Γ := Δ) (var 0) (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift k) (Syn.shift e)
  simpa [Δ,summandsBounded,stepScale,GaussianEulerEtaToOneRowBound.rootStep,height,GaussianGammaIntegralCutoffs.tailCoefficient,Syn.shift] using
    bound_congr value.eqSymm (.eqRefl _) (.eqRefl _) norm

theorem original_weighted_sum (s z R B H k e : PTm n) : Γ ⊢[PRAAx]
    originalQuadrature s z R B H k e ≐ sum weightedPanelBody H (panelData s z R B H k e) :=
  (GaussianEulerEtaToOneRootGrid.grouped_original_quadrature evaluatorF s H k (succ e) R (fixedData z B)).eqTrans
    (GaussianRationalFiniteSum.sum_multiply _ _ _ _).eqSymm

theorem original_finite_bound (s z R B H k e L : PTm n) (h : Γ ⊢[PRAAx] source z R B H k e L) : Γ ⊢[PRAAx]
    bounded (originalQuadrature s z R B H k e)
      (H*GaussianEulerLowerBlockWeight.numerator (rootDen H k (succ e) R) (stepScale k e R) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDen H k (succ e) R) (unit s)) := by
  have hD := GaussianEulerEtaToOneRootGrid.denominator_positive H k (succ e) R h.andE₁
  have hY := positive_product (Γ := Γ) _ _ (positive_product _ _ hD hD) (unit_positive s)
  exact bound_congr (original_weighted_sum s z R B H k e).eqSymm (.eqRefl _) (.eqRefl _)
    (uniform_sum_bound weightedPanelBody H (panelData s z R B H k e) _ _ hY (original_weighted_panels s z R B H k e L h))

theorem actual_eta_to_one_original_finite_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      bounded (originalQuadrature (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (var 4*GaussianEulerLowerBlockWeight.numerator (rootDen (var 4) (var 5) (succ (var 6)) (var 2)) (stepScale (var 5) (var 6) (var 2)) (var 7) (unit (var 0)))
        (GaussianEulerLowerBlockWeight.denominator (rootDen (var 4) (var 5) (succ (var 6)) (var 2)) (unit (var 0)))) :=
  closeUniv 8 (.impI (original_finite_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerEtaToOneQuadratureBound
