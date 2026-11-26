import IPRADerivations.Analysis.Euler.GaussianEulerCompactLowerTail

/-!
# Reusing the original lower-root partition for an actual evaluator

Only the evaluator and its fixed data vary. All original root-grid
codes, cutF partition, weights, panel widths and block conversions are
unchanged. Actual uniform row bounds imply the original finite weighted
quadrature bound through the existing block/sum theorems. There is no
new recursor, geometry proof, integral or output-name premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianLowerRootQuadratureBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLowerTailRootGrid (rootDenominator rootNumerator timeNumerator timeDenominator)
open GaussianEulerLowerTailPartition (cutF cutData offset offset_at panelWidth totalWidth root_right_guard uniform_panel_width grouped_original_quadrature)
open GaussianEulerLowerTailRowBound (stepScale right_width)
open GaussianCompactRiemannName (sampleBody sampleData quadrature sample_body_at)
open GaussianUniformFiniteSumBound (summandsBounded uniform_sum_bound)
open GaussianRationalFiniteSum (sum sum_index_congr multiplyBody multiply_body_at)
open GaussianPartitionedFiniteSum (block blockBody block_at)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem subst_rootDenominator {m : ℕ} (σ : Fin n → PTm m) (H q A R : PTm n) :
    Syn.subst σ (rootDenominator H q A R) = rootDenominator (Syn.subst σ H) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [rootDenominator,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
private theorem subst_rootNumerator {m : ℕ} (σ : Fin n → PTm m) (i H p q : PTm n) :
    Syn.subst σ (rootNumerator i H p q) = rootNumerator (Syn.subst σ i) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) :=
  by simp [rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio]
private theorem subst_timeNumerator {m : ℕ} (σ : Fin n → PTm m) (i H p q A : PTm n) :
    Syn.subst σ (timeNumerator i H p q A) = timeNumerator (Syn.subst σ i) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) := by simp [timeNumerator,subst_rootNumerator]
private theorem subst_timeDenominator {m : ℕ} (σ : Fin n → PTm m) (H q A R : PTm n) :
    Syn.subst σ (timeDenominator H q A R) = timeDenominator (Syn.subst σ H) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) := by simp [timeDenominator,subst_rootDenominator]
attribute [local simp] subst_rootDenominator subst_rootNumerator subst_timeNumerator subst_timeDenominator

@[simp] private theorem subst_panelWidth {m : ℕ} (σ : Fin n → PTm m) (i H p q A : PTm n) :
    Syn.subst σ (panelWidth i H p q A) = panelWidth (Syn.subst σ i) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) := by simp [panelWidth]

def gridData (s H p q k R x : PTm n) : PTm n := sampleData s (totalWidth H p q (succ k)) (timeNumerator zero H p q (succ k))
  (totalWidth H p q (succ k)) (timeDenominator H q (succ k) R) x
def weightedPoint (H p q k R : PTm n) : PTm n := GaussianEulerCompactLowerTail.weightedPoint H p q k R
def originalQuadrature (F : PR 3) (s H p q k R x : PTm n) : PTm n := quadrature F s (totalWidth H p q (succ k))
  (timeNumerator zero H p q (succ k)) (totalWidth H p q (succ k)) (timeDenominator H q (succ k) R) x
def panelRows (F : PR 3) (s H p q k R L x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift H) ⟶ summandsBounded (offB (sampleBody F))
    (panelWidth (var 0) (Syn.shift H) (Syn.shift p) (Syn.shift q) (succ (Syn.shift k)))
    (pairT (offset (var 0) (Syn.shift H) (Syn.shift p) (Syn.shift q) (succ (Syn.shift k)))
      (gridData (Syn.shift s) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift R) (Syn.shift x)))
    (GaussianEulerLowerBlockWeight.rowNumerator (rootDenominator (Syn.shift H) (Syn.shift q) (succ (Syn.shift k)) (Syn.shift R))
      (pw (rootDenominator (Syn.shift H) (Syn.shift q) (succ (Syn.shift k)) (Syn.shift R)) (Syn.shift k))
      (pw (rootNumerator (succ (var 0)) (Syn.shift H) (Syn.shift p) (Syn.shift q)) (Syn.shift k))
      (stepScale (Syn.shift p) (Syn.shift q) (Syn.shift k)) (Syn.shift L) (unit (Syn.shift s)))
    (GaussianEulerLowerBlockWeight.rowDenominator (rootDenominator (Syn.shift H) (Syn.shift q) (succ (Syn.shift k)) (Syn.shift R))
      (pw (rootNumerator (succ (var 0)) (Syn.shift H) (Syn.shift p) (Syn.shift q)) (Syn.shift k)) (unit (Syn.shift s))))
def source (F : PR 3) (s H p q k R L x : PTm n) : Fm PTm n := le one H ⋏
  (le p q ⋏ (le one (totalWidth H p q (succ k)) ⋏ panelRows F s H p q k R L x))
@[simp] theorem subst_gridData {m : ℕ} (σ : Fin n → PTm m) (s H p q k R x : PTm n) :
    Syn.subst σ (gridData s H p q k R x) = gridData (Syn.subst σ s) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ R) (Syn.subst σ x) := by simp [gridData,totalWidth]
@[simp] theorem subst_panelRows {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (s H p q k R L x : PTm n) :
    (panelRows F s H p q k R L x).subst σ = panelRows F (Syn.subst σ s) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ x) :=
  by simp [panelRows,Syn.subst_shift,Syn.shift_subst,stepScale]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (s H p q k R L x : PTm n) :
    (source F s H p q k R L x).subst σ = source F (Syn.subst σ s) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ x) := by simp [source,totalWidth]

theorem panel_rows_at (F : PR 3) (i s H p q k R L x : PTm n) (h : Γ ⊢[PRAAx] panelRows F s H p q k R L x) (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    summandsBounded (offB (sampleBody F)) (panelWidth i H p q (succ k))
      (pairT (offset i H p q (succ k)) (gridData s H p q k R x))
      (GaussianEulerLowerBlockWeight.rowNumerator (rootDenominator H q (succ k) R) (pw (rootDenominator H q (succ k) R) k)
        (pw (rootNumerator (succ i) H p q) k) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDenominator H q (succ k) R) (pw (rootNumerator (succ i) H p q) k) (unit s)) := by
  have rule := h.allE i
  simp [panelRows,panelWidth,stepScale] at rule
  exact .impE rule hi

/-- The original weighted-block conversion is used without changing any
root-grid or panel code. -/
theorem panel_norm (F : PR 3) (i s H p q k R L x : PTm n) (hi : Γ ⊢[PRAAx] lt i H)
    (h : Γ ⊢[PRAAx] source F s H p q k R L x) : Γ ⊢[PRAAx]
    bounded (qmul (weightedPoint H p q k R) (block cutF (sampleBody F) i (cutData H p q (succ k)) (gridData s H p q k R x)))
      (GaussianEulerLowerBlockWeight.numerator (rootDenominator H q (succ k) R) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator H q (succ k) R) (unit s)) := by
  let A := succ k
  let D := rootDenominator H q A R
  let U := pw D k
  let V := pw (rootNumerator (succ i) H p q) k
  let S := stepScale p q k
  let P := unit s
  let J := panelWidth i H p q A
  let y := gridData s H p q k R x
  let f := sampleBody F
  let d := cutData H p q A
  have hH := h.andE₁
  have hpq := h.andE₂.andE₁
  have hW := h.andE₂.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hH
  have hU : Γ ⊢[PRAAx] le one U := GaussianPolynomialPerturbation.power_positive _ _ hD
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _ (root_right_guard i H p q A R hH hpq hi).andE₁
  have hJU : Γ ⊢[PRAAx] le J (S*U) := le_congr (.eqRefl _) (by dsimp only [S,U,D,A]; unfold stepScale; ipra_ring)
    (uniform_panel_width i H p q k R hH hpq hi)
  have hs : Γ ⊢[PRAAx] GaussianEulerLowerBlockWeight.source J D U V S P :=
    .andI hD (.andI hU (.andI hV (.andI (unit_positive s) (.andI (right_width i H p q k) hJU))))
  have eq : Γ ⊢[PRAAx] block cutF f i d y ≐ sum (offB f) J (pairT (offset i H p q A) y) :=
    sum_index_congr _ (congrMonus (offset_at (succ i) H p q A) (offset_at i H p q A))
      (congrPairT (offset_at i H p q A) (.eqRefl y))
  exact bound_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) eq).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerLowerBlockWeight.finite_block_bound (offB f) (weightedPoint H p q k R) _ J D U V S L P hs
      (GaussianEulerCompactLowerTail.literal_weight H p q k R hH hW) (panel_rows_at F i s H p q k R L x h.andE₂.andE₂.andE₂ hi))

def weightedPanelBody (F : PR 3) : PTm 2 := multiplyBody (blockBody cutF (sampleBody F))
def panelData (s H p q k R x : PTm n) : PTm n := pairT (weightedPoint H p q k R) (pairT (cutData H p q (succ k)) (gridData s H p q k R x))
@[simp] theorem subst_weightedPoint {m : ℕ} (σ : Fin n → PTm m) (H p q k R : PTm n) :
    Syn.subst σ (weightedPoint H p q k R) = weightedPoint (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ R) := by simp [weightedPoint]
@[simp] theorem subst_panelData {m : ℕ} (σ : Fin n → PTm m) (s H p q k R x : PTm n) :
    Syn.subst σ (panelData s H p q k R x) = panelData (Syn.subst σ s) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ R) (Syn.subst σ x) := by simp [panelData]

theorem weighted_panel_at (F : PR 3) (i s H p q k R x : PTm n) : Γ ⊢[PRAAx]
    inst2 (weightedPanelBody F) i (panelData s H p q k R x) ≐
      qmul (weightedPoint H p q k R) (block cutF (sampleBody F) i (cutData H p q (succ k)) (gridData s H p q k R x)) :=
  (multiply_body_at _ _ _ _).eqTrans (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (block_at _ _ _ _ _))

theorem weighted_panels (F : PR 3) (s H p q k R L x : PTm n) (h : Γ ⊢[PRAAx] source F s H p q k R L x) : Γ ⊢[PRAAx]
    summandsBounded (weightedPanelBody F) H (panelData s H p q k R x)
      (GaussianEulerLowerBlockWeight.numerator (rootDenominator H q (succ k) R) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator H q (succ k) R) (unit s)) := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source F (Syn.shift s) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift R) (Syn.shift L) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  have norm := panel_norm F (var 0) (Syn.shift s) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift R) (Syn.shift L) (Syn.shift x) Prf.hyp0 hs.wk
  let Δ := lt (var 0) (Syn.shift H) :: Γ.map Fm.shift
  have eq := weighted_panel_at (Γ := Δ) F (var 0) (Syn.shift s) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift R) (Syn.shift x)
  simpa [Δ,summandsBounded,stepScale,Syn.shift] using bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) norm

/-- Literal existing quadrature and unchanged partitioned finite sums. -/
theorem weighted_sum (F : PR 3) (s H p q k R x : PTm n) : Γ ⊢[PRAAx]
    originalQuadrature F s H p q k R x ≐ sum (weightedPanelBody F) H (panelData s H p q k R x) :=
  (grouped_original_quadrature F s H p q (succ k) R x).eqTrans (GaussianRationalFiniteSum.sum_multiply _ _ _ _).eqSymm

theorem finite_bound (F : PR 3) (s H p q k R L x : PTm n) (h : Γ ⊢[PRAAx] source F s H p q k R L x) : Γ ⊢[PRAAx]
    bounded (originalQuadrature F s H p q k R x)
      (H*GaussianEulerLowerBlockWeight.numerator (rootDenominator H q (succ k) R) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator H q (succ k) R) (unit s)) := by
  have hD := positive_product (Γ := Γ) _ _ (unit_positive (GaussianGammaIntegralCutoffs.height q (succ k) R)) h.andE₁
  have hY := positive_product (Γ := Γ) _ _ (positive_product _ _ hD hD) (unit_positive s)
  exact bound_congr (weighted_sum F s H p q k R x).eqSymm (.eqRefl _) (.eqRefl _)
    (uniform_sum_bound (weightedPanelBody F) H (panelData s H p q k R x) _ _ hY (weighted_panels F s H p q k R L x h))

theorem literal_panel_row (F : PR 3) (i j s H p q k R x : PTm n) : Γ ⊢[PRAAx]
    inst2 (offB (sampleBody F)) j (pairT (offset i H p q (succ k)) (gridData s H p q k R x)) ≐
      ap3 F s (GaussianEulerLowerTailLocalComparison.rowTime i j H p q (succ k) R) x :=
  (GaussianRationalFiniteProduct.offset_at _ _ _ _).eqTrans (sample_body_at F _ _ _ _ _ _ _)

theorem actual_original_lower_root_grid_finite_bound_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      bounded (originalQuadrature F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))
        (var 1*GaussianEulerLowerBlockWeight.numerator (rootDenominator (var 1) (var 3) (succ (var 4)) (var 5))
          (stepScale (var 2) (var 3) (var 4)) (var 6) (unit (var 0)))
        (GaussianEulerLowerBlockWeight.denominator (rootDenominator (var 1) (var 3) (succ (var 4)) (var 5)) (unit (var 0)))) :=
  closeUniv 8 (.impI (finite_bound F _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLowerRootQuadratureBound
