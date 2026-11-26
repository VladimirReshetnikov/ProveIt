import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactLowerTail
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTailFiniteBudget

/-!
# Finite lower-tail transport for a compact evaluator

The original root partition and affine grid work for any evaluator with
its sampled modulus and the original lower-tail bound at each right
endpoint. These hypotheses give the same finite lower-tail budget as
for the ordinary Euler evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerLowerFinite

open_ipra
open GaussianEulerLowerTailRootGrid (rootDenominator rootNumerator timeNumerator timeDenominator)
open GaussianEulerLowerTailPartition (cutF cutData offset offset_at panelWidth totalWidth root_right_guard
  uniform_panel_width grouped_original_quadrature)
open GaussianEulerLowerTailLocalComparison (rightTime rowTime original_row_distance)
open GaussianEulerLowerTailRowBound (stepScale right_width scale_local_budget)
open GaussianEulerCompactLowerTail (weightedPoint literal_weight)
open GaussianCompactRiemannName (sampleBody sampleData sampledModulus quadrature sample_body_at)
open GaussianUniformFiniteSumBound (summandsBounded uniform_sum_bound)
open GaussianRationalFiniteSum (sum sum_index_congr multiplyBody multiply_body_at sum_multiply)
open GaussianPartitionedFiniteSum (block blockBody block_at)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rightBody (F : PR 3) (i s N p q k R x : PTm n) : Fm PTm n :=
  let U := pw (rootDenominator N q (succ k) R) k
  let V := pw (rootNumerator (succ i) N p q) k
  bounded (ap3 F s (rightTime i N p q (succ k) R) x) (U*unit s+V) (V*unit s)
def rightEndpoints (F : PR 3) (s N p q k R x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    rightBody F (var 0) (Syn.shift s) (Syn.shift N) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift R) (Syn.shift x))
def source (F : PR 3) (s N p q k R L x : PTm n) : Fm PTm n :=
  le one N ⋏ (le p q ⋏ (le one (totalWidth N p q (succ k)) ⋏
    (sampledModulus F (timeNumerator zero N p q (succ k)) (totalWidth N p q (succ k))
      (timeDenominator N q (succ k) R) L x ⋏ rightEndpoints F s N p q k R x)))

def gridData (s N p q k R x : PTm n) : PTm n :=
  sampleData s (totalWidth N p q (succ k)) (timeNumerator zero N p q (succ k))
    (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) x
def originalQuadrature (F : PR 3) (s N p q k R x : PTm n) : PTm n :=
  quadrature F s (totalWidth N p q (succ k)) (timeNumerator zero N p q (succ k))
    (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) x
private def weightedPanelBody (F : PR 3) : PTm 2 := multiplyBody (blockBody cutF (sampleBody F))
private def panelData (s N p q k R x : PTm n) : PTm n :=
  pairT (weightedPoint N p q k R) (pairT (cutData N p q (succ k)) (gridData s N p q k R x))

@[simp] private theorem subst_timeNumerator {m : ℕ} (σ : Fin n → PTm m) (i N p q A : PTm n) :
    Syn.subst σ (timeNumerator i N p q A) =
      timeNumerator (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) :=
  by simp [timeNumerator,rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio]
@[simp] private theorem subst_rootDenominator {m : ℕ} (σ : Fin n → PTm m) (N q A R : PTm n) :
    Syn.subst σ (rootDenominator N q A R) = rootDenominator (Syn.subst σ N) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [rootDenominator,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient,Products.fact]
@[simp] private theorem subst_rootNumerator {m : ℕ} (σ : Fin n → PTm m) (i N p q : PTm n) :
    Syn.subst σ (rootNumerator i N p q) = rootNumerator (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) :=
  by simp [rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio]

ipra_subst rightBody [rightTime, timeDenominator]
ipra_subst rightEndpoints [Syn.subst_shift, Syn.shift_subst]
ipra_subst source [totalWidth, timeDenominator, one]
@[simp] private theorem subst_gridData {m : ℕ} (σ : Fin n → PTm m) (s N p q k R x : PTm n) :
    Syn.subst σ (gridData s N p q k R x) = gridData (Syn.subst σ s) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ R) (Syn.subst σ x) :=
  by simp [gridData,totalWidth,timeDenominator]
@[simp] private theorem subst_panelData {m : ℕ} (σ : Fin n → PTm m) (s N p q k R x : PTm n) :
    Syn.subst σ (panelData s N p q k R x) = panelData (Syn.subst σ s) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ R) (Syn.subst σ x) := by simp [panelData]

theorem right_endpoint_at (F : PR 3) (i s N p q k R x : PTm n) (hi : Γ ⊢[PRAAx] lt i N)
    (h : Γ ⊢[PRAAx] rightEndpoints F s N p q k R x) : Γ ⊢[PRAAx] rightBody F i s N p q k R x := by
  have oneRight : Γ ⊢[PRAAx] lt i N ⟶ rightBody F i s N p q k R x := by
    simpa only [rightEndpoints,Fm.subst_imp,subst_lt,subst_rightBody,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      using h.allE i
  exact oneRight.impE hi

private theorem row_norm (F : PR 3) (i j s N p q k R L x : PTm n) (hi : Γ ⊢[PRAAx] lt i N)
    (hj : Γ ⊢[PRAAx] lt j (panelWidth i N p q (succ k))) (hs : Γ ⊢[PRAAx] source F s N p q k R L x) :
    Γ ⊢[PRAAx] bounded (ap3 F s (rowTime i j N p q (succ k) R) x)
      (GaussianEulerLowerBlockWeight.rowNumerator (rootDenominator N q (succ k) R) (pw (rootDenominator N q (succ k) R) k)
        (pw (rootNumerator (succ i) N p q) k) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDenominator N q (succ k) R) (pw (rootNumerator (succ i) N p q) k) (unit s)) := by
  let D := rootDenominator N q (succ k) R
  let V := pw (rootNumerator (succ i) N p q) k
  let P := unit s
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hs.andE₁
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _
    (root_right_guard i N p q (succ k) R hs.andE₁ hs.andE₂.andE₁ hi).andE₁
  have hP := unit_positive (Γ := Γ) s
  have hDP := positive_product _ _ hD hP
  have hVP := positive_product _ _ hV hP
  have dist := original_row_distance F i j N p q k R L x s s hs.andE₁ hs.andE₂.andE₁ hi hj
    hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁
  have near := scale_local_budget _ _ s N p q k R L hs.andE₁ dist
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hDP hVP near
    (right_endpoint_at F i s N p q k R x hi hs.andE₂.andE₂.andE₂.andE₂)
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ hDP hVP)
    (GaussianEulerLowerBlockWeight.row_denominator_positive D V P hD hV hP) ?_ raw
  exact le_of_eq_add (d := zero) (by unfold GaussianEulerLowerBlockWeight.rowNumerator GaussianEulerLowerBlockWeight.rowDenominator; ipra_ring)

private theorem panel_norm (F : PR 3) (i s N p q k R L x : PTm n)
    (hi : Γ ⊢[PRAAx] lt i N) (hs : Γ ⊢[PRAAx] source F s N p q k R L x) :
    Γ ⊢[PRAAx] bounded (qmul (weightedPoint N p q k R)
      (block cutF (sampleBody F) i (cutData N p q (succ k)) (gridData s N p q k R x)))
      (GaussianEulerLowerBlockWeight.numerator (rootDenominator N q (succ k) R) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator N q (succ k) R) (unit s)) := by
  let A := succ k
  let D := rootDenominator N q A R
  let U := pw D k
  let V := pw (rootNumerator (succ i) N p q) k
  let S := stepScale p q k
  let P := unit s
  let J := panelWidth i N p q A
  let y := gridData s N p q k R x
  let f := sampleBody F
  let data := pairT (offset i N p q A) y
  let w := weightedPoint N p q k R
  have hN := hs.andE₁
  have hpq := hs.andE₂.andE₁
  have hW := hs.andE₂.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hN
  have hU : Γ ⊢[PRAAx] le one U := GaussianPolynomialPerturbation.power_positive _ _ hD
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _
    (root_right_guard i N p q A R hN hpq hi).andE₁
  have hJU : Γ ⊢[PRAAx] le J (S*U) :=
    le_congr (.eqRefl _) (by dsimp only [S,U,D,A]; unfold stepScale; ipra_ring)
      (uniform_panel_width i N p q k R hN hpq hi)
  have blockSource : Γ ⊢[PRAAx] GaussianEulerLowerBlockWeight.source J D U V S P :=
    .andI hD (.andI hU (.andI hV (.andI (unit_positive s) (.andI (right_width i N p q k) hJU))))
  have eq : Γ ⊢[PRAAx] block cutF f i (cutData N p q A) y ≐ sum (offB f) J data :=
    sum_index_congr _ (congrMonus (offset_at (succ i) N p q A) (offset_at i N p q A))
      (congrPairT (offset_at i N p q A) (.eqRefl y))
  have rowBounds : Γ ⊢[PRAAx] summandsBounded (offB f) J data
      (GaussianEulerLowerBlockWeight.rowNumerator D U V S L P) (GaussianEulerLowerBlockWeight.rowDenominator D V P) := by
    let sh (u : PTm n) := Syn.shift u
    have hi' : Γ.map Fm.shift ⊢[PRAAx] lt (sh i) (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hi.shift
    have hs' : Γ.map Fm.shift ⊢[PRAAx] source F (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh L) (sh x) :=
      by simpa [Fm.shift,Syn.shift,sh] using hs.shift
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (sh J) :: Γ.map Fm.shift
    have hj : Δ ⊢[PRAAx] lt (var 0) (panelWidth (sh i) (sh N) (sh p) (sh q) (succ (sh k))) :=
      by simpa [Δ,J,A,panelWidth,sh,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (sh J))
    have t : Δ ⊢[PRAAx] inst2 (offB f) (var 0)
        (pairT (offset (sh i) (sh N) (sh p) (sh q) (succ (sh k))) (gridData (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh x))) ≐
      ap3 F (sh s) (rowTime (sh i) (var 0) (sh N) (sh p) (sh q) (succ (sh k)) (sh R)) (sh x) :=
      (GaussianRationalFiniteProduct.offset_at _ _ _ _).eqTrans (sample_body_at F _ _ _ _ _ _ _)
    simpa [Δ,J,summandsBounded,panelWidth,stepScale,sh,Syn.shift,data,D,U,V,S,P,A,y] using
      bound_congr t.eqSymm (.eqRefl _) (.eqRefl _)
        (row_norm F (sh i) (var 0) (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh L) (sh x) hi'.wk hj hs'.wk)
  exact bound_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl w) eq).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerLowerBlockWeight.finite_block_bound (offB f) w data J D U V S L P blockSource
      (literal_weight N p q k R hN hW) rowBounds)

theorem original_finite_lower_tail_bound (F : PR 3) (s N p q k R L x : PTm n)
    (hs : Γ ⊢[PRAAx] source F s N p q k R L x) : Γ ⊢[PRAAx]
    bounded (originalQuadrature F s N p q k R x)
      (GaussianEulerLowerTailFiniteBudget.oldNumerator N (rootDenominator N q (succ k) R) (GaussianEulerLowerTailFiniteBudget.scale p q k) L (unit s))
      (GaussianEulerLowerTailFiniteBudget.oldDenominator (rootDenominator N q (succ k) R) (unit s)) := by
  let D := rootDenominator N q (succ k) R
  let P := unit s
  let S := stepScale p q k
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hs.andE₁
  have den : Γ ⊢[PRAAx] le one (GaussianEulerLowerBlockWeight.denominator D P) :=
    positive_product _ _ (positive_product _ _ hD hD) (unit_positive s)
  have allPanels : Γ ⊢[PRAAx] summandsBounded (weightedPanelBody F) N (panelData s N p q k R x)
      (GaussianEulerLowerBlockWeight.numerator D S L P) (GaussianEulerLowerBlockWeight.denominator D P) := by
    let sh (u : PTm n) := Syn.shift u
    have hs' : Γ.map Fm.shift ⊢[PRAAx] source F (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh L) (sh x) :=
      by simpa [Fm.shift,Syn.shift,sh] using hs.shift
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    have t : Δ ⊢[PRAAx] inst2 (weightedPanelBody F) (var 0) (panelData (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh x)) ≐
        qmul (weightedPoint (sh N) (sh p) (sh q) (sh k) (sh R))
          (block cutF (sampleBody F) (var 0) (cutData (sh N) (sh p) (sh q) (succ (sh k))) (gridData (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh x))) :=
      (multiply_body_at _ _ _ _).eqTrans (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (block_at _ _ _ _ _))
    simpa [Δ,summandsBounded,stepScale,D,S,P,Syn.shift,sh] using bound_congr t.eqSymm (.eqRefl _) (.eqRefl _)
      (panel_norm F (var 0) (sh s) (sh N) (sh p) (sh q) (sh k) (sh R) (sh L) (sh x) Prf.hyp0 hs'.wk)
  have eq : Γ ⊢[PRAAx] originalQuadrature F s N p q k R x ≐ sum (weightedPanelBody F) N (panelData s N p q k R x) :=
    (grouped_original_quadrature F s N p q (succ k) R x).eqTrans (sum_multiply _ _ _ _).eqSymm
  exact bound_congr eq.eqSymm (by
    simp only [GaussianEulerLowerTailFiniteBudget.oldNumerator,GaussianEulerLowerTailFiniteBudget.scale,
      GaussianEulerLowerBlockWeight.numerator,stepScale,D,P,S]
    ipra_ring) (.eqRefl _)
    (uniform_sum_bound (weightedPanelBody F) N (panelData s N p q k R x) _ _ den allPanels)

theorem original_native_lower_tail_bound (F : PR 3) (s t N p q k R L x : PTm n)
    (hs : Γ ⊢[PRAAx] source F s N p q k R L x) (hN : Γ ⊢[PRAAx] le (unit t) N)
    (hP : Γ ⊢[PRAAx] le (unit t) (unit s)) : Γ ⊢[PRAAx]
    bounded (originalQuadrature F s N p q k R x) (GaussianEulerLowerTailFiniteBudget.numerator t p q k R L)
      (GaussianEulerLowerTailFiniteBudget.denominator t p k R) :=
  GaussianEulerLowerTailFiniteBudget.original_radius_conversion _ s t N p q k R L hs.andE₂.andE₁ hN hP
    (original_finite_lower_tail_bound F s N p q k R L x hs)

theorem actual_compact_evaluator_finite_lower_tail_closed (F : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source F (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        le (unit (var 1)) (var 2) ⟶ le (unit (var 1)) (unit (var 0)) ⟶
        bounded (originalQuadrature F (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8))
          (GaussianEulerLowerTailFiniteBudget.numerator (var 1) (var 3) (var 4) (var 5) (var 6) (var 7))
          (GaussianEulerLowerTailFiniteBudget.denominator (var 1) (var 3) (var 5) (var 6))) :=
  closeUniv 9 (.impI (.impI (.impI (original_native_lower_tail_bound F _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerLowerFinite
