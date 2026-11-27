import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Tails.GaussianEulerLowerTailRowBound
import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianUniformFiniteSumBound

/-!
# Finite lower-tail bound for the original Euler quadrature

Each exact block of original observations uses the right endpoint
of the transformed panel. Applying its uniform weighted bound
and summing through the actual block and original quadrature laws
gives the lower-tail estimate with finite mesh and observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactLowerTail

open_ipra
open GaussianEulerLowerTailRootGrid (rootDenominator rootNumerator timeNumerator timeDenominator)
open GaussianEulerLowerTailPartition (cutF cutData offset offset_at panelWidth totalWidth root_right_guard
  uniform_panel_width grouped_original_quadrature)
open GaussianEulerLowerTailRowBound (stepScale right_width time_den_product actual_row_norm_bound)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (sampleBody sampleData sampledModulus quadrature sample_body_at)
open GaussianRationalRiemannRefinement (weight weight_bound)
open GaussianUniformFiniteSumBound (summandsBounded uniform_sum_bound)
open GaussianRationalFiniteSum (sum sum_index_congr multiplyBody multiply_body_at sum_multiply)
open GaussianPartitionedFiniteSum (block blockBody block_at)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B N p q k L : PTm n) : Fm PTm n :=
  le one N ⋏ (le p q ⋏ (le one (totalWidth N p q (succ k)) ⋏
    (GaussianEulerLowerPowerCoefficients.source z R B (succ k) ⋏
      sampledModulus evaluatorF (timeNumerator zero N p q (succ k)) (totalWidth N p q (succ k))
        (timeDenominator N q (succ k) R) L (fixedData z B))))

def gridData (s z R B N p q k : PTm n) : PTm n :=
  sampleData s (totalWidth N p q (succ k)) (timeNumerator zero N p q (succ k))
    (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) (fixedData z B)
def weightedPoint (N p q k R : PTm n) : PTm n :=
  weight (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) (totalWidth N p q (succ k))
def originalQuadrature (s z R B N p q k : PTm n) : PTm n :=
  quadrature evaluatorF s (totalWidth N p q (succ k)) (timeNumerator zero N p q (succ k))
    (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) (fixedData z B)
def weightedPanelBody : PTm 2 := multiplyBody (blockBody cutF (sampleBody evaluatorF))
def panelData (s z R B N p q k : PTm n) : PTm n :=
  pairT (weightedPoint N p q k R) (pairT (cutData N p q (succ k)) (gridData s z R B N p q k))

theorem subst_timeNumerator {m : ℕ} (σ : Fin n → PTm m) (i N p q A : PTm n) :
    Syn.subst σ (timeNumerator i N p q A) =
      timeNumerator (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) :=
  by simp [timeNumerator,rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio]
theorem subst_timeDenominator {m : ℕ} (σ : Fin n → PTm m) (N q A R : PTm n) :
    Syn.subst σ (timeDenominator N q A R) = timeDenominator (Syn.subst σ N) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [timeDenominator,rootDenominator,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient,Products.fact]
theorem subst_rootDenominator {m : ℕ} (σ : Fin n → PTm m) (N q A R : PTm n) :
    Syn.subst σ (rootDenominator N q A R) = rootDenominator (Syn.subst σ N) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [rootDenominator,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient,Products.fact]
theorem subst_rootNumerator {m : ℕ} (σ : Fin n → PTm m) (i N p q : PTm n) :
    Syn.subst σ (rootNumerator i N p q) = rootNumerator (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ q) :=
  by simp [rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio]

attribute [local simp] subst_timeNumerator subst_timeDenominator subst_rootDenominator subst_rootNumerator

ipra_subst source [totalWidth]
ipra_subst gridData [totalWidth]
ipra_subst weightedPoint [totalWidth]
ipra_subst panelData

theorem literal_weight (N p q k R : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hW : Γ ⊢[PRAAx] le one (totalWidth N p q (succ k))) : Γ ⊢[PRAAx]
    bounded (weightedPoint N p q k R) one
      (rootDenominator N q (succ k) R*pw (rootDenominator N q (succ k) R) k) := by
  let W := totalWidth N p q (succ k)
  let E := timeDenominator N q (succ k) R
  have hD := positive_product (Γ := Γ) _ _ (unit_positive (GaussianGammaIntegralCutoffs.height q (succ k) R)) hN
  have hE : Γ ⊢[PRAAx] le one E := GaussianPolynomialPerturbation.power_positive _ _ hD
  have e : Γ ⊢[PRAAx] weight W E W ≐ weight W E (W*one) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring)
  have ew := e.eqTrans (GaussianCompactRiemannSplit.weight_shared W E one hW hE (le_refl one))
  exact bound_congr ew.eqSymm (.eqRefl _)
    ((by ipra_ring : Γ ⊢[PRAAx] E*one ≐ E).eqTrans (time_den_product N q k R))
    (weight_bound one E one hE (le_refl one))

theorem literal_panel_row (i j s z R B N p q k : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB (sampleBody evaluatorF)) j
      (pairT (offset i N p q (succ k)) (gridData s z R B N p q k)) ≐
      ap3 evaluatorF s (GaussianEulerLowerTailLocalComparison.rowTime i j N p q (succ k) R) (fixedData z B) :=
  (GaussianRationalFiniteProduct.offset_at _ _ _ _).eqTrans
    (sample_body_at evaluatorF _ _ _ _ _ _ _)

theorem original_panel_rows (i s z R B N p q k L : PTm n)
    (hi : Γ ⊢[PRAAx] lt i N) (h : Γ ⊢[PRAAx] source z R B N p q k L) :
    Γ ⊢[PRAAx] summandsBounded (offB (sampleBody evaluatorF)) (panelWidth i N p q (succ k))
      (pairT (offset i N p q (succ k)) (gridData s z R B N p q k))
      (GaussianEulerLowerBlockWeight.rowNumerator (rootDenominator N q (succ k) R) (pw (rootDenominator N q (succ k) R) k)
        (pw (rootNumerator (succ i) N p q) k) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDenominator N q (succ k) R) (pw (rootNumerator (succ i) N p q) k) (unit s)) := by
  refine .allI (.impI ?_)
  have hi' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hi.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift N) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift L) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have hN := h'.andE₁
  have hpq := h'.andE₂.andE₁
  have hW := h'.andE₂.andE₂.andE₁
  have hc := h'.andE₂.andE₂.andE₂.andE₁
  have hm := h'.andE₂.andE₂.andE₂.andE₂
  have sub := actual_row_norm_bound (Syn.shift i) (var 0) (Syn.shift s) (Syn.shift N) (Syn.shift p) (Syn.shift q) (Syn.shift k)
    (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift L) hN.wk hpq.wk hi'.wk
    (by simpa [panelWidth,Syn.shift] using (Prf.hyp0 : _ ⊢[PRAAx] lt (var 0) (Syn.shift (panelWidth i N p q (succ k)))))
    hW.wk hc.wk hm.wk
  simpa [summandsBounded,panelWidth,stepScale,Syn.shift] using bound_congr
    (literal_panel_row (Syn.shift i) (var 0) (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N)
      (Syn.shift p) (Syn.shift q) (Syn.shift k)).eqSymm (.eqRefl _) (.eqRefl _) sub

theorem panel_norm (i s z R B N p q k L : PTm n)
    (hi : Γ ⊢[PRAAx] lt i N) (h : Γ ⊢[PRAAx] source z R B N p q k L) :
    Γ ⊢[PRAAx] bounded
      (qmul (weightedPoint N p q k R) (block cutF (sampleBody evaluatorF) i (cutData N p q (succ k)) (gridData s z R B N p q k)))
      (GaussianEulerLowerBlockWeight.numerator (rootDenominator N q (succ k) R) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator N q (succ k) R) (unit s)) := by
  let A := succ k
  let D := rootDenominator N q A R
  let U := pw D k
  let V := pw (rootNumerator (succ i) N p q) k
  let S := stepScale p q k
  let P := unit s
  let J := panelWidth i N p q A
  let y := gridData s z R B N p q k
  let f := sampleBody evaluatorF
  let x := pairT (offset i N p q A) y
  let d := cutData N p q A
  let w := weightedPoint N p q k R
  have hN := h.andE₁
  have hpq := h.andE₂.andE₁
  have hW := h.andE₂.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hN
  have hU : Γ ⊢[PRAAx] le one U := GaussianPolynomialPerturbation.power_positive _ _ hD
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _
    (root_right_guard i N p q A R hN hpq hi).andE₁
  have hJU : Γ ⊢[PRAAx] le J (S*U) :=
    le_congr (.eqRefl _) (by dsimp only [S,U,D,A]; unfold stepScale; ipra_ring)
      (uniform_panel_width i N p q k R hN hpq hi)
  have hs : Γ ⊢[PRAAx] GaussianEulerLowerBlockWeight.source J D U V S P :=
    .andI hD (.andI hU (.andI hV (.andI (unit_positive s) (.andI (right_width i N p q k) hJU))))
  have eq : Γ ⊢[PRAAx] block cutF f i d y ≐ sum (offB f) J x :=
    sum_index_congr _ (congrMonus (offset_at (succ i) N p q A) (offset_at i N p q A))
      (congrPairT (offset_at i N p q A) (.eqRefl y))
  exact bound_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl w) eq).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerLowerBlockWeight.finite_block_bound (offB f) w x J D U V S L P hs
      (literal_weight N p q k R hN hW) (original_panel_rows i s z R B N p q k L hi h))

theorem weighted_panel_at (i s z R B N p q k : PTm n) :
    Γ ⊢[PRAAx] inst2 weightedPanelBody i (panelData s z R B N p q k) ≐
      qmul (weightedPoint N p q k R)
        (block cutF (sampleBody evaluatorF) i (cutData N p q (succ k)) (gridData s z R B N p q k)) :=
  (multiply_body_at _ _ _ _).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (block_at _ _ _ _ _))

theorem original_weighted_panels (s z R B N p q k L : PTm n) (h : Γ ⊢[PRAAx] source z R B N p q k L) :
    Γ ⊢[PRAAx] summandsBounded weightedPanelBody N (panelData s z R B N p q k)
      (GaussianEulerLowerBlockWeight.numerator (rootDenominator N q (succ k) R) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator N q (succ k) R) (unit s)) := by
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift N) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift L) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have raw := panel_norm (var 0) (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B)
    (Syn.shift N) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift L) Prf.hyp0 h'.wk
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have term := weighted_panel_at (Γ := Δ) (var 0) (Syn.shift s) (Syn.shift z) (Syn.shift R)
    (Syn.shift B) (Syn.shift N) (Syn.shift p) (Syn.shift q) (Syn.shift k)
  simpa [Δ,summandsBounded,stepScale,Syn.shift] using
    bound_congr term.eqSymm (.eqRefl _) (.eqRefl _) raw

theorem original_weighted_sum (s z R B N p q k : PTm n) :
    Γ ⊢[PRAAx] originalQuadrature s z R B N p q k ≐ sum weightedPanelBody N (panelData s z R B N p q k) :=
  (grouped_original_quadrature evaluatorF s N p q (succ k) R (fixedData z B)).eqTrans
    (GaussianRationalFiniteSum.sum_multiply _ _ _ _).eqSymm

theorem original_finite_lower_tail_bound (s z R B N p q k L : PTm n) (h : Γ ⊢[PRAAx] source z R B N p q k L) :
    Γ ⊢[PRAAx] bounded (originalQuadrature s z R B N p q k)
      (N*GaussianEulerLowerBlockWeight.numerator (rootDenominator N q (succ k) R) (stepScale p q k) L (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator N q (succ k) R) (unit s)) := by
  let D := rootDenominator N q (succ k) R
  let P := unit s
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) h.andE₁
  have hY : Γ ⊢[PRAAx] le one (GaussianEulerLowerBlockWeight.denominator D P) :=
    positive_product _ _ (positive_product _ _ hD hD) (unit_positive s)
  exact bound_congr (original_weighted_sum s z R B N p q k).eqSymm (.eqRefl _) (.eqRefl _)
    (uniform_sum_bound weightedPanelBody N (panelData s z R B N p q k) _ _ hY
      (original_weighted_panels s z R B N p q k L h))

theorem actual_finite_lower_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (originalQuadrature (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (var 4*GaussianEulerLowerBlockWeight.numerator (rootDenominator (var 4) (var 6) (succ (var 7)) (var 2))
          (stepScale (var 5) (var 6) (var 7)) (var 8) (unit (var 0)))
        (GaussianEulerLowerBlockWeight.denominator (rootDenominator (var 4) (var 6) (succ (var 7)) (var 2)) (unit (var 0)))) :=
  closeUniv 9 (.impI (original_finite_lower_tail_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactLowerTail
