import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianLowerRootQuadratureBound
import IPRADerivations.Analysis.Beta.Endpoints.Lower.GaussianBetaKernelLowerTransformedPower
import IPRADerivations.Analysis.Beta.CompactKernels.Regularity.GaussianBetaKernelCompactModulus
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Tails.GaussianEulerLowerTailFiniteBudget

/-!
# Original finite beta quadrature on the unchanged lower-root partition

The fixed lower interval uses the original eta(q) denominator for its
time modulus. Positive rescaling carries that SAME modulus to the old
root-grid encoding, so the constant is independent of the mesh and beta
degree. Actual transformed right endpoints and original local comparison
supply all panel-row bounds. The generic original partition aggregator
and the old finite radius conversion then give the exact lower-tail
bound, with no modulus or row-output premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelLowerRootQuadrature

open_ipra
open GaussianEulerLowerTailRootGrid (rootDenominator rootNumerator timeNumerator timeDenominator)
open GaussianEulerLowerTailPartition (root_right_guard panelWidth totalWidth)
open GaussianEulerLowerTailRowBound (stepScale)
open GaussianEulerLowerTailLocalComparison (rowTime rightTime)
open GaussianBetaKernelGridComparison (evaluatorF sampleDataBeta)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianGammaCompactCutoffGeometry (lowerWidth ratio lower_endpoint)
open GaussianCompactRiemannName (sampledModulus sampled_modulus_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem subst_rootDenominator {m : ℕ} (σ : Fin n → PTm m) (H q A R : PTm n) :
    Syn.subst σ (rootDenominator H q A R) = rootDenominator (Syn.subst σ H) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [rootDenominator,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
private theorem subst_rootNumerator {m : ℕ} (σ : Fin n → PTm m) (i H p q : PTm n) :
    Syn.subst σ (rootNumerator i H p q) = rootNumerator (Syn.subst σ i) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) :=
  by simp [rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio]
attribute [local simp] subst_rootDenominator subst_rootNumerator

def lipschitz (q k R : PTm n) : PTm n := GaussianBetaKernelCompactModulus.lipschitz R (etaDen q (succ k) R) one
def source (z R B H p q k N : PTm n) : Fm PTm n := GaussianEulerLowerPowerCoefficients.source z R B (succ k) ⋏
  (le one H ⋏ (lt p q ⋏ le one N))
def originalQuadrature (s z R B H p q k N : PTm n) : PTm n :=
  GaussianLowerRootQuadratureBound.originalQuadrature evaluatorF s H p q k R (sampleDataBeta z B N)

ipra_subst lipschitz [etaDen, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst source

/-- The original lower interval lies below one, so the original degree
N>=1 supplies the beta support for every actual local time query. -/
theorem base_modulus (z R B p q k N : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ k))
    (hpq : Γ ⊢[PRAAx] le p q) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF one (lowerWidth p q (succ k)) (etaDen q (succ k) R) (lipschitz q k R) (sampleDataBeta z B N) := by
  let A := succ k
  let E := etaDen q A R
  have ratioBound : Γ ⊢[PRAAx] le (ratio p q A) E :=
    le_congr (one_mul _) ((mul_comm _ _).eqTrans (GaussianGammaCompactCutoffGeometry.eta_den_refinement p q A R hpq).eqSymm)
      (mul_le_mul_right (ratio p q A) (eta_den_positive p A R))
  have endBound : Γ ⊢[PRAAx] le (one+lowerWidth p q A) (E*one) :=
    le_congr (lower_endpoint p q A).eqSymm (by ipra_ring) ratioBound
  have oldSource : Γ ⊢[PRAAx] GaussianBetaKernelCompactModulus.compactSource z R B E one one (lowerWidth p q A) N :=
    .andI (.andI h.andE₂.andE₁.andE₁ (.andI (eta_den_positive q A R) h.andE₂.andE₁.andE₂))
      (.andI (.andI hN hN) (.andI (le_refl one) endBound))
  exact GaussianBetaKernelCompactModulus.sampled_modulus z R B E one one (lowerWidth p q A) N oldSource

/-- Exact positive rescaling keeps the original fixed-interval modulus;
it does not replace it by a mesh-dependent compact constant. -/
theorem root_modulus (z R B H p q k N : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ k))
    (hH : Γ ⊢[PRAAx] le one H) (hpq : Γ ⊢[PRAAx] le p q) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF (timeNumerator zero H p q (succ k)) (totalWidth H p q (succ k))
      (timeDenominator H q (succ k) R) (lipschitz q k R) (sampleDataBeta z B N) := by
  let A := succ k
  let E := etaDen q A R
  let C := lowerWidth p q A
  let K := pw H A
  have hK := GaussianPolynomialPerturbation.power_positive H A hH
  have mod := GaussianCompactIntervalRescaling.rescaled_modulus evaluatorF K one C E (lipschitz q k R) (sampleDataBeta z B N) hK (base_modulus z R B p q k N h hpq hN)
  have ha : Γ ⊢[PRAAx] K*one ≐ timeNumerator zero H p q A :=
    (by ipra_ring : Γ ⊢[PRAAx] K*one ≐ K).eqTrans (GaussianEulerLowerTailRootGrid.time_first H p q A).eqSymm
  have hc : Γ ⊢[PRAAx] K*C ≐ totalWidth H p q A :=
    (mul_comm _ _).eqTrans (GaussianEulerLowerTailRootGrid.time_width H p q A).eqSymm
  have he : Γ ⊢[PRAAx] K*E ≐ timeDenominator H q A R :=
    (mul_comm _ _).eqTrans (GaussianEulerLowerTailRootGrid.time_denominator H q A R).eqSymm
  exact sampled_modulus_congr ha hc he (.eqRefl _) (.eqRefl _) mod

theorem right_sample_norm (i s H p q k z R B N : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i H)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ k)) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF s (rightTime i H p q (succ k) R) (sampleDataBeta z B N))
      (pw (rootDenominator H q (succ k) R) k*unit s+pw (rootNumerator (succ i) H p q) k)
      (pw (rootNumerator (succ i) H p q) k*unit s) := by
  let A := succ k
  let a := rootNumerator (succ i) H p q
  let b := rootDenominator H q A R
  have pos := root_right_guard i H p q A R hH hpq hi
  have hd := positive_product (Γ := Γ) _ _ (unit_positive (GaussianGammaIntegralCutoffs.height q A R)) hH
  have hs : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R B A a b := .andI h (.andI (.andI pos.andE₁ hd) pos.andE₂)
  have obs := GaussianBetaKernelGridComparison.row_at (Γ := Γ) s z B (pw a A) (pw b A) N
  have e := pred_succ (Γ := Γ) k
  have numEq := congrAdd (congrMul (congrAp2 powF e (.eqRefl b)) (.eqRefl (unit s))) (congrAp2 powF e (.eqRefl a))
  have denEq := congrMul (congrAp2 powF e (.eqRefl a)) (.eqRefl (unit s))
  exact bound_congr obs.eqSymm numEq denEq (GaussianBetaKernelLowerTransformedPower.original_transformed_beta_row s z R B A a b N hs hN)

theorem actual_row_norm_bound (i j s H p q k z R B N : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i H)
    (hj : Γ ⊢[PRAAx] lt j (panelWidth i H p q (succ k))) (hW : Γ ⊢[PRAAx] le one (totalWidth H p q (succ k)))
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ k)) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF s (rowTime i j H p q (succ k) R) (sampleDataBeta z B N))
      (GaussianEulerLowerBlockWeight.rowNumerator (rootDenominator H q (succ k) R) (pw (rootDenominator H q (succ k) R) k)
        (pw (rootNumerator (succ i) H p q) k) (stepScale p q k) (lipschitz q k R) (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDenominator H q (succ k) R) (pw (rootNumerator (succ i) H p q) k) (unit s)) := by
  let D := rootDenominator H q (succ k) R
  let U := pw D k
  let V := pw (rootNumerator (succ i) H p q) k
  let S := stepScale p q k
  let P := unit s
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) hH
  have hV : Γ ⊢[PRAAx] le one V := GaussianPolynomialPerturbation.power_positive _ _ (root_right_guard i H p q (succ k) R hH hpq hi).andE₁
  have hP := unit_positive (Γ := Γ) s
  have hDP := positive_product _ _ hD hP
  have hVP := positive_product _ _ hV hP
  have est := GaussianEulerLowerTailLocalComparison.original_row_distance evaluatorF i j H p q k R (lipschitz q k R)
    (sampleDataBeta z B N) s s hH hpq hi hj hW (root_modulus z R B H p q k N h hH hpq hN)
  have near := GaussianEulerLowerTailRowBound.scale_local_budget _ _ s H p q k R (lipschitz q k R) hH est
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hDP hVP near (right_sample_norm i s H p q k z R B N hH hpq hi h hN)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hDP hVP)
    (GaussianEulerLowerBlockWeight.row_denominator_positive D V P hD hV hP) _ raw
  exact le_of_eq_add (d := zero) (by unfold GaussianEulerLowerBlockWeight.rowNumerator GaussianEulerLowerBlockWeight.rowDenominator; dsimp only [D,U,V,S,P]; ipra_ring)

theorem width_positive (H p q k : PTm n) (hH : Γ ⊢[PRAAx] le one H) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    le one (totalWidth H p q (succ k)) :=
  le_congr (.eqRefl _) (GaussianEulerLowerTailRootGrid.time_width H p q (succ k)).eqSymm
    (positive_product _ _ (GaussianGammaCompactCutoffGeometry.lower_positive p q (succ k) (zero_lt_succ k) hpq)
      (GaussianPolynomialPerturbation.power_positive H (succ k) hH))

/-- The literal generated panel rows satisfy the old block-weight bounds
from the original source, with no supplied local row estimate. -/
theorem original_panel_rows (i s z R B H p q k N : PTm n) (hi : Γ ⊢[PRAAx] lt i H)
    (h : Γ ⊢[PRAAx] source z R B H p q k N) : Γ ⊢[PRAAx]
    GaussianUniformFiniteSumBound.summandsBounded (offB (GaussianCompactRiemannName.sampleBody evaluatorF)) (panelWidth i H p q (succ k))
      (pairT (GaussianEulerLowerTailPartition.offset i H p q (succ k)) (GaussianLowerRootQuadratureBound.gridData s H p q k R (sampleDataBeta z B N)))
      (GaussianEulerLowerBlockWeight.rowNumerator (rootDenominator H q (succ k) R) (pw (rootDenominator H q (succ k) R) k)
        (pw (rootNumerator (succ i) H p q) k) (stepScale p q k) (lipschitz q k R) (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDenominator H q (succ k) R) (pw (rootNumerator (succ i) H p q) k) (unit s)) := by
  refine .allI (.impI ?_)
  have hi' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift H) := by simpa [Fm.shift,Syn.shift] using hi.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  have hH := hs.andE₂.andE₁
  have hpq := hs.andE₂.andE₂.andE₁
  have hN := hs.andE₂.andE₂.andE₂
  have hW := width_positive (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k) hH hpq
  let Δ := lt (var 0) (Syn.shift (panelWidth i H p q (succ k))) :: Γ.map Fm.shift
  have widthEq : Syn.shift (panelWidth i H p q (succ k)) = panelWidth (Syn.shift i) (Syn.shift H) (Syn.shift p) (Syn.shift q) (succ (Syn.shift k)) := by simp [Syn.shift,panelWidth]
  have hj : Δ ⊢[PRAAx] lt (var 0) (panelWidth (Syn.shift i) (Syn.shift H) (Syn.shift p) (Syn.shift q) (succ (Syn.shift k))) := by
    rw [← widthEq]
    exact Prf.hyp0
  have rowBound := actual_row_norm_bound (Γ := Δ) (Syn.shift i) (var 0) (Syn.shift s) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k)
    (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hH.wk (le_of_lt hpq).wk hi'.wk
    hj hW.wk hs.andE₁.wk hN.wk
  have actual := GaussianLowerRootQuadratureBound.literal_panel_row (Γ := Δ) evaluatorF (Syn.shift i) (var 0) (Syn.shift s) (Syn.shift H)
    (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift R) (sampleDataBeta (Syn.shift z) (Syn.shift B) (Syn.shift N))
  simpa [Δ,GaussianUniformFiniteSumBound.summandsBounded,panelWidth,stepScale,Syn.shift] using
    bound_congr actual.eqSymm (.eqRefl _) (.eqRefl _) rowBound

theorem generic_source (s z R B H p q k N : PTm n) (h : Γ ⊢[PRAAx] source z R B H p q k N) : Γ ⊢[PRAAx]
    GaussianLowerRootQuadratureBound.source evaluatorF s H p q k R (lipschitz q k R) (sampleDataBeta z B N) := by
  have rows : Γ ⊢[PRAAx] GaussianLowerRootQuadratureBound.panelRows evaluatorF s H p q k R (lipschitz q k R) (sampleDataBeta z B N) := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
    simpa [GaussianLowerRootQuadratureBound.panelRows,Syn.shift] using
      original_panel_rows (var 0) (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift k) (Syn.shift N) Prf.hyp0 hs.wk
  exact .andI h.andE₂.andE₁ (.andI (le_of_lt h.andE₂.andE₂.andE₁)
    (.andI (width_positive H p q k h.andE₂.andE₁ h.andE₂.andE₂.andE₁) rows))

/-- Exact finite lower-tail quadrature bound. The only beta-degree guard
is N>=1; the original transformed geometry and all constants ignore N. -/
theorem original_finite_beta_lower_tail_bound (s z R B H p q k N : PTm n) (h : Γ ⊢[PRAAx] source z R B H p q k N) : Γ ⊢[PRAAx]
    bounded (originalQuadrature s z R B H p q k N)
      (H*GaussianEulerLowerBlockWeight.numerator (rootDenominator H q (succ k) R) (stepScale p q k) (lipschitz q k R) (unit s))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator H q (succ k) R) (unit s)) :=
  GaussianLowerRootQuadratureBound.finite_bound evaluatorF s H p q k R (lipschitz q k R) (sampleDataBeta z B N) (generic_source s z R B H p q k N h)

/-- Existing exact root-height arithmetic converts the finite bound to
A/2^height(p)+a fixed error constant/2^t. It is uniform in beta degree. -/
theorem converted_finite_bound (s t z R B H p q k N : PTm n) (h : Γ ⊢[PRAAx] source z R B H p q k N)
    (hMesh : Γ ⊢[PRAAx] le (unit t) H) (hPrecision : Γ ⊢[PRAAx] le (unit t) (unit s)) : Γ ⊢[PRAAx]
    bounded (originalQuadrature s z R B H p q k N)
      (GaussianEulerLowerTailFiniteBudget.numerator t p q k R (lipschitz q k R)) (GaussianEulerLowerTailFiniteBudget.denominator t p k R) := by
  have matched : Γ ⊢[PRAAx] bounded (originalQuadrature s z R B H p q k N)
      (GaussianEulerLowerTailFiniteBudget.oldNumerator H (rootDenominator H q (succ k) R) (GaussianEulerLowerTailFiniteBudget.scale p q k) (lipschitz q k R) (unit s))
      (GaussianEulerLowerTailFiniteBudget.oldDenominator (rootDenominator H q (succ k) R) (unit s)) :=
    bound_congr (.eqRefl _) (by unfold GaussianEulerLowerTailFiniteBudget.oldNumerator GaussianEulerLowerTailFiniteBudget.scale GaussianEulerLowerBlockWeight.numerator stepScale; ipra_ring)
      (.eqRefl _) (original_finite_beta_lower_tail_bound s z R B H p q k N h)
  exact GaussianEulerLowerTailFiniteBudget.original_radius_conversion _ s t H p q k R (lipschitz q k R)
    (le_of_lt h.andE₂.andE₂.andE₁) hMesh hPrecision matched

theorem original_beta_lower_root_fixed_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      sampledModulus evaluatorF (timeNumerator zero (var 3) (var 4) (var 5) (succ (var 6)))
        (totalWidth (var 3) (var 4) (var 5) (succ (var 6))) (timeDenominator (var 3) (var 5) (succ (var 6)) (var 1))
        (lipschitz (var 5) (var 6) (var 1)) (sampleDataBeta (var 0) (var 2) (var 7))) :=
  closeUniv 8 (.impI (root_modulus _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    (le_of_lt Prf.hyp0.andE₂.andE₂.andE₁) Prf.hyp0.andE₂.andE₂.andE₂))
theorem original_finite_beta_lower_tail_degree_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (originalQuadrature (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (var 4*GaussianEulerLowerBlockWeight.numerator (rootDenominator (var 4) (var 6) (succ (var 7)) (var 2))
          (stepScale (var 5) (var 6) (var 7)) (lipschitz (var 6) (var 7) (var 2)) (unit (var 0)))
        (GaussianEulerLowerBlockWeight.denominator (rootDenominator (var 4) (var 6) (succ (var 7)) (var 2)) (unit (var 0)))) :=
  closeUniv 9 (.impI (original_finite_beta_lower_tail_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_finite_beta_lower_tail_converted_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏ le (unit (var 1)) (var 5) ⋏ le (unit (var 1)) (unit (var 0))) ⟶
      bounded (originalQuadrature (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (GaussianEulerLowerTailFiniteBudget.numerator (var 1) (var 6) (var 7) (var 8) (var 3) (lipschitz (var 7) (var 8) (var 3)))
        (GaussianEulerLowerTailFiniteBudget.denominator (var 1) (var 6) (var 8) (var 3))) :=
  closeUniv 10 (.impI (converted_finite_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelLowerRootQuadrature
