import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerTailPartition
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerTransformedIntegrand

/-!
# The literal eta-to-one panel on the existing transformed root grid

The old root numerators and partition program are reused at ratio index
height(k,A,R), while the denominator uses the original cutoff k. The
first point is exactly eta_k and the last exactly one. Actual original
Euler right-endpoint observations retain their checked sharp transformed
power bound. Extending the old uniform-grid local comparison to these
decoupled indices is the remaining compact-panel step.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerEtaToOneRootGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height etaDen)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianCompactRiemannName (quadrature sampleBody sampleData)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianRationalFiniteSum (sum)
open GaussianPartitionedFiniteSum (blockBody)
open GaussianEulerLowerTailPartition (cutF cutData offset_at offset_zero cut_increasing)
open GaussianRationalRiemannRefinement (weight)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def root (i H k A R : PTm n) : PTm n := GaussianEulerLowerTailRootGrid.rootNumerator i H zero (height k A R)
def rootDen (H k A R : PTm n) : PTm n := GaussianEulerLowerTailRootGrid.rootDenominator H k A R
def time (i H k A R : PTm n) : PTm n := GaussianEulerLowerTailRootGrid.timeNumerator i H zero (height k A R) A
def timeDen (H k A R : PTm n) : PTm n := GaussianEulerLowerTailRootGrid.timeDenominator H k A R
def totalWidth (H k A R : PTm n) : PTm n := GaussianEulerLowerTailPartition.totalWidth H zero (height k A R) A
def rightTime (i H k A R : PTm n) : PTm n := GaussianEulerIntegrandName.timeData (time (succ i) H k A R) (timeDen H k A R)

theorem exact_ratio (k A R : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerLowerTailRootGrid.rootRatio zero (height k A R) ≐ unit (height k A R) :=
  congrAp2 powF (monus_zero _) (.eqRefl two)

theorem root_first (H k A R : PTm n) : Γ ⊢[PRAAx] root zero H k A R ≐ H :=
  GaussianEulerLowerTailRootGrid.root_first _ _ _
theorem root_last (H k A R : PTm n) : Γ ⊢[PRAAx] root H H k A R ≐ rootDen H k A R :=
  (GaussianEulerLowerTailRootGrid.root_last H zero (height k A R)).eqTrans (congrMul (exact_ratio k A R) (.eqRefl H))
theorem first_time (H k A R : PTm n) : Γ ⊢[PRAAx] time zero H k A R ≐ pw H A :=
  GaussianEulerLowerTailRootGrid.time_first _ _ _ _
theorem last_time (H k A R : PTm n) : Γ ⊢[PRAAx] time H H k A R ≐ timeDen H k A R :=
  congrAp2 powF (.eqRefl A) (root_last H k A R)
theorem exact_denominator (H k A R : PTm n) : Γ ⊢[PRAAx] timeDen H k A R ≐ etaDen k A R*pw H A :=
  GaussianEulerLowerTailRootGrid.time_denominator _ _ _ _

theorem exact_width (H k A R : PTm n) : Γ ⊢[PRAAx]
    totalWidth H k A R ≐ monus (etaDen k A R) one*pw H A := by
  have ratio : Γ ⊢[PRAAx] GaussianGammaCompactCutoffGeometry.ratio zero (height k A R) A ≐ etaDen k A R :=
    congrAp2 powF (congrMul (.eqRefl A) (monus_zero (height k A R))) (.eqRefl two)
  exact (GaussianEulerLowerTailRootGrid.time_width H zero (height k A R) A).eqTrans
    (congrMul (congrMonus ratio (.eqRefl one)) (.eqRefl _))

theorem denominator_positive (H k A R : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx] le one (rootDen H k A R) :=
  positive_product _ _ (unit_positive _) hH

theorem right_guard (i H k A R : PTm n) (hH : Γ ⊢[PRAAx] le one H) (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    le one (root (succ i) H k A R) ⋏ le (root (succ i) H k A R) (rootDen H k A R) := by
  let S := monus (GaussianEulerLowerTailRootGrid.rootRatio zero (height k A R)) one
  have pos : Γ ⊢[PRAAx] le one (root (succ i) H k A R) := le_trans hH (le_add_right H (S*succ i))
  have cmp : Γ ⊢[PRAAx] le (root (succ i) H k A R) (root H H k A R) :=
    add_le_add₂ (le_refl H) (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right S hi))
  exact .andI pos (le_congr (.eqRefl _) (root_last H k A R) cmp)

/-- The existing literal partition program groups this actual quadrature
even though the new denominator has its own original cutoff index. -/
theorem grouped_original_quadrature (F : PR 3) (s H k A R x : PTm n) : Γ ⊢[PRAAx]
    quadrature F s (totalWidth H k A R) (time zero H k A R) (totalWidth H k A R) (timeDen H k A R) x ≐
      qmul (weight (totalWidth H k A R) (timeDen H k A R) (totalWidth H k A R))
        (sum (blockBody cutF (sampleBody F)) H
          (pairT (cutData H zero (height k A R) A)
            (sampleData s (totalWidth H k A R) (time zero H k A R) (totalWidth H k A R) (timeDen H k A R) x))) := by
  let d := cutData H zero (height k A R) A
  let W := totalWidth H k A R
  let y := sampleData s W (time zero H k A R) W (timeDen H k A R) x
  have grouped := GaussianPartitionedFiniteSum.grouped_from_zero (Γ := Γ) cutF (sampleBody F) H d y
    (cut_increasing H zero (height k A R) A) ((offset_at zero H zero (height k A R) A).eqTrans (offset_zero H zero (height k A R) A))
  exact qmul_congr (.eqRefl _) ((grouped.eqTrans
    (GaussianRationalFiniteSum.sum_index_congr (sampleBody F) (offset_at H H zero (height k A R) A) (.eqRefl y))).eqSymm)

/-- A source-only norm of the original Euler evaluator at each actual
right transformed root, with the exact reciprocal-root power retained. -/
theorem original_right_observation_bound (i p H k z R B A : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hi : Γ ⊢[PRAAx] lt i H)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF p (rightTime i H k A R) (fixedData z B))
      (pw (rootDen H k A R) (pred A)*unit p+pw (root (succ i) H k A R) (pred A))
      (pw (root (succ i) H k A R) (pred A)*unit p) := by
  have guards := right_guard i H k A R hH hi
  have dpos := denominator_positive H k A R hH
  have src : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R B A (root (succ i) H k A R) (rootDen H k A R) :=
    .andI h (.andI (.andI guards.andE₁ dpos) guards.andE₂)
  have value := GaussianEulerIntegrandName.sample_at (Γ := Γ) p z B
    (pw (root (succ i) H k A R) A) (pw (rootDen H k A R) A)
  exact GaussianRationalReciprocal.bound_congr value.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerLowerTransformedIntegrand.original_integrand_bound p z R B A (root (succ i) H k A R) (rootDen H k A R) src)

theorem actual_eta_to_one_root_grid_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((time zero (var 0) (var 1) (var 2) (var 3) ≐ pw (var 0) (var 2)) ⋏
      ((time (var 0) (var 0) (var 1) (var 2) (var 3) ≐ timeDen (var 0) (var 1) (var 2) (var 3)) ⋏
        totalWidth (var 0) (var 1) (var 2) (var 3) ≐ monus (etaDen (var 1) (var 2) (var 3)) one*pw (var 0) (var 2))) :=
  closeUniv 4 (.andI (first_time _ _ _ _) (.andI (last_time _ _ _ _) (exact_width _ _ _ _)))

theorem actual_eta_to_one_original_Euler_right_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 2) ⋏ (lt (var 0) (var 2) ⋏ GaussianEulerLowerPowerCoefficients.source (var 4) (var 5) (var 6) (var 7))) ⟶
      bounded (ap3 evaluatorF (var 1) (rightTime (var 0) (var 2) (var 3) (var 7) (var 5)) (fixedData (var 4) (var 6)))
        (pw (rootDen (var 2) (var 3) (var 7) (var 5)) (pred (var 7))*unit (var 1)+
          pw (root (succ (var 0)) (var 2) (var 3) (var 7) (var 5)) (pred (var 7)))
        (pw (root (succ (var 0)) (var 2) (var 3) (var 7) (var 5)) (pred (var 7))*unit (var 1))) :=
  closeUniv 8 (.impI (original_right_observation_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerEtaToOneRootGrid
