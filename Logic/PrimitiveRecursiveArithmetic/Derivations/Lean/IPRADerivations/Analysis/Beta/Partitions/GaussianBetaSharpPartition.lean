import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpDegreeSchedule

/-!
# The sharp Euler split on the original dyadic grid

The original denominator is even on the native source. Thus time one,
the exact half of any degree, the degree itself and the original upper
cutoff are integer numerator positions on that same grid.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpPartition

open_ipra
open GaussianGammaIntegralCutoffs (etaDen top height height_positive eta_den_positive)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCompactRiemannName (fraction_congr)
open GaussianCompactRiemannSplit (fraction_cancel)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def halfDen (k A R : PTm n) : PTm n := unit (monus (A*height k A R) one)
def halfPoint (k A R N : PTm n) : PTm n := halfDen k A R*N
def lowWidth (k A R : PTm n) : PTm n := monus (etaDen k A R) one
def middleWidth (k A R N : PTm n) : PTm n := monus (halfPoint k A R N) (etaDen k A R)
def supportTailWidth (k A R N : PTm n) : PTm n := monus (etaDen k A R*N) (halfPoint k A R N)
def exteriorWidth (k A R N : PTm n) : PTm n := monus (etaDen k A R*top k A R) (etaDen k A R*N)
def source (k A R N : PTm n) : Fm PTm n := le one A ⋏ (le two N ⋏ le N (top k A R))

theorem even_denominator (k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] etaDen k A R ≐ two*halfDen k A R := by
  let exponent := A*height k A R
  let previous := monus exponent one
  have pos : Γ ⊢[PRAAx] le one exponent := positive_product _ _ hA (height_positive k A R)
  have retime : Γ ⊢[PRAAx] exponent ≐ succ previous :=
    ((eq_add_of_le pos).eqTrans (add_comm _ _)).eqTrans (succ_eq_add_one _).eqSymm
  exact ((congrAp2 powF retime (.eqRefl two)).eqTrans (pw_succ two previous)).eqTrans (mul_comm _ _)

theorem half_boundary_order (k A R N : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] le (etaDen k A R) (halfPoint k A R N) ⋏ le (halfPoint k A R N) (etaDen k A R*N) := by
  let H := halfDen k A R
  have even := even_denominator k A R hA
  have lower := le_congr even.eqSymm (mul_comm _ _) (mul_le_mul_right H hN)
  have grow : Γ ⊢[PRAAx] le H (two*H) := le_of_eq_add (d := H) (by ipra_ring)
  exact .andI lower (mul_le_mul_right N (le_congr (.eqRefl H) even.eqSymm grow))

/-- The four widths are exact even when the interval from one to the
half degree has width zero. -/
theorem exact_partition (k A R N : PTm n) (h : Γ ⊢[PRAAx] source k A R N) :
    Γ ⊢[PRAAx] (one+lowWidth k A R ≐ etaDen k A R) ⋏
      ((etaDen k A R+middleWidth k A R N ≐ halfPoint k A R N) ⋏
       ((halfPoint k A R N+supportTailWidth k A R N ≐ etaDen k A R*N) ⋏
        (etaDen k A R*N+exteriorWidth k A R N ≐ etaDen k A R*top k A R))) := by
  have mid := half_boundary_order k A R N h.andE₁ h.andE₂.andE₁
  have out := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (etaDen k A R) h.andE₂.andE₂)
  exact .andI (eq_add_of_le (eta_den_positive k A R)).eqSymm
    (.andI (eq_add_of_le mid.andE₁).eqSymm (.andI (eq_add_of_le mid.andE₂).eqSymm (eq_add_of_le out).eqSymm))

theorem half_point_fraction (k A R N : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] fraction (halfPoint k A R N) (etaDen k A R) ≐ fraction N two :=
  (fraction_congr _ _ _ _ (.eqRefl _) ((even_denominator k A R hA).eqTrans (mul_comm _ _))).eqTrans
    (fraction_cancel _ _ _ (unit_positive _) (zero_lt_succ one))

theorem half_point_decay_sample (q k A R N : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] ap2 decayF q (decayData (halfPoint k A R N) (two*etaDen k A R)) ≐
      ap2 decayF q (decayData N (num 4)) := by
  let H := halfDen k A R
  let X := fraction (halfPoint k A R N) (two*etaDen k A R)
  let Y := fraction N (num 4)
  have es : Γ ⊢[PRAAx] two*etaDen k A R ≐ H*num 4 :=
    (congrMul (.eqRefl two) (even_denominator k A R hA)).eqTrans (by ipra_ring)
  have fm : Γ ⊢[PRAAx] X ≐ Y :=
    (fraction_congr _ _ _ _ (.eqRefl _) es).eqTrans
      (fraction_cancel H N (num 4) (unit_positive _) GaussianEulerSharpDegreeSchedule.four_positive)
  have same := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (GaussianGammaFiniteApproximantName.exponentialInputData GaussianGammaCanonicalExponent.constantF
      (GaussianRationalMetric.qnegative (var 0)) : PTm 1)
    (σ := ![X]) (σ' := ![Y]) (fun i => by fin_cases i; exact fm)
  exact congrAp2 decayF (.eqRefl q) (by
    simpa [decayData,decayPoint,GaussianGammaFiniteApproximantName.exponentialInputData,X,Y] using same)

theorem original_sharp_Euler_partition_at_one_and_half_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) (var 3) ⟶
        ((one+lowWidth (var 0) (var 1) (var 2) ≐ etaDen (var 0) (var 1) (var 2)) ⋏
          ((etaDen (var 0) (var 1) (var 2)+middleWidth (var 0) (var 1) (var 2) (var 3) ≐ halfPoint (var 0) (var 1) (var 2) (var 3)) ⋏
           ((halfPoint (var 0) (var 1) (var 2) (var 3)+supportTailWidth (var 0) (var 1) (var 2) (var 3) ≐ etaDen (var 0) (var 1) (var 2)*var 3) ⋏
            (etaDen (var 0) (var 1) (var 2)*var 3+exteriorWidth (var 0) (var 1) (var 2) (var 3) ≐
              etaDen (var 0) (var 1) (var 2)*top (var 0) (var 1) (var 2)))))) :=
  closeUniv 4 (.impI (exact_partition _ _ _ _ Prf.hyp0))

theorem original_half_degree_tail_decay_on_same_grid_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 2) ⟶ ap2 decayF (var 0)
        (decayData (halfPoint (var 1) (var 2) (var 3) (var 4)) (two*etaDen (var 1) (var 2) (var 3))) ≐
        ap2 decayF (var 0) (decayData (var 4) (num 4))) :=
  closeUniv 5 (.impI (half_point_decay_sample _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpPartition
