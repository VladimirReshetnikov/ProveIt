import IPRADerivations.Analysis.Beta.Tails.ZeroExtension.GaussianBetaZeroTailDifferencePointwise
import IPRADerivations.Analysis.Beta.Tails.KernelDifferences.GaussianBetaEulerUpperDifferenceGrid

/-!
# One half-decay majorant on a contiguous zero-extended upper grid

The original zero-extended beta and Euler evaluators use one shared
mesh across the degree endpoint. Their literal difference is dominated
by one scaled half-decay quadrature over the whole interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaZeroUpperDifferenceGrid

open_ipra
open GaussianEulerUpperPowerCoefficients (source)
open GaussianBetaEulerTailDifferencePointwise (referenceError)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerCompactUpperTail (halfEvaluator)
open GaussianBetaEulerUpperDifferenceGrid (scalarBody scalar_body_at grid_bound_of_majorized_difference)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at)
open GaussianRationalSumMajorant (majorized termsMajorized majorized_congr)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem majorized_row (i p M a C E z R B N : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a) (h : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    majorized (inst2 (differenceBody (sampleBody GaussianBetaZeroExtension.evaluatorF) (sampleBody GaussianEulerIntegrandName.evaluatorF)) i
      (pairT (sampleData p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
        (sampleData p M a C E (GaussianEulerIntegrandName.fixedData z B))))
      (inst2 scalarBody i (sampleData p M a C E R)) := by
  let u := a*M+C*i
  let v := E*M
  have hv := positive_product (Γ := Γ) _ _ hE hM
  have hle : Γ ⊢[PRAAx] le v u := le_trans (mul_le_mul_right M hea) (le_add_right _ _)
  have hs : Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B u v := .andI h (.andI (.andI (le_trans hv hle) hv) hle)
  have left := sample_body_at (Γ := Γ) GaussianBetaZeroExtension.evaluatorF i p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N)
  have right := sample_body_at (Γ := Γ) GaussianEulerIntegrandName.evaluatorF i p M a C E (GaussianEulerIntegrandName.fixedData z B)
  have point := (difference_body_at _ _ i _ _).eqTrans (qsub_congr left right)
  exact majorized_congr point.eqSymm (scalar_body_at i p M a C E R).eqSymm
    (GaussianBetaZeroTailDifferencePointwise.original_cell_majorized p z R B u v N hs hN)

theorem original_grid_bound_from_scaled_half (p M a C E z R B N U V : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a)
    (h : Γ ⊢[PRAAx] source z R B) (hN : Γ ⊢[PRAAx] le one N) (hV : Γ ⊢[PRAAx] le one V)
    (hHalf : Γ ⊢[PRAAx] bounded (qmul (GaussianDominantPairAlgebra.radiusPoint (majorant R) one)
      (quadrature halfEvaluator p M a C E zero)) U V) : Γ ⊢[PRAAx]
    distanceBounded (quadrature GaussianBetaZeroExtension.evaluatorF p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF p M a C E (GaussianEulerIntegrandName.fixedData z B))
      ((C*referenceError R)*V+U*(E*unit p)) ((E*unit p)*V) := by
  let f := sampleBody GaussianBetaZeroExtension.evaluatorF
  let g := sampleBody GaussianEulerIntegrandName.evaluatorF
  let X := sampleData p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N)
  let Y := sampleData p M a C E (GaussianEulerIntegrandName.fixedData z B)
  let Z := sampleData p M a C E R
  have hm : Γ ⊢[PRAAx] termsMajorized (differenceBody f g) scalarBody M (pairT X Y) Z := by
    have m' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    have ea' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift E) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hea.shift
    have h' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
    have n' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    refine .allI (.impI ?_)
    simpa only [termsMajorized,X,Y,Z,f,g,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_pairT,
      GaussianBetaKernelGridComparison.subst_sampleDataBeta,GaussianEulerIntegrandName.subst_fixedData] using
      majorized_row (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) m'.wk e'.wk ea'.wk h'.wk n'.wk
  exact grid_bound_of_majorized_difference f g p M a C E R X Y U V hM hE hV hHalf hm

theorem original_contiguous_zero_extended_upper_grid_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((le one (var 1) ⋏ le one (var 4) ⋏ le (var 4) (var 2)) ⟶ source (var 5) (var 6) (var 7) ⟶ le one (var 8) ⟶
      (le one (var 10) ⋏ bounded (qmul (GaussianDominantPairAlgebra.radiusPoint (majorant (var 6)) one)
        (quadrature halfEvaluator (var 0) (var 1) (var 2) (var 3) (var 4) zero)) (var 9) (var 10)) ⟶
      distanceBounded (quadrature GaussianBetaZeroExtension.evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4)
        (GaussianBetaKernelGridComparison.sampleDataBeta (var 5) (var 7) (var 8)))
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (GaussianEulerIntegrandName.fixedData (var 5) (var 7)))
        ((var 3*referenceError (var 6))*var 10+var 9*(var 4*unit (var 0))) ((var 4*unit (var 0))*var 10)) :=
  closeUniv 11 (.impI (.impI (.impI (.impI (original_grid_bound_from_scaled_half _ _ _ _ _ _ _ _ _ _ _
    hyp2.wk.andE₁ hyp2.wk.andE₂.andE₁ hyp2.wk.andE₂.andE₂ hyp2 Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))))

end LeanProofs.IPRA.Analysis.GaussianBetaZeroUpperDifferenceGrid
