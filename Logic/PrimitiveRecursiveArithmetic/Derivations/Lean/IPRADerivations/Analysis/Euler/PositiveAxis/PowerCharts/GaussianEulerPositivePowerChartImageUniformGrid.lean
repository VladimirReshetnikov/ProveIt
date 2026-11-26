import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannSplit
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactUniformGridComparison
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithm

/-!
# Ordinary quadrature on a native rational lattice

At count K and width K/M the original evaluator samples the represented
times (a+i)/M, with exact weight 1/M on each row. The quadrature identity
also holds at K=0, when the finite sum is empty.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageUniformGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (fraction_congr grid inside quadrature sampleBody sampleData value value_grid)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum sum_index_congr)
open GaussianRationalHorner (qmul)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem grid_value (i K a M : PTm n) (hK : Γ ⊢[PRAAx] le one K) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] value (grid i K a K M) ≐ fraction (a+i) M :=
  (value_grid i K a K M).eqTrans
    ((fraction_congr _ _ _ _ (by ipra_ring : Γ ⊢[PRAAx] a*K+K*i ≐ K*(a+i))
      (mul_comm M K)).eqTrans
      (GaussianCompactRiemannSplit.fraction_cancel K (a+i) M hK hM))

theorem lattice_inside (i K a M : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hM : Γ ⊢[PRAAx] le one M)
    (hi : Γ ⊢[PRAAx] le i K) : Γ ⊢[PRAAx] inside a K M (pairT (a+i) M) := by
  have lo : Γ ⊢[PRAAx] le (a*M) (M*(a+i)) := le_of_eq_add (d := M*i) (by ipra_ring)
  have up : Γ ⊢[PRAAx] le (M*(a+i)) ((a+K)*M) :=
    le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right M (add_le_add₂ (le_refl a) hi))
  have left : Γ ⊢[PRAAx] fstT (pairT (a+i) M) ≐ a+i := fst_pair _ _
  have right : Γ ⊢[PRAAx] sndT (pairT (a+i) M) ≐ M := snd_pair _ _
  exact .andI (le_congr (.eqRefl _) left.eqSymm (le_trans ha (le_add_right a i)))
    (.andI (le_congr (.eqRefl _) right.eqSymm hM)
      (.andI (le_congr (congrMul (.eqRefl _) right.eqSymm) (congrMul (.eqRefl _) left.eqSymm) lo)
        (le_congr (congrMul (.eqRefl _) left.eqSymm) (congrMul (.eqRefl _) right.eqSymm) up)))

theorem weight_value (K M : PTm n) (hK : Γ ⊢[PRAAx] le one K) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] weight K M K ≐ fraction one M :=
  (fraction_congr _ _ _ _ (by ipra_ring : Γ ⊢[PRAAx] K ≐ K*one) (mul_comm M K)).eqTrans
    (GaussianCompactRiemannSplit.fraction_cancel K one M hK hM)

theorem quadrature_value (F : PR 3) (p K a M x : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] quadrature F p K a K M x ≐
      qmul (fraction one M) (sum (sampleBody F) K (sampleData p K a K M x)) := by
  refine .orE (zero_or_succ K) ?_ ?_
  · have h0 : (K ≐ zero)::Γ ⊢[PRAAx] K ≐ zero := Prf.hyp0
    have left := (GaussianCompactRiemannName.quadrature_index_congr F p K zero a K M x h0).eqTrans
      (GaussianCompactUniformGridComparison.empty_quadrature F p a K M x)
    have s0 := (sum_index_congr (sampleBody F) h0 (.eqRefl (sampleData p K a K M x))).eqTrans
      (GaussianRationalFiniteSum.sum_zero _ _)
    exact left.eqTrans ((qmul_congr (.eqRefl _) s0).eqTrans (qmul_zero_right _)).eqSymm
  · have hK : (K ≐ ConciseIPRA.PTm.succ (pred K))::Γ ⊢[PRAAx] le one K :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact qmul_congr (weight_value K M hK hM.wk) (.eqRefl _)

theorem actual_original_native_lattice_grid_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le one (var 3)) ⟶
      value (grid (var 0) (var 1) (var 2) (var 1) (var 3)) ≐ fraction (var 2+var 0) (var 3)) :=
  closeUniv 4 (.impI (grid_value _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_native_lattice_quadrature_value_closed (F : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 3) ⟶ quadrature F (var 0) (var 1) (var 2) (var 1) (var 3) (var 4) ≐
        qmul (fraction one (var 3)) (sum (sampleBody F) (var 1)
          (sampleData (var 0) (var 1) (var 2) (var 1) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (quadrature_value F _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageUniformGrid
