import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GridBounds.GaussianStirlingAllOrderFullGridCovariance
import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GridBounds.GaussianStirlingAllOrderBernoulliGridRate

/-!
# Readback of the full Bernoulli mean and its exact finite correction

The original full panel contains the same centered Bernoulli mesh as
the signed polynomial fold. Its mean can therefore be replaced by the
signed integral mean plus the explicit coefficient-radius error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFullGridMeanRate

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticBounds (add_monotone)
open BernoulliBounds (bden bden_pos)
open GaussianStirlingAllOrderBernoulliGridMean (body body_at coefficients)
open GaussianStirlingAllOrderBernoulliGridRate (average mean_error)
open GaussianStirlingAllOrderBoxProductGap (sampleAt)
open GaussianStirlingAllOrderCrossedCells (bernoulliBody bernoulli_at segmentData subst_sampleAt subst_segmentData)
open GaussianStirlingAllOrderFullGridCovariance
  (fullMean doubledWeight midpointCorrection full_grid_covariance doubled_weight_nonnegative)
open GaussianStirlingAllOrderHalfGridMean (margin)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderPanelTail (panel)
open RationalAlgebra (multiply_congr multiply_commutative)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (add multiply multiply_monotone order_of_representations)
open RationalFiniteSum (term termwiseEq sum_ext)
open RationalPolynomialGridMeanError (radius)
open RationalRepresentedUpper (left right to_signed)
open RationalRepresentations (represents_add represents_self)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem zero_index (m : ℕ) (S i : PTm n) : Γ ⊢[PRAAx] sampleAt m S (zero+i) ≐ sampleAt m S i := by
  simpa only [subst_sampleAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Γ := Γ) (sampleAt m (var 0) (var 1) : PTm 2) (σ := ![S,zero+i]) (σ' := ![S,i])
      (fun j => by fin_cases j <;> first | exact zero_add i | exact .eqRefl _)

theorem full_mean_readback (m : ℕ) (q U B S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] fullMean m q U B S ≐ average (m+1) (S*num 8) := by
  let f := bernoulliBody m
  let g := body (m+1)
  let M := S*num 8
  let x := segmentData q U B S zero
  have h : Γ ⊢[PRAAx] termwiseEq f g M x M := by
    refine .allI (.impI ?_)
    let T := Syn.shift S
    let i : PTm (n+1) := var 0
    let Δ := lt i (T*num 8) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] le one T := (by simpa [Fm.shift,Syn.shift,T] using hS.shift : Γ.map Fm.shift ⊢[PRAAx] le one T).wk
    have hm : Δ ⊢[PRAAx] le one (T*num 8) := positive_product _ _ hs (by ipra_le 7)
    have e := (bernoulli_at (Γ := Δ) m i (Syn.shift q) (Syn.shift U) (Syn.shift B) T zero).eqTrans
      (zero_index m T i)
    have row := e.eqTrans (body_at (m+1) i (T*num 8) hm).eqSymm
    simpa [termwiseEq,f,g,M,x,T,i,Δ,Syn.shift] using (RationalArgmin.rationalEq_congr row.eqSymm (.eqRefl _) (.eqRefl _))
  exact multiply_congr (.eqRefl _) (sum_ext f g M x M h)

alias upper_as_added_fraction := RationalConvexEndpointBudget.order_of_upper

def meanErrorNumerator (m : ℕ) : PTm n := num (radius (coefficients (m+1)))
def meanErrorDenominator (m : ℕ) (S : PTm n) : PTm n := num (bden (2*(m+1)))*(S*num 8)

def correctedMean (m : ℕ) (S : PTm n) : PTm n :=
  add (signedMean (m+1)) (fraction (meanErrorNumerator m) (meanErrorDenominator m S))

theorem full_mean_le (m : ℕ) (q U B S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (fullMean m q U B S) (correctedMean m S) := by
  have hM : Γ ⊢[PRAAx] le one (S*num 8) := positive_product _ _ hS (by ipra_le 7)
  have hD : Γ ⊢[PRAAx] le one (meanErrorDenominator m S) :=
    positive_product _ _ (Foundations.NumeralPrimes.num_le (bden_pos (2*(m+1)))) hM
  have h := (mean_error (m+1) (S*num 8) (by omega) hM).andE₁
  have e := full_mean_readback m q U B S hS
  exact upper_as_added_fraction _ _ _ _ hD (upper_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) h)

noncomputable def meanComparison (m : ℕ) (q A B S k : PTm n) : Fm PTm n :=
  let U := A+B*k
  rationalLE (add (multiply (fraction two one) (panel m q A B (S*num 8) k)) (margin m q U B))
    (add (multiply (correctedMean m S) (doubledWeight q U B S)) (midpointCorrection m q A B S k))

theorem signed_mean_covariance (m : ℕ) (q A B S k : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] meanComparison m q A B S k := by
  let U := A+B*k
  let V := doubledWeight q U B S
  let T := midpointCorrection m q A B S k
  have p := doubled_weight_nonnegative q U B S (le_trans hA (le_add_right _ _)) hS
  have raw := multiply_monotone V _ _ p (full_mean_le m q U B S hS)
  have e := rationalLE_congr (multiply_commutative V (fullMean m q U B S))
    (multiply_commutative V (correctedMean m S)) raw
  exact transitive (full_grid_covariance m q A B S k hA hB hS) (add_monotone _ _ T T e (reflexive _))

theorem actual_original_full_left_panel_signed_mean_comparison_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
        meanComparison m (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (signed_mean_covariance m _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFullGridMeanRate
