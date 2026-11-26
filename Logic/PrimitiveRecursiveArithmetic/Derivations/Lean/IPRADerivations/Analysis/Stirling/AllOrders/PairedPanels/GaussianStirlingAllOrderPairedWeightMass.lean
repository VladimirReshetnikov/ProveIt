import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPairedWeightFold
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsRecurrence

/-!
# The paired-weight and integration-by-parts mass use the same samples

The unweighted full-interval average in the covariance estimate
is precisely the original reciprocal-power sum used in the
integration-by-parts recurrence.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedWeightMass

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num subst_num)
open GaussianStirlingAllOrderPairedRefinement (mesh start)
open GaussianStirlingAllOrderPairedWeight (weight)
open GaussianStirlingAllOrderPairedWeightFold
  (singleWeight weightData weightBody weight_row_at weightAverage subst_weightData)
open GaussianStirlingAllOrderPanelPartsFinite (weightAt parameters weight_at subst_parameters)
open GaussianStirlingAllOrderPanelPartsRecurrence (panelMass)
open GaussianStirlingAllOrderReciprocalGridError (gridDen)
open RationalAlgebra (multiply_congr)
open RationalArgmin (rationalEq_congr)
open RationalFiniteSum (sum sum_ext termwiseEq)
open RationalNonnegativePowers (fraction_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_weight (e : ℕ) (he : 1≤e) (A B S i : PTm n) :
    Γ ⊢[PRAAx] singleWeight (num (e-1)) A B S i ≐ weightAt e A B (S*num 8) i := by
  have exp : succ (num (e-1) : PTm n) = num e := by
    change num ((e-1)+1) = num e
    congr 1
    omega
  unfold singleWeight weight weightAt GaussianStirlingAllOrderReciprocalWeightError.weight
    GaussianStirlingAllOrderReciprocalWeightError.power
  rw [exp]
  exact fraction_congr (congrAp2 powF (.eqRefl _) (by unfold mesh; ipra_ring))
    (congrAp2 powF (.eqRefl _) (by unfold start gridDen; ipra_ring))

theorem original_weight_average (e : ℕ) (he : 1≤e) (A B S : PTm n) :
    Γ ⊢[PRAAx] weightAverage (num (e-1)) A B S ≐ panelMass e A B (S*num 8) := by
  apply multiply_congr (.eqRefl _)
  apply sum_ext
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh S*num 8) :: Γ.map Fm.shift
  let q : PTm (n+1) := num (e-1)
  have eq := (weight_row_at (Γ := Δ) i q (sh A) (sh B) (sh S)).eqTrans
    ((original_weight e he (sh A) (sh B) (sh S) i).eqTrans
      (weight_at e (sh A) (sh B) (sh S*num 8) i).eqSymm)
  simpa only [Δ,termwiseEq,RationalFiniteSum.term,sh,i,q,Syn.shift,subst_weightData,
    GaussianStirlingAllOrderPanelPartsFold.weightInput,subst_parameters,PTm.subst_mul,subst_num] using
    rationalEq_congr eq.eqSymm (.eqRefl _) (.eqRefl _)

theorem actual_reflected_weight_average_original_mass_closed (e : ℕ) (he : 1≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (weightAverage (num (e-1)) (var 0) (var 1) (var 2) ≐ panelMass e (var 0) (var 1) (var 2*num 8)) :=
  closeUniv 3 (original_weight_average e he _ _ _)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedWeightMass
