import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPairedReadback
import IPRADerivations.Analysis.Stirling.AllOrders.Covariance.GaussianStirlingAllOrderCrossedRectangles
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelTail
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumMirror

/-!
# The reflected weighted fold recovers the original panel

On a mesh of length 8S the original left-endpoint sum equals the
reflected weighted sum over the first 4S indices plus the midpoint
row. The omitted right endpoint is zero by centered Bernoulli
reflection and endpoint evaluation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedPanel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (positive_product)
open GaussianStirlingAllOrderCenteredBernoulli (endpoint_samples_zero)
open GaussianStirlingAllOrderCrossedCells (segmentData bernoulliBody reflectedBody subst_segmentData)
open GaussianStirlingAllOrderCrossedRectangles (pairedSum)
open GaussianStirlingAllOrderKernel (row multiply_zero_right)
open GaussianStirlingAllOrderPairedReadback (original_paired_term)
open GaussianStirlingAllOrderPanelTail (panelBody panelData panel panel_row_at subst_panelData)
open RationalAlgebra (add_congr multiply_congr multiply_commutative)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalEq_congr)
open RationalCrossedProductSums (productBody)
open RationalFiniteSum (sum term sum_ext termwiseEq sum_well_formed)
open RationalReciprocalPowerTail (add_zero_right)
open RationalSumMirror (mirrorBody mirrorData mirror_at mirror_sum subst_mirrorData)
open RationalSumSegments (sum_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num subst_num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem reflected_readback (m : ℕ) (q A B S k i : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hi : Γ ⊢[PRAAx] le i (S*num 4)) :
    Γ ⊢[PRAAx] term (mirrorBody (panelBody m)) i (mirrorData (S*num 4) (panelData q A B (S*num 8) k)) ≐
      term (productBody (bernoulliBody m) reflectedBody) i (segmentData q (A+B*k) B S zero) := by
  let M := S*num 8
  let N := S*num 4
  let f := panelBody m
  let x := panelData q A B M k
  have full : Γ ⊢[PRAAx] M ≐ N+N := by dsimp [M,N]; ipra_ring
  have hr : Γ ⊢[PRAAx] le (zero+i) M :=
    le_congr (zero_add i).eqSymm full.eqSymm (le_trans hi (le_add_right N N))
  have reflect : Γ ⊢[PRAAx] monus (N+N) i ≐ monus M (zero+i) :=
    congrMonus full.eqSymm (zero_add i).eqSymm
  have left : Γ ⊢[PRAAx] term f i x ≐ row m q A B M k (zero+i) :=
    (congrInst2 f (zero_add i).eqSymm (.eqRefl x)).eqTrans (panel_row_at m q A B M k _)
  have right : Γ ⊢[PRAAx] term f (monus (N+N) i) x ≐ row m q A B M k (monus M (zero+i)) :=
    (congrInst2 f reflect (.eqRefl x)).eqTrans (panel_row_at m q A B M k _)
  exact (mirror_at f i N x hi).eqTrans ((add_congr left right).eqTrans
    (original_paired_term m q A B S k zero i hS hr).eqSymm)

private theorem sum_readback (m : ℕ) (q A B S k : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] sum (mirrorBody (panelBody m)) (S*num 4) (mirrorData (S*num 4) (panelData q A B (S*num 8) k)) ≐
      pairedSum m q (A+B*k) B S zero (S*num 4) := by
  apply sum_ext
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh S*num 4) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i (sh S*num 4) := Prf.hyp0
  have hs : Δ ⊢[PRAAx] le one (sh S) := by
    simpa [Δ,Fm.shift,sh,Syn.shift,one] using hS.shift.wk
  have eq := reflected_readback m (sh q) (sh A) (sh B) (sh S) (sh k) i hs (le_of_lt hi)
  simpa only [Δ,termwiseEq,sh,i,Syn.shift,subst_panelData,subst_mirrorData,subst_segmentData,
    PTm.subst_mul,PTm.subst_add,subst_num,ConciseIPRA.PTm.subst_zero] using
      rationalEq_congr eq.eqSymm (.eqRefl _) (.eqRefl _)

theorem left_panel_fold (m : ℕ) (q A B S k : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] sum (panelBody m) (S*num 8) (panelData q A B (S*num 8) k) ≐
      add (pairedSum m q (A+B*k) B S zero (S*num 4)) (row m q A B (S*num 8) k (S*num 4)) := by
  let f := panelBody m
  let M := S*num 8
  let N := S*num 4
  let x := panelData q A B M k
  have endIndex : Γ ⊢[PRAAx] M ≐ N+N := by dsimp [M,N]; ipra_ring
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have lastZero : Γ ⊢[PRAAx] term f M x ≐ fraction zero one := by
    exact (panel_row_at m q A B M k M).eqTrans
      ((multiply_congr (endpoint_samples_zero (m+1) M hM).2 (.eqRefl _)).eqTrans
        ((multiply_commutative _ _).eqTrans (multiply_zero_right _)))
  have entry : Γ ⊢[PRAAx] add (sum f M x) (term f M x) ≐ sum f M x :=
    (add_congr (.eqRefl _) lastZero).eqTrans (add_zero_right _ (sum_well_formed f M x))
  exact entry.eqSymm.eqTrans ((add_congr (sum_congr f endIndex (.eqRefl x))
    (congrInst2 f endIndex (.eqRefl x))).eqTrans ((mirror_sum f N x).eqTrans
      (add_congr (sum_readback m q A B S k hS) (panel_row_at m q A B M k N))))

theorem original_panel (m : ℕ) (q A B S k : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] panel m q A B (S*num 8) k ≐
      multiply (fraction one (S*num 8))
        (add (pairedSum m q (A+B*k) B S zero (S*num 4)) (row m q A B (S*num 8) k (S*num 4))) :=
  multiply_congr (.eqRefl _) (left_panel_fold m q A B S k hS)

theorem actual_original_panel_half_grid_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (le one (var 3) ⟶
      panel m (var 0) (var 1) (var 2) (var 3*num 8) (var 4) ≐
        multiply (fraction one (var 3*num 8))
          (add (pairedSum m (var 0) (var 1+var 2*var 4) (var 2) (var 3) zero (var 3*num 4))
            (row m (var 0) (var 1) (var 2) (var 3*num 8) (var 4) (var 3*num 4)))) :=
  closeUniv 5 (.impI (original_panel m _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedPanel
