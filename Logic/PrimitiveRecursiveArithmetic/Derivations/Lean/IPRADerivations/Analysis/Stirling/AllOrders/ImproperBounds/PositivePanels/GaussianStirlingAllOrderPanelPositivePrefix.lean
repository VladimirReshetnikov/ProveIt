import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.PositivePanels.GaussianStirlingAllOrderPanelPositive
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.OuterSums.GaussianStirlingAllOrderPanelPartsOuterFold
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumReversal

/-!
# The same positive bound for every nonempty original panel prefix

The first weighted panel already contains a positive block.
The other panels have nonnegative samples, so the first panel's
mesh-independent lower bound persists after every positive cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPositivePrefix

open_ipra
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderKernel (multiply_zero_right)
open GaussianStirlingAllOrderPanelPartsOuter (data)
open GaussianStirlingAllOrderPanelPartsOuterFold (panel_at panelPrefix)
open GaussianStirlingAllOrderPanelPositive (panelFloor panel_floor_den_positive first_panel_positive_lower)
open GaussianStirlingAllOrderPanelTail (panel_envelope)
open RationalAlgebra (add_congr multiply_commutative)
open RationalArithmetic (add)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalFiniteSum (term sum termwiseLE sum_monotone)
open RationalNormalForm (normalize_well_formed)
open RationalReciprocalPowerTail (add_zero_right)
open RationalSumConstants (constantBody term_constant sum_constant)
open RationalSumReversal (sum_first)
open RationalSumSegments (sum_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem suffix_nonnegative (m q : ℕ) (A B M N : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) :
    let f := GaussianStirlingAllOrderPanelPartsOuterFold.panelBody m q
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (sum (offB f) N (pairT one (data A B M))) := by
  let f := GaussianStirlingAllOrderPanelPartsOuterFold.panelBody m q
  let x := pairT one (data A B M)
  let z : PTm n := fraction zero one
  have hrows : Γ ⊢[PRAAx] termwiseLE constantBody (offB f) N z x := by
    refine .allI (.impI ?_)
    let sh (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh N) :: Γ.map Fm.shift
    have ha : Δ ⊢[PRAAx] le one (sh A) := by simpa [Δ,Fm.shift,sh,Syn.shift] using hA.shift.wk
    have hm : Δ ⊢[PRAAx] le one (sh M) := by simpa [Δ,Fm.shift,sh,Syn.shift] using hM.shift.wk
    have hk : Δ ⊢[PRAAx] le one (one+i) := le_add_right _ _
    have nonneg := (panel_envelope m (num q) (sh A) (sh B) (sh M) (one+i) ha hm hk).andE₁
    have read := (offset_at (Γ := Δ) f one i (data (sh A) (sh B) (sh M))).eqTrans
      (panel_at m q (sh A) (sh B) (sh M) (one+i))
    rw [term_constant]
    simpa [Δ,f,x,z,sh,i,Syn.shift,one,termwiseLE,term_constant,term,data] using
      rationalLE_congr (.eqRefl _) read.eqSymm nonneg
  have rz := (sum_constant (Γ := Γ) N z (normalize_well_formed _ _ (le_refl one))).eqTrans
    ((multiply_commutative _ _).eqTrans (multiply_zero_right _))
  exact rationalLE_congr rz (.eqRefl _) (sum_monotone _ _ _ _ _ hrows)

theorem prefix_positive_lower (m q : ℕ) (A B S L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] le one S) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] rationalLE (panelFloor m (num q) A B) (panelPrefix m q A B (S*num 8) L) := by
  let M := S*num 8
  let f := GaussianStirlingAllOrderPanelPartsOuterFold.panelBody m q
  let x := data A B M
  let H := monus L one
  let t := sum (offB f) H (pairT one x)
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have count : Γ ⊢[PRAAx] L ≐ succ H :=
    (eq_add_of_le hL).eqTrans ((add_comm _ _).eqTrans (succ_eq_add_one H).eqSymm)
  have eq : Γ ⊢[PRAAx] panelPrefix m q A B M L ≐
      add (GaussianStirlingAllOrderPanelTail.panel m (num q) A B M zero) t :=
    (sum_congr f count (.eqRefl x)).eqTrans ((sum_first f H x).eqTrans
      (add_congr (panel_at m q A B M zero) (.eqRefl _)))
  have h := add_monotone _ _ _ _ (first_panel_positive_lower m (num q) A B S hA hB hS)
    (suffix_nonnegative m q A B M H hA hM)
  have canon : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (panelFloor m (num q) A B) :=
    normalize_well_formed _ _ (panel_floor_den_positive m (num q) A B hA)
  exact rationalLE_congr (add_zero_right _ canon) eq.eqSymm h

theorem actual_original_reciprocal_positive_prefix_lower_closed (m q : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 0) ⋏ (le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 3)))) ⟶
        rationalLE (panelFloor m (num q) (var 0) (var 1)) (panelPrefix m q (var 0) (var 1) (var 2*num 8) (var 3))) :=
  closeUniv 4 (.impI (prefix_positive_lower m q _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPositivePrefix
