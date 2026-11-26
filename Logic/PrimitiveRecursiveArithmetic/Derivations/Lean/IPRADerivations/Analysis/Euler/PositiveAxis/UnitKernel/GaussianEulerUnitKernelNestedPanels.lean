import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelPanelAdditivity
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelPanelRescaling
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelMarginIndependence
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelNativePanel
import IPRADerivations.Analysis.Integration.Partitions.RationalNestedPanelGeometry
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffAlignment

/-!
# Exact nested unit-quadrature splitting across rational denominators

The outside and inside original compact names keep their actual input
codes and may each use a different valid margin. The other two summands
are the actual ordinary compact quadratures on the two omitted strips,
at a common denominator. All three widths may be zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelNestedPanels

open_ipra
open GaussianEulerUnitKernelCompactName (nameF data name_regular)
open GaussianEulerUnitKernelPanelAdditivity (left_source right_source data_congr)
open GaussianEulerUnitKernelPanelRescaling (source_rescaling original_rescaling)
open GaussianEulerUnitKernelMarginIndependence (original_margin_invariance)
open GaussianEulerUnitKernelNativePanel (proper_from_source source_at_denominator)
open RationalNestedPanelGeometry (leftWidth rightWidth left_cut total_width)
open GaussianNameArithmetic (addF addData add_fast add_equivalent)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_trans cross_symm diagonal_refl)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev panelSource (z R B a C E G : PTm n) : Fm PTm n := GaussianEulerUnitKernelCompactName.source z R B a C E G

def source (z R B a C E G b D H J : PTm n) : Fm PTm n :=
  panelSource z R B a C E G ⋏ (panelSource z R B b D H J ⋏ RationalNestedPanelGeometry.source a C E b D H)
def commonDen (E H : PTm n) : PTm n := H*E
def rightStart (a E b D H : PTm n) : PTm n := (H*a+leftWidth a E b H)+E*D
def leftData (z R B a E b H : PTm n) : PTm n :=
  data z R B (H*a) (leftWidth a E b H) (commonDen E H) (commonDen E H)
def rightData (z R B a C E b D H : PTm n) : PTm n :=
  data z R B (rightStart a E b D H) (rightWidth a C E b D H) (commonDen E H) (commonDen E H)
def splitData (z R B a C E b D H J : PTm n) : PTm n :=
  addData (leftData z R B a E b H) (addData (data z R B b D H J) (rightData z R B a C E b D H))

private theorem source_congr (z R B a C E G a' C' E' : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hC : Γ ⊢[PRAAx] C ≐ C') (hE : Γ ⊢[PRAAx] E ≐ E')
    (h : Γ ⊢[PRAAx] panelSource z R B a C E G) : Γ ⊢[PRAAx] panelSource z R B a' C' E' G :=
  .andI h.andE₁ (.andI (le_congr (.eqRefl _) hE h.andE₂.andE₁)
    (.andI (le_congr hE (congrMul (.eqRefl _) ha) h.andE₂.andE₂.andE₁)
      (le_congr (congrAdd (congrMul (.eqRefl _) (congrAdd ha hC)) hE)
        (congrMul (.eqRefl _) hE) h.andE₂.andE₂.andE₂)))

private theorem data_den_congr (z R B a C E E' G : PTm n) (e : Γ ⊢[PRAAx] E ≐ E') :
    Γ ⊢[PRAAx] data z R B a C E G ≐ data z R B a C E' G :=
  congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT e (.eqRefl _)))

private theorem three_width (a C E b D H : PTm n) (h : Γ ⊢[PRAAx] RationalNestedPanelGeometry.source a C E b D H) :
    Γ ⊢[PRAAx] leftWidth a E b H+(E*D+rightWidth a C E b D H) ≐ H*C :=
  (add_assoc _ _ _).eqSymm.eqTrans (total_width a C E b D H h)

theorem common_outer_source (z R B a C E G b D H J : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G b D H J) :
    Γ ⊢[PRAAx] panelSource z R B (H*a) (leftWidth a E b H+(E*D+rightWidth a C E b D H)) (commonDen E H) (commonDen E H) := by
  have scaled := source_rescaling z R B a C E G H h.andE₁ h.andE₂.andE₁.andE₂.andE₁
  have proper := proper_from_source _ _ _ _ _ _ _ scaled
  have upper : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B :=
    .andI scaled.andE₁.andE₁ scaled.andE₁.andE₂.andE₂
  exact source_congr _ _ _ _ _ _ _ _ _ _ (.eqRefl _) (three_width a C E b D H h.andE₂.andE₂).eqSymm (.eqRefl _)
    (source_at_denominator _ _ _ _ _ _ upper proper)

theorem tail_sources (z R B a C E G b D H J : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G b D H J) :
    Γ ⊢[PRAAx] panelSource z R B (H*a) (leftWidth a E b H) (commonDen E H) (commonDen E H) ⋏
      panelSource z R B (rightStart a E b D H) (rightWidth a C E b D H) (commonDen E H) (commonDen E H) := by
  have outer := common_outer_source z R B a C E G b D H J h
  exact .andI (left_source _ _ _ _ _ _ _ _ outer) (right_source _ _ _ _ _ _ _ _ (right_source _ _ _ _ _ _ _ _ outer))

private theorem sum_middle_congr (F : PR 2) (x y v w : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN F y)
    (hv : Γ ⊢[PRAAx] pointCN F v) (hw : Γ ⊢[PRAAx] pointCN F w)
    (h : Γ ⊢[PRAAx] crossEquivalent F F y v) : Γ ⊢[PRAAx]
    crossEquivalent (addF F (addF F F)) (addF F (addF F F))
      (addData x (addData y w)) (addData x (addData v w)) := by
  have tail := add_equivalent F F F F y v w w hy hv hw hw
    (cross_to_diagonal _ _ _ _ h) (diagonal_refl _ _)
  exact add_equivalent F F (addF F F) (addF F F) x x (addData y w) (addData v w) hx hx
    (add_fast F F y w hy hw) (add_fast F F v w hv hw)
    (diagonal_refl _ _) (cross_to_diagonal _ _ _ _ tail)

theorem original_split (z R B a C E G b D H J : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G b D H J) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF nameF (addF nameF nameF)) (data z R B a C E G)
      (splitData z R B a C E b D H J) := by
  let M := commonDen E H
  let L := leftWidth a E b H
  let U := rightWidth a C E b D H
  let x := leftData z R B a E b H
  let y := data z R B (H*a+L) (E*D) M M
  let v := data z R B b D H J
  let w := rightData z R B a C E b D H
  have outer := common_outer_source z R B a C E G b D H J h
  have width := three_width a C E b D H h.andE₂.andE₂
  have hG := source_rescaling z R B a C E G H h.andE₁ h.andE₂.andE₁.andE₂.andE₁
  have hM := source_congr _ _ _ _ _ _ _ _ _ _ (.eqRefl _) width (.eqRefl _) outer
  have same := original_margin_invariance z R B (H*a) (H*C) M G M hG hM
  have original := original_rescaling z R B a C E G H h.andE₁ h.andE₂.andE₁.andE₂.andE₁
  have whole := cross_data_congr _ _ _ _ _ _ (.eqRefl _) (data_congr z R B (H*a) (H*C) (H*a) (L+(E*D+U))
    M M (.eqRefl _) width.eqSymm) (cross_trans _ _ _ _ _ _ original same)
  have pieces := GaussianEulerUnitKernelPanelAdditivity.original_three_split z R B (H*a) L (E*D) U M M outer
  have tail := right_source _ _ _ _ _ _ _ _ outer
  have mid := left_source _ _ _ _ _ _ _ _ tail
  have es := left_cut a C E b D H h.andE₂.andE₂
  have adjusted := source_congr _ _ _ _ _ _ _ _ _ _ es (.eqRefl _) (.eqRefl _) mid
  have hJ := source_rescaling z R B b D H J E h.andE₂.andE₁ h.andE₁.andE₂.andE₁
  have em : Γ ⊢[PRAAx] E*H ≐ M := mul_comm _ _
  have hJ' := source_congr _ _ _ _ _ _ _ _ _ _ (.eqRefl _) (.eqRefl _) em hJ
  have align := cross_data_congr _ _ _ _ _ _ (.eqRefl _) (data_den_congr z R B (E*b) (E*D) (E*H) M J em)
    (original_rescaling z R B b D H J E h.andE₂.andE₁ h.andE₁.andE₂.andE₁)
  have equivalent : Γ ⊢[PRAAx] crossEquivalent nameF nameF v y := cross_data_congr _ _ _ _ _ _ (.eqRefl _)
    (data_congr z R B (E*b) (E*D) (H*a+L) (E*D) M M es.eqSymm (.eqRefl _))
    (cross_trans _ _ _ _ _ _ align (original_margin_invariance z R B (E*b) (E*D) M J M hJ' adjusted))
  have hs := tail_sources z R B a C E G b D H J h
  have hx : Γ ⊢[PRAAx] pointCN nameF x := name_regular _ _ _ _ _ _ _ hs.andE₁
  have hw : Γ ⊢[PRAAx] pointCN nameF w := name_regular _ _ _ _ _ _ _ hs.andE₂
  have hy : Γ ⊢[PRAAx] pointCN nameF y := name_regular _ _ _ _ _ _ _ mid
  have hv : Γ ⊢[PRAAx] pointCN nameF v := name_regular _ _ _ _ _ _ _ h.andE₂.andE₁
  have sumEq := sum_middle_congr nameF x y v w hx hy hv hw (cross_symm _ _ _ _ equivalent)
  exact cross_trans _ _ _ _ _ _ whole (cross_trans _ _ _ _ _ _ pieces sumEq)

theorem actual_original_nested_unit_quadrature_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      crossEquivalent nameF (addF nameF (addF nameF nameF)) (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (splitData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 8) (var 9) (var 10))) :=
  closeUniv 11 (.impI (original_split _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelNestedPanels
