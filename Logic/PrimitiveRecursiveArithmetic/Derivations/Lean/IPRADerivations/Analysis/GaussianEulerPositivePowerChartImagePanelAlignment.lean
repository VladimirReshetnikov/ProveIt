import IPRADerivations.Analysis.GaussianEulerPositivePowerChartImageWeights

/-!
# Same corrected endpoints in the exact native lattice

The common-denominator endpoint panel and the native lattice have
exactly equal rational endpoints. Enclosure by either encoding yields
the corresponding native inequalities in the other encoding.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImagePanelAlignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartCorrectedImage (input imageNumerator imageDenominator)
open GaussianEulerPositivePowerChartImageCuts (data numeratorBody denominatorBody start count denominator)
open GaussianEulerPositivePowerChartImageLattice (absolute node_cleared absolute_below absolute_as_relative)
local notation "panelStart" => GaussianEulerPositivePowerChartCorrectedPanel.start
local notation "panelSpan" => GaussianEulerPositivePowerChartCorrectedPanel.span
local notation "panelDen" => GaussianEulerPositivePowerChartCorrectedPanel.denominator
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem node_clears_corrected (k i e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) :
    let x := data k e f d h Q S E T a C N
    Γ ⊢[PRAAx] absolute numeratorBody denominatorBody i N x J*imageDenominator k i e f d h Q S E T a C N ≐
      denominator N x J*imageNumerator k i e f d h Q S E T a C N := by
  dsimp only
  let x := data k e f d h Q S E T a C N
  let U := absolute numeratorBody denominatorBody i N x J
  let M := denominator N x J
  let A := imageNumerator k i e f d h Q S E T a C N
  let D := imageDenominator k i e f d h Q S E T a C N
  let v := GaussianEulerPositivePowerChartImageLattice.nodeIndex numeratorBody denominatorBody i N x J
  have hD := GaussianEulerPositivePowerChartImageCuts.denominator_at (Γ := Γ) k i e f d h Q S E T a C N
  have hN := GaussianEulerPositivePowerChartImageCuts.numerator_at (Γ := Γ) k i e f d h Q S E T a C N
  have atNode := node_cleared numeratorBody denominatorBody i N x J
    (GaussianEulerPositivePowerChartImageCuts.original_denominators k e f d h Q S E T a C N hs) hi
  have geom : Γ ⊢[PRAAx] U ≐ v := absolute_below _ _ i N x J hi
  exact ((mul_comm U D).eqTrans (congrMul hD.eqSymm geom)).eqTrans
    (atNode.eqTrans (congrMul (.eqRefl M) hN))

theorem same_endpoints (k e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) :
    let x := data k e f d h Q S E T a C N
    let M := denominator N x J
    let A := start N x J
    let K := count N x J
    let A' := panelStart k e f d h Q S E T a C N
    let K' := panelSpan k e f d h Q S E T a C N
    let M' := panelDen k e f d h Q S E T a C N
    Γ ⊢[PRAAx] (A*M' ≐ A'*M) ⋏ ((A+K)*M' ≐ (A'+K')*M) := by
  dsimp only
  let x := data k e f d h Q S E T a C N
  let M := denominator N x J
  let A := start N x J
  let K := count N x J
  let A' := panelStart k e f d h Q S E T a C N
  let K' := panelSpan k e f d h Q S E T a C N
  let M' := panelDen k e f d h Q S E T a C N
  let U := absolute numeratorBody denominatorBody N N x J
  let B₀ := imageNumerator k zero e f d h Q S E T a C N
  let B₁ := imageNumerator k N e f d h Q S E T a C N
  let D₀ := imageDenominator k zero e f d h Q S E T a C N
  let D₁ := imageDenominator k N e f d h Q S E T a C N
  have ha : Γ ⊢[PRAAx] A*D₀ ≐ M*B₀ :=
    node_clears_corrected k zero e f d h Q S E T a C N J hs (zero_le _)
  have hu : Γ ⊢[PRAAx] U*D₁ ≐ M*B₁ :=
    node_clears_corrected k N e f d h Q S E T a C N J hs (le_refl _)
  have atLast : Γ ⊢[PRAAx] A+K ≐ U :=
    absolute_as_relative numeratorBody denominatorBody N N x J
      (GaussianEulerPositivePowerChartImageCuts.original_denominators k e f d h Q S E T a C N hs)
      (GaussianEulerPositivePowerChartImageCuts.original_ordered k e f d h Q S E T a C N hs) (le_refl _)
  have atPanelLast : Γ ⊢[PRAAx] A'+K' ≐ B₁*D₀ :=
    GaussianEulerPositivePowerChartCorrectedPanel.endpoint_identity k e f d h Q S E T a C N hs.andE₁
  have firstCleared : Γ ⊢[PRAAx] A*M' ≐ (A*D₀)*D₁ := by
    change Γ ⊢[PRAAx] A*(D₀*D₁) ≐ (A*D₀)*D₁
    ipra_ring
  have firstRestore : Γ ⊢[PRAAx] (M*B₀)*D₁ ≐ A'*M := by
    change Γ ⊢[PRAAx] (M*B₀)*D₁ ≐ (B₀*D₁)*M
    ipra_ring
  have first : Γ ⊢[PRAAx] A*M' ≐ A'*M :=
    firstCleared.eqTrans ((congrMul ha (.eqRefl D₁)).eqTrans firstRestore)
  have lastCleared : Γ ⊢[PRAAx] U*M' ≐ (U*D₁)*D₀ := by
    change Γ ⊢[PRAAx] U*(D₀*D₁) ≐ (U*D₁)*D₀
    ipra_ring
  have last : Γ ⊢[PRAAx] (A+K)*M' ≐ (A'+K')*M :=
    (congrMul atLast (.eqRefl M')).eqTrans
      (lastCleared.eqTrans
        ((congrMul hu (.eqRefl D₀)).eqTrans
          ((by ipra_ring : Γ ⊢[PRAAx] (M*B₁)*D₀ ≐ (B₁*D₀)*M).eqTrans
            (congrMul atPanelLast.eqSymm (.eqRefl M)))))
  exact .andI first last

theorem lattice_containment (k e f d h Q S E T a C N J V W : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N)
    (hl : Γ ⊢[PRAAx] le (panelStart k e f d h Q S E T a C N*V) (panelDen k e f d h Q S E T a C N))
    (hr : Γ ⊢[PRAAx] le (W*panelDen k e f d h Q S E T a C N)
      (panelStart k e f d h Q S E T a C N+panelSpan k e f d h Q S E T a C N)) :
    let x := data k e f d h Q S E T a C N
    let A := start N x J
    let K := count N x J
    let M := denominator N x J
    Γ ⊢[PRAAx] le (A*V) M ⋏ le (W*M) (A+K) := by
  dsimp only
  let x := data k e f d h Q S E T a C N
  let A := start N x J
  let K := count N x J
  let M := denominator N x J
  let B := panelStart k e f d h Q S E T a C N
  let D := panelDen k e f d h Q S E T a C N
  let H := B+panelSpan k e f d h Q S E T a C N
  have same := same_endpoints k e f d h Q S E T a C N J hs
  have pos : Γ ⊢[PRAAx] le one D :=
    (GaussianEulerPositivePowerChartCorrectedPanel.panel_geometry k e f d h Q S E T a C N hs).andE₁.andE₂
  have lefteq : Γ ⊢[PRAAx] (B*V)*M ≐ D*(A*V) :=
    (by ipra_ring : Γ ⊢[PRAAx] (B*V)*M ≐ (B*M)*V).eqTrans
      ((congrMul same.andE₁.eqSymm (.eqRefl V)).eqTrans (by ipra_ring))
  have righteq : Γ ⊢[PRAAx] H*M ≐ D*(A+K) :=
    same.andE₂.eqSymm.eqTrans (mul_comm _ _)
  exact .andI
    (RationalValueBounds.positive_cancel pos (le_congr lefteq (.eqRefl _) (mul_le_mul_right M hl)))
    (RationalValueBounds.positive_cancel pos (le_congr (by ipra_ring) righteq (mul_le_mul_right M hr)))

theorem actual_native_lattice_contains_corrected_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
    (let x := data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
        (var 9) (var 10) (var 11)
      let A := start (var 11) x (var 12)
      let K := count (var 11) x (var 12)
      let M := denominator (var 11) x (var 12)
      let B := panelStart (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
        (var 9) (var 10) (var 11)
      let H := B+panelSpan (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
        (var 9) (var 10) (var 11)
      let D := panelDen (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
        (var 9) (var 10) (var 11)
      (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⋏
        (le (B*var 13) D ⋏ le (var 14*D) H)) ⟶ (le (A*var 13) M ⋏ le (var 14*M) (A+K))) :=
  closeUniv 15 (.impI (lattice_containment _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImagePanelAlignment
