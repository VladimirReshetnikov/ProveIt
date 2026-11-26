import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactExhaustionScaled
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartImageName
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartImagePanelAlignment

/-!
# Euler exhaustion on the exact rational panel of the ordinary image name

The checked endpoint alignment gives cutoff containment in the lattice
used by the actual image sampler, at the requested mesh multiplier.
The native lattice geometry supplies the other guards for exhaustion.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionImageLattice

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartImageCuts (data start count denominator)
open GaussianEulerPositivePowerChartCorrectedImage (input)
open GaussianEulerPositivePowerChartImageName (latticeFactor panelTop)
open GaussianEulerPositivePowerChartImage (reciprocalMargin)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianGammaIntegralCutoffs (etaDen top)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "BaseStart" => GaussianEulerPositivePowerChartCorrectedPanel.start
local notation "BaseDen" => GaussianEulerPositivePowerChartCorrectedPanel.denominator
local notation "BaseSpan" => GaussianEulerPositivePowerChartCorrectedPanel.span

theorem original_lattice_exhaustion_source (r j k z R B A e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N)
    (hb : Γ ⊢[PRAAx] GaussianEulerCompactExhaustion.source z R B A j
      (BaseStart k e f d h Q S E T a C N) (BaseSpan k e f d h Q S E T a C N)
      (BaseDen k e f d h Q S E T a C N) (reciprocalMargin h Q E T) (panelTop Q S E T)) :
    let x := data k e f d h Q S E T a C N
    let J := latticeFactor r R h Q S E T
    Γ ⊢[PRAAx] GaussianEulerCompactExhaustion.source z R B A j
      (start N x J) (count N x J) (denominator N x J) (reciprocalMargin h Q E T) (panelTop Q S E T) := by
  dsimp only
  let J := latticeFactor r R h Q S E T
  have hJ : Γ ⊢[PRAAx] le one J := GaussianCompactRiemannName.mesh_positive r _ _
  have hg := GaussianEulerPositivePowerChartImageWeights.original_lattice_geometry k e f d h Q S E T a C N J hs hJ
  have contain := GaussianEulerPositivePowerChartImagePanelAlignment.lattice_containment k e f d h Q S E T a C N
    J (etaDen j A R) (top j A R) hs hb.andE₂.andE₂.andE₁ hb.andE₂.andE₂.andE₂
  exact .andI hb.andE₁ (.andI (.andI hb.andE₂.andE₁.andE₁ hg) contain)

theorem original_scaled_lattice_source (r j k z R B A e f d h L Q S E T a C N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerPowerScalingParameter.source z R B A e f L Q)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N)
    (hb : Γ ⊢[PRAAx] GaussianEulerCompactExhaustion.source (scaled z f) (L*R) (B*e) (Q*A) j
      (BaseStart k e f d h Q S E T a C N) (BaseSpan k e f d h Q S E T a C N)
      (BaseDen k e f d h Q S E T a C N) (reciprocalMargin h Q E T) (panelTop Q S E T)) :
    let x := data k e f d h Q S E T a C N
    let J := latticeFactor r (L*R) h Q S E T
    Γ ⊢[PRAAx] GaussianEulerCompactExhaustionScaled.source z R B A e f d h L Q j
      (start N x J) (count N x J) (denominator N x J) (reciprocalMargin h Q E T) (panelTop Q S E T) := by
  dsimp only
  have lc := original_lattice_exhaustion_source r j k (scaled z f) (L*R) (B*e) (Q*A) e f d h Q S E T a C N hs hb
  exact .andI hz (.andI hs.andE₁.andE₁.andE₂.andE₁ lc.andE₂)

end LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionImageLattice
