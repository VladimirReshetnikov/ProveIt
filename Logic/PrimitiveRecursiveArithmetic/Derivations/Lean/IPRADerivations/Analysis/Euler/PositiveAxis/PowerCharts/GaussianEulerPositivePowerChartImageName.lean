import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartImageComparison
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence

/-!
# The exact corrected panel's ordinary compact name

Multiplying the native lattice denominator by the requested compact
mesh count makes its full lattice an exact refinement of that ordinary
grid. The comparison includes zero-length corrected panels.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartImageCuts (data numeratorBody denominatorBody cutF start count denominator)
open GaussianEulerPositivePowerChartImageLattice (cutData absolute)
open GaussianEulerPositivePowerChartImageRows (cost errorDenominator)
open GaussianEulerPositivePowerChartImageComparison (ordinary lattice_compact_source)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPositivePowerChart (majorant)
open GaussianEulerPowerScalingCorrectedQuadrature (source correctedSum)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (quadrature precision mesh name_at)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qzero positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def panelTop (Q S E T : PTm n) : PTm n := majorant Q S E T+one
def panelModulus (R h Q S E T : PTm n) : PTm n :=
  GaussianEulerCompactModulus.lipschitz R (reciprocalMargin h Q E T) (panelTop Q S E T)
def latticeFactor (s R h Q S E T : PTm n) : PTm n := mesh s (panelModulus R h Q S E T) (panelTop Q S E T)
def panelData (s k z R B e f d h Q S E T a C N : PTm n) : PTm n :=
  let x := data k e f d h Q S E T a C N
  let J := latticeFactor s R h Q S E T
  GaussianEulerPositivePowerChartImageCompactModulus.data (scaled z f) R (B*e)
    (start N x J) (count N x J) (denominator N x J) (reciprocalMargin h Q E T) (panelTop Q S E T)
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF
def observation (s k z R B e f d h Q S E T a C N : PTm n) : PTm n :=
  ap2 nameF s (panelData s k z R B e f d h Q S E T a C N)

private theorem absolute_multiplier (i N x J : PTm n) :
    Γ ⊢[PRAAx] absolute numeratorBody denominatorBody i N x J ≐ J*absolute numeratorBody denominatorBody i N x one := by
  unfold absolute GaussianEulerPositivePowerChartImageLattice.nodeIndex GaussianEulerPositivePowerChartImageLattice.multiplier
  ipra_ring

theorem native_count_multiplier (k e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartCorrectedImage.input k e f d h Q S E T a C N) :
    let x := data k e f d h Q S E T a C N
    Γ ⊢[PRAAx] count N x J ≐ J*count N x one := by
  dsimp only
  let x := data k e f d h Q S E T a C N
  let A := start N x one
  let B := absolute numeratorBody denominatorBody N N x one
  let K := count N x one
  have hd := GaussianEulerPositivePowerChartImageCuts.original_denominators k e f d h Q S E T a C N hs
  have ho := GaussianEulerPositivePowerChartImageCuts.original_ordered k e f d h Q S E T a C N hs
  have native : Γ ⊢[PRAAx] A+K ≐ B :=
    GaussianEulerPositivePowerChartImageLattice.absolute_as_relative _ _ N N x one hd ho (le_refl N)
  have left : Γ ⊢[PRAAx] absolute numeratorBody denominatorBody N N x J ≐ J*A+J*K :=
    (absolute_multiplier N N x J).eqTrans ((congrMul (.eqRefl J) native.eqSymm).eqTrans (by ipra_ring))
  have right : Γ ⊢[PRAAx] start N x J ≐ J*A := absolute_multiplier zero N x J
  exact (GaussianEulerPositivePowerChartImageLattice.cut_at numeratorBody denominatorBody N N x J).eqTrans
    ((congrMonus left right).eqTrans (add_monus' (J*K) (J*A)))

private theorem zero_width (q K A M x : PTm n) (hM : Γ ⊢[PRAAx] le one M) (h0 : Γ ⊢[PRAAx] K ≐ zero)
    (N : PTm n) : Γ ⊢[PRAAx] quadrature evaluatorF q N A K M x ≐ qzero := by
  have move : Γ ⊢[PRAAx] quadrature evaluatorF q N A K M x ≐ quadrature evaluatorF q N A zero M x := by
    simpa using Prf.eqCongr1 (quadrature evaluatorF (Syn.shift q) (Syn.shift N) (Syn.shift A)
      (var 0) (Syn.shift M) (Syn.shift x)) h0
  exact move.eqTrans (GaussianCompactUniformGridComparison.zero_width_any_count evaluatorF q N A M x hM)

theorem original_lattice_to_compact_name (s q k z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N)
    (hq : Γ ⊢[PRAAx] le (precision s (panelTop Q S E T)) q) :
    let x := data k e f d h Q S E T a C N
    let J := latticeFactor s R h Q S E T
    Γ ⊢[PRAAx] distanceBounded (ordinary q (count N x J) k z B e f d h Q S E T a C N J)
      (observation s k z R B e f d h Q S E T a C N) (num 3) (unit (s+num 6)) := by
  dsimp only
  let x := data k e f d h Q S E T a C N
  let X := fixedData (scaled z f) (B*e)
  let U := panelTop Q S E T
  let L := panelModulus R h Q S E T
  let J := latticeFactor s R h Q S E T
  let K := count N x J
  let K₀ := count N x one
  let A := start N x J
  let M := denominator N x J
  let G := reciprocalMargin h Q E T
  have hJ : Γ ⊢[PRAAx] le one J := GaussianCompactRiemannName.mesh_positive s L U
  have hc := lattice_compact_source k z R B e f d h Q S E T a C N J hs hJ
  have hM : Γ ⊢[PRAAx] le one M := hc.andE₂.andE₁.andE₂
  have count_eq : Γ ⊢[PRAAx] K ≐ K₀*J :=
    (native_count_multiplier k e f d h Q S E T a C N J hs.andE₂).eqTrans (mul_comm J K₀)
  have bound := GaussianEulerPositivePowerChartImageCompactModulus.compact_input (scaled z f) R (B*e) A K M G U hc
  have read : Γ ⊢[PRAAx] observation s k z R B e f d h Q S E T a C N ≐
      GaussianCompactRiemannName.sample evaluatorF s A K M L U X :=
    name_at evaluatorF s A K M L U X
  refine .orE (zero_or_succ K₀) ?_ ?_
  · have empty : ((K₀ ≐ zero) :: Γ) ⊢[PRAAx] K ≐ zero :=
      count_eq.wk.eqTrans ((congrMul Prf.hyp0 (.eqRefl J)).eqTrans (zero_mul J))
    have l := zero_width q K A M X hM.wk empty K
    have r := read.wk.eqTrans (zero_width (precision s U) K A M X hM.wk empty J)
    have hu : ((K₀ ≐ zero) :: Γ) ⊢[PRAAx] le one (unit (s+num 6)) := unit_positive _
    exact distance_congr l.eqSymm r.eqSymm (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ zero _ (num 3) _ hu hu (le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _))
        (GaussianRationalPowerDifference.distance_refl_zero qzero _ hu))
  · have hK : ((K₀ ≐ succ (pred K₀)) :: Γ) ⊢[PRAAx] le one K₀ :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have coarse := GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF s q K₀ A K M L U X bound.wk hK hq.wk
    have l := GaussianCompactRiemannName.quadrature_index_congr
      (Γ := (K₀ ≐ succ (pred K₀)) :: Γ) evaluatorF q K (K₀*J) A K M X count_eq.wk
    exact distance_congr l.eqSymm read.wk.eqSymm (.eqRefl _) (.eqRefl _) coarse

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageName
