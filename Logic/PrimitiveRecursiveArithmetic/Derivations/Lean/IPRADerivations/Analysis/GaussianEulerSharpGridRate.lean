import IPRADerivations.Analysis.GaussianBetaSharpNaturalDegreeSchedule
import IPRADerivations.Analysis.GaussianBetaSharpPieceAlignment
import IPRADerivations.Analysis.GaussianEulerSharpResidualAssembly

/-!
# Sharp comparison of the full shared Euler grids

The original low, middle and upper grid estimates need only a positive
half-plane margin and degree at least two. The six working allowances
cover the three panel comparisons and both shared-grid splits.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpGridRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaSharpFiniteBinding (fullBeta fullEuler)
open GaussianBetaSharpCofinalSchedule (cutoff factor)
open GaussianBetaSharpNaturalDegreeSchedule (source)
open GaussianBetaSharpPartition (lowWidth middleWidth)
open GaussianBetaSharpPieceAlignment (low middle tail)
open GaussianBetaSharpAlignedThreeSplit (threePieces)
open GaussianBetaContiguousUpperTailBudget (fixedNumerator fixedDenominator fixed_denominator_positive)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianMonomialDecayQuadrature (cap)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem middle_comparison (R C E N p t : PTm n)
    (h : Γ ⊢[PRAAx] le (two*C*unit t) (E*unit p)) : Γ ⊢[PRAAx]
    le (GaussianBetaMiddleDyadicBudget.numerator p p t R C E N*(N*unit t))
      ((cap (R+two)*unit t+two*N)*GaussianBetaMiddleDyadicBudget.denominator p p t E N) := by
  let U := unit t
  let P := unit p
  have grow := mul_le_mul_right (N*N*P*U) h
  have sum := add_le_add_right (cap (R+two)*E*N*P*P*U*U+E*N*N*P*P*U) grow
  exact le_congr (by unfold GaussianBetaMiddleDyadicBudget.numerator; ipra_ring)
    (by unfold GaussianBetaMiddleDyadicBudget.denominator; ipra_ring) sum

private theorem rescale_split (x y p t k A R : PTm n)
    (h : Γ ⊢[PRAAx] le (num 4*width k A R*unit t) (etaDen k A R*unit p))
    (split : Γ ⊢[PRAAx] distanceBounded x y (num 4*width k A R) (etaDen k A R*unit p)) :
    Γ ⊢[PRAAx] distanceBounded x y one (unit t) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (eta_den_positive k A R) (unit_positive p))
    (unit_positive t) (le_congr (.eqRefl _) (one_mul _).eqSymm h) split

def sampleClock (t z R B A N : PTm n) : PTm n :=
  GaussianBetaSharpCofinalSchedule.minimumPrecision t (GaussianBetaSharpCofinalSchedule.minimumH t z R B A N) z R B A N
def mesh (t z R B A N : PTm n) : PTm n :=
  factor t (GaussianBetaSharpCofinalSchedule.minimumH t z R B A N) A R N
def mainNumerator (q0 R N : PTm n) : PTm n :=
  GaussianEulerSharpDegreeSchedule.coefficient R*fixedDenominator q0 N+fixedNumerator q0 R N*N
def mainDenominator (q0 N : PTm n) : PTm n := N*fixedDenominator q0 N

theorem original_grids (t q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (fullBeta (sampleClock t z R B A N) (cutoff t A N) A R (mesh t z R B A N) z B N)
      (fullEuler (sampleClock t z R B A N) (cutoff t A N) A R (mesh t z R B A N) z B)
      (mainNumerator q0 R N*unit t+num 6*mainDenominator q0 N) (mainDenominator q0 N*unit t) := by
  let k := cutoff t A N
  let H := GaussianBetaSharpCofinalSchedule.minimumH t z R B A N
  let K := factor t H A R N
  let p := GaussianBetaSharpCofinalSchedule.minimumPrecision t H z R B A N
  let w := GaussianBetaSharpCofinalSchedule.minimumMiddleQuery t A R N
  let r := GaussianBetaSharpCofinalSchedule.minimumTailQuery t R
  let E := etaDen k A R
  let C := middleWidth k A R N
  let F := GaussianBetaZeroExtension.evaluatorF
  let G := GaussianEulerIntegrandName.evaluatorF
  let x := GaussianBetaKernelGridComparison.sampleDataBeta z B N
  let y := GaussianEulerIntegrandName.fixedData z B
  have hLower := h.andE₁
  have hDisk : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B := hLower.andE₂.andE₁
  have hPart := GaussianBetaSharpNaturalDegreeSchedule.original_partition t z R B A N h
  have hN := le_trans (le_succ_self one) h.andE₂
  have hE := eta_den_positive (Γ := Γ) k A R
  have hK := GaussianBetaSharpCofinalSchedule.factor_positive (Γ := Γ) t H z R B A N (le_refl H)
  have hm := GaussianBetaSharpCofinalSchedule.mesh_budgets (Γ := Γ) t H z R B A N (le_refl H)
  have hp := GaussianBetaSharpCofinalSchedule.precision_budgets (Γ := Γ) p t H z R B A N (le_refl p)
  have hU := unit_positive (Γ := Γ) t
  have hTail := fixed_denominator_positive (Γ := Γ) q0 N
  have loRaw := GaussianBetaLowDyadicBudget.original_sharp_low_dyadic_bound p p t (lowWidth k A R*K) k z R B A N
    hLower (GaussianBetaSharpNaturalDegreeSchedule.low_count_positive t H z R B A N h (le_refl H))
    hPart.andE₂.andE₁ hp.andE₁ hp.andE₁
  have lo : Γ ⊢[PRAAx] distanceBounded (low F p k A R N K x) (low G p k A R N K y)
      (unit t+N) (N*unit t) :=
    distance_congr (GaussianBetaSharpPieceAlignment.low_supported p k A R N K z B hPart).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) loRaw
  have midRaw := GaussianBetaSharpPieceAlignment.original_middle_bound p p t w k A R N K z B
    hDisk hPart hm.andE₂.andE₂.andE₁ (le_refl w)
  have mid := distance_radius_mono _ _ _ _ _ _
    (GaussianBetaMiddleDyadicBudget.denominator_positive p p t E N hE hN) (positive_product _ _ hN hU)
    (middle_comparison R C E N p t
      (GaussianBetaSharpNaturalDegreeSchedule.middle_time_budget p t H z R B A N h (le_refl p))) midRaw
  have tailRaw := GaussianBetaContiguousUpperTailBudget.original_cofinal_bound t p r q0 k A K z R B N (top k A R)
    (GaussianBetaSharpNaturalDegreeSchedule.tail_source t H z R B A N h (le_refl H))
    hm.andE₂.andE₂.andE₂ hp.andE₂.andE₂.andE₂.andE₁ (le_refl r)
  have upper : Γ ⊢[PRAAx] distanceBounded (tail F p k A R N K x) (tail G p k A R N K y)
      (fixedNumerator q0 R N*unit t+fixedDenominator q0 N) (fixedDenominator q0 N*unit t) :=
    distance_congr (GaussianBetaSharpPieceAlignment.tail_beta_alignment p k A R N K z B hPart).eqSymm
      (GaussianBetaSharpPieceAlignment.tail_euler_alignment p k A R N K z B hPart).eqSymm
      (.eqRefl _) (.eqRefl _) tailRaw
  have panels := GaussianEulerSharpResidualAssembly.panel_distance
    (low F p k A R N K x) (low G p k A R N K y) (middle F p k A R N K x) (middle G p k A R N K y)
    (tail F p k A R N K x) (tail G p k A R N K y) _ _ _ _ _ hN hTail hU lo mid upper
  have betaRaw := GaussianBetaSharpAlignedThreeSplit.original_aligned_three_piece_split F k A R N K p x
    (.andI hPart (.andI hK (GaussianBetaZeroExtensionAligned.original_aligned_samples z R B E N (width k A R)
      (.andI hDisk.andE₁ (.andI hE hDisk.andE₂)) hN)))
  have budget := GaussianBetaSharpCofinalSchedule.split_time_budget (Γ := Γ) p t H z R B A N (le_refl p)
  have betaSplit := rescale_split _ _ p t k A R budget betaRaw
  have eulerSplit := rescale_split _ _ p t k A R budget
    (GaussianBetaSharpAlignedThreeSplit.original_Euler_three_piece_split k A R N K p z B hDisk hPart hK)
  have bd := positive_product _ _ hN hTail
  exact GaussianEulerSharpResidualAssembly.split_distance (fullBeta p k A R K z B N)
    (threePieces F p k A R N K x) (threePieces G p k A R N K y) (fullEuler p k A R K z B)
    _ _ _ bd hU betaSplit panels eulerSplit

end LeanProofs.IPRA.Analysis.GaussianEulerSharpGridRate
