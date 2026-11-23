import IPRADerivations.Analysis.GaussianBetaSharpCofinalSchedule
import IPRADerivations.Analysis.GaussianBetaSharpPieceAlignment
import IPRADerivations.Analysis.GaussianEulerSharpResidualAssembly
import IPRADerivations.Analysis.GaussianRationalSlackRemoval

/-!
# Sharp finite Euler estimate for the original samplers

The low and middle panels contribute the literal coefficient C_R/N.
The contiguous tail contributes one D_R times the original decay
observation at N/4. An explicit finite precision removes the mesh and
auxiliary allowances. The two requested output observations and the
requested decay observation keep their own precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpFiniteRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaSharpFiniteBinding (fullBeta fullEuler)
open GaussianBetaSharpCofinalSchedule (source cutoff factor)
open GaussianBetaSharpPartition (lowWidth middleWidth)
open GaussianBetaSharpPieceAlignment (low middle tail)
open GaussianBetaSharpAlignedThreeSplit (threePieces)
open GaussianBetaContiguousUpperTailBudget (fixedNumerator fixedDenominator fixed_denominator_positive)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianMonomialDecayQuadrature (cap)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finitePoint (q z R B A N : PTm n) : PTm n := ap2 eulerF q (eulerData z R B A N)
def improperPoint (v z R B A : PTm n) : PTm n :=
  ap2 GaussianEulerImproperName.nameF v (GaussianEulerImproperName.data z R B A)
def numerator (q v q0 R N : PTm n) : PTm n :=
  GaussianEulerSharpResidualAssembly.boundNumerator
    (GaussianEulerSharpDegreeSchedule.coefficient R*fixedDenominator q0 N+fixedNumerator q0 R N*N)
    (N*fixedDenominator q0 N) (unit q) (unit v)
def denominator (q v q0 N : PTm n) : PTm n :=
  GaussianEulerSharpResidualAssembly.boundDenominator (N*fixedDenominator q0 N) (unit q) (unit v)

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

/-- Every working precision has a concrete common mesh and sample clock
satisfying the original three panel estimates and both sampler bindings. -/
theorem cofinal_observations (t q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z R B A N) (improperPoint v z R B A)
      (numerator q v q0 R N*unit t+num 12*denominator q v q0 N) (denominator q v q0 N*unit t) := by
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
  have hPart := GaussianBetaSharpCofinalSchedule.original_partition t z R B A N h
  have hCut := GaussianBetaSharpCofinalSchedule.cutoff_bounds (Γ := Γ) t A R N
  have hN := GaussianBetaFiniteEulerComparison.degree_positive z R B A N h
  have hE := eta_den_positive (Γ := Γ) k A R
  have hK := GaussianBetaSharpCofinalSchedule.factor_positive (Γ := Γ) t H z R B A N (le_refl H)
  have hm := GaussianBetaSharpCofinalSchedule.mesh_budgets (Γ := Γ) t H z R B A N (le_refl H)
  have hp := GaussianBetaSharpCofinalSchedule.precision_budgets (Γ := Γ) p t H z R B A N (le_refl p)
  have ht := GaussianBetaSharpCofinalSchedule.finite_binding_time_budget (Γ := Γ) p t H z R B A N (le_refl p)
  have hU := unit_positive (Γ := Γ) t
  have hTail := fixed_denominator_positive (Γ := Γ) q0 N
  have loRaw := GaussianBetaLowDyadicBudget.original_sharp_low_dyadic_bound p p t (lowWidth k A R*K) k z R B A N
    hLower (GaussianBetaSharpCofinalSchedule.low_count_positive t H z R B A N h (le_refl H))
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
      (GaussianBetaSharpCofinalSchedule.middle_time_budget p t H z R B A N h (le_refl p))) midRaw
  have tailRaw := GaussianBetaContiguousUpperTailBudget.original_cofinal_bound t p r q0 k A K z R B N (top k A R)
    (GaussianBetaSharpCofinalSchedule.tail_source t H z R B A N h (le_refl H))
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
  have grid := GaussianEulerSharpResidualAssembly.split_distance (fullBeta p k A R K z B N)
    (threePieces F p k A R N K x) (threePieces G p k A R N K y) (fullEuler p k A R K z B)
    _ _ _ bd hU betaSplit panels eulerSplit
  have finite := GaussianBetaSharpFiniteBinding.original_finite_euler t p q k z R B A N K
    h hCut.andE₂.andE₂ hK hCut.andE₂.andE₁
    (GaussianBetaSharpCofinalSchedule.support_cells t H z R B A N h (le_refl H))
    hp.andE₂.andE₁ ht
  have improper := GaussianBetaSharpFiniteBinding.original_improper_euler t p v k z R B A H
    (.andI hDisk hLower) hm.andE₁ hCut.andE₁ hp.andE₂.andE₂.andE₁
  exact GaussianEulerSharpResidualAssembly.sampler_distance
    (finitePoint q z R B A N) (fullBeta p k A R K z B N) (fullEuler p k A R K z B) (improperPoint v z R B A)
    _ _ _ _ _ bd (unit_positive q) (unit_positive v) hU finite grid improper

/-- The original finite Euler name and the original improper Euler name satisfy
the sharp two-term rate. The decay-name error is one D_R times its requested
observation tolerance, while the two output queries have their own tolerances. -/
theorem original_sharp_bound (q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z R B A N) (improperPoint v z R B A)
      (numerator q v q0 R N) (denominator q v q0 N) := by
  let diff := qsub (finitePoint q z R B A N) (improperPoint v z R B A)
  let X := numerator q v q0 R N
  let Y := denominator q v q0 N
  let t := GaussianRationalSlackRemoval.precision diff X Y (num 12)
  have hN := GaussianBetaFiniteEulerComparison.degree_positive z R B A N h
  have hY : Γ ⊢[PRAAx] le one Y :=
    positive_product _ _ (positive_product _ _ hN (fixed_denominator_positive q0 N))
      (positive_product _ _ (unit_positive q) (unit_positive v))
  exact GaussianRationalSlackRemoval.slack_removal_at diff X Y (num 12) hY
    (cofinal_observations t q v q0 z R B A N h)

theorem actual_finite_Euler_sharp_rate_to_original_improper_integral_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (finitePoint (var 0) (var 3) (var 4) (var 5) (var 6) (var 7))
          (improperPoint (var 1) (var 3) (var 4) (var 5) (var 6))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 7))
          (denominator (var 0) (var 1) (var 2) (var 7))) :=
  closeUniv 8 (.impI (original_sharp_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpFiniteRate
