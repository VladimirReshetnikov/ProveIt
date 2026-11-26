import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinPoweredWindow
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinFiniteDampedGrid
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinFiniteDampedModulus
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerCofinalQuadrature

/-!
# The finite product approximation on the original powered compact name

Refine the original compact sampler by the scheduled damped mesh.
Both compact and damped precision requirements are met by one later
observation. Removing the compact approximation slack gives an
independent rate to the original Gamma times finite Dirichlet name.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinPoweredCompactProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (name_at precision)
open GaussianFastValueCut (exponent)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianGammaZetaMellinDampedWindow (cutoff clock)
open GaussianGammaZetaMellinDampedWindowSchedule (gainBudget mesh mesh_positive)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF budget)
open GaussianGammaZetaMellinFiniteDampedModulus (lipschitz original_sampled_modulus)
open GaussianGammaZetaMellinPoweredWindow (outerCutoff scheduled_product_error)
open GaussianNameEquivalence (point_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "GammaSource" => GaussianEulerIntegralGammaIdentification.source
local notation "productF" => GaussianGammaZetaMellinDampedImproper.gammaProductF
local notation "productData" => GaussianGammaZetaMellinDampedImproper.gammaProductData
local notation "finiteData" => GaussianGammaZetaMellinFiniteDampedEvaluator.data

abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF

def panelCutoff (p i N z R B A J S : PTm n) : PTm n :=
  outerCutoff i N (cutoff p N (gainBudget N z R B A)) A R J S

def data (p i N z R B A J S : PTm n) : PTm n :=
  let q := panelCutoff p i N z R B A J S
  let E := etaDen q J S
  let T := top q J S
  GaussianCompactRiemannName.data one (width q J S) E (lipschitz N R E T) T (finiteData z B N (budget R E T N))

private theorem subst_etaDen {m : ℕ} (σ : Fin n → PTm m) (q J S : PTm n) :
    Syn.subst σ (etaDen q J S) = etaDen (Syn.subst σ q) (Syn.subst σ J) (Syn.subst σ S) := by
  simp [etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
private theorem subst_top {m : ℕ} (σ : Fin n → PTm m) (q J S : PTm n) :
    Syn.subst σ (top q J S) = top (Syn.subst σ q) (Syn.subst σ J) (Syn.subst σ S) := by
  simp [top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p i N z R B A J S : PTm n) :
    Syn.subst σ (data p i N z R B A J S) =
      data (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
        (Syn.subst σ A) (Syn.subst σ J) (Syn.subst σ S) := by
  simp [data,panelCutoff,cutoff,subst_etaDen,subst_top,one]

theorem compact_input (p i N z R B A J S : PTm n) (hz : Γ ⊢[PRAAx] GammaSource z R B A) :
    let q := panelCutoff p i N z R B A J S
    let E := etaDen q J S
    let T := top q J S
    Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF one (width q J S) E (lipschitz N R E T) T (finiteData z B N (budget R E T N)) := by
  intro q E T
  let C := width q J S
  have src := (GaussianEulerIntegralGammaIdentification.improper_source z R B A hz).andE₁
  have hE : Γ ⊢[PRAAx] le one E := eta_den_positive _ _ _
  have topB : Γ ⊢[PRAAx] le (one+C) (E*T) :=
    le_congr (exact_right_endpoint q J S).eqSymm (.eqRefl _) (le_refl _)
  let Q := budget R E T N
  have hQ : Γ ⊢[PRAAx] le N Q := le_of_eq_add (d := N*GaussianGammaZetaMellinDampedPoint.cost R E T)
    (by unfold Q budget; ipra_ring)
  have h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B one C E T :=
    .andI (.andI src.andE₁ (.andI hE src.andE₂)) (.andI (le_refl one) topB)
  exact .andI (le_refl one) (.andI hE (.andI (le_trans (le_add_left C one) topB)
    (original_sampled_modulus z R B N Q one C E T h hQ)))

private theorem product_slack (p r v t i N z R B A J S : PTm n) (hz : Γ ⊢[PRAAx] GammaSource z R B A)
    (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] slack (qsub (ap2 nameF r (data p i N z R B A J S)) (ap2 productF v (productData N z R B A)))
      (rateNumerator (num 10) (unit p) r v) (rateDenominator (unit p) r v) two t := by
  let q := panelCutoff p i N z R B A J S
  let E := etaDen q J S
  let C := width q J S
  let T := top q J S
  let L := lipschitz N R E T
  let Q := budget R E T N
  let x := finiteData z B N Q
  let rowCap := N*T
  let K := mesh p N R E rowCap
  let M := K*GaussianCompactRiemannName.mesh t L T
  let w := precision t T+clock p N rowCap
  let s := exponent Q w
  let U := unit p
  let V := unit r
  let W := unit v
  let X := unit t
  let y := ap2 nameF r (data p i N z R B A J S)
  let Z := ap2 productF v (productData N z R B A)
  let d := GaussianCompactRiemannName.quadrature evaluatorF w M one C E x
  have hK : Γ ⊢[PRAAx] le one K := mesh_positive _ _ _ _ _
  have hM : Γ ⊢[PRAAx] le K M :=
    le_congr (one_mul _) (mul_comm _ _)
      (mul_le_mul_right K (GaussianCompactRiemannName.mesh_positive t L T))
  have hw₁ : Γ ⊢[PRAAx] le (precision t T) w := le_add_right _ _
  have hw₂ : Γ ⊢[PRAAx] le (clock p N rowCap) s := le_trans (le_add_left _ _) (le_add_right _ _)
  have h := compact_input p i N z R B A J S hz
  have hV := unit_positive (Γ := Γ) r
  have hX := unit_positive (Γ := Γ) t
  have hW := unit_positive (Γ := Γ) v
  have hU := unit_positive (Γ := Γ) p
  have refineGrid := GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF t w K one C E L T x h hK hw₁
  have first := distance_congr (.eqRefl d) (name_at (Γ := Γ) evaluatorF t one C E L T x).eqSymm (.eqRefl _) (.eqRefl _) refineGrid
  have hD : Γ ⊢[PRAAx] le one (X*V) := positive_product _ _ hX hV
  have small := distance_radius_mono _ _ _ _ V (X*V) (unit_positive _) hD
    (mul_le_mul_right V (GaussianEulerLowerCofinalQuadrature.three_slack t) |>
      le_congr (by ipra_ring) (by ipra_ring)) first
  have regular := GaussianCompactRiemannName.name_regular evaluatorF one C E L T x h
  have between := point_at nameF (data p i N z R B A J S) t r regular
  have left : Γ ⊢[PRAAx] distanceBounded y d (X+two*V) (X*V) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_symmetric _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD small between))
  have read := GaussianGammaZetaMellinFiniteDampedGrid.strip_grid_agreement (Γ := Γ) w z B M N one C E Q
  have raw := scheduled_product_error p s v i N z R B A J S M hz hJ hM hw₂
  have hUW : Γ ⊢[PRAAx] le one (U*W) := positive_product _ _ hU hW
  have right : Γ ⊢[PRAAx] distanceBounded d Z (num 10*W+U) (U*W) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hUW) hUW
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold num; ipra_ring))
      (distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw)
  have total := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hD hUW left right
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    (by dsimp only [X,V,W,U]; unfold rateNumerator rateDenominator unit num; ipra_ring)
    (by dsimp only [X,V,W,U]; unfold rateDenominator unit; ipra_ring) total

theorem original_compact_product_observations (p r v i N z R B A J S : PTm n)
    (hz : Γ ⊢[PRAAx] GammaSource z R B A) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF r (data p i N z R B A J S)) (ap2 productF v (productData N z R B A))
      (rateNumerator (num 10) (unit p) r v) (rateDenominator (unit p) r v) := by
  let y := qsub (ap2 nameF r (data p i N z R B A J S)) (ap2 productF v (productData N z R B A))
  let U := rateNumerator (num 10) (unit p) r v
  let V := rateDenominator (unit p) r v
  let t := GaussianRationalSlackRemoval.precision y U V two
  exact slack_removal_at y U V two (denominator_positive (unit p) r v (unit_positive p))
    (product_slack p r v t i N z R B A J S hz hJ)

theorem original_compact_product_rate (p i N z R B A J S : PTm n)
    (hz : Γ ⊢[PRAAx] GammaSource z R B A) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    independentRate nameF productF (data p i N z R B A J S) (productData N z R B A) (num 10) (unit p) := by
  refine .allI (.allI ?_)
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hz' : Δ ⊢[PRAAx] GammaSource (sh z) (sh R) (sh B) (sh A) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hz.shift.shift
  have hJ' : Δ ⊢[PRAAx] le one (sh J) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hJ.shift.shift
  simpa only [independentRate,Δ,sh,Syn.shift,subst_data,GaussianCoefficientNameBounds.subst_unit,
    GaussianGammaZetaMellinDampedImproper.subst_gammaProductData,LeanProofs.IPRA.PTm.subst_num] using
    original_compact_product_observations (sh p) (var 1) (var 0) (sh i) (sh N) (sh z) (sh R) (sh B) (sh A) (sh J) (sh S)
      hz' hJ'

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinPoweredCompactProduct
