import OAI.Combinatorics.Progressions.Dynamics.AllocatedCommonCoarseBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedUniformPeriodSizes

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {p c P e Eraw Esite w v : ℝ}

local notation "cutoff" => allocatedRefinedPeriodCutoff m P
local notation "cutoffLog" => allocatedRefinedPeriodLog m P + 1
local notation "S" => allocatedCommonScale (G := G) B U b hR hσ p c P e Eraw
local notation "sourceParameter" => allocatedCommonRefinedSourceLog m p c P e Eraw Esite
local notation "scalarEnvelope" => canonicalScalarSourceEnvelope m cutoff
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter w v Esite
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter w v Esite
local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

theorem exists_original_common_period_sampling
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hEraw : 0 ≤ Eraw) (hEsite : 0 ≤ Esite)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hR1 : ∀ j, R j ≤ 1)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ witnesses : (q : AllocatedRefinedPeriodIndex m P) →
        (r : AllocatedPositiveResidue (dim := dim) B U b S (q.val : ℕ)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (q.val : ℕ) r.val,
      (∀ q r, allocatedActiveSiteBounds B U b S rowSets scalarEnvelope pointTolerance Λ
        sitePeriods (witnesses q r).expansion) ∧
      ∀ q r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
        B U b hR hσ S (q.val : ℕ) (witnesses q r) δ := by
  have hcutoffLog : 0 ≤ cutoffLog := by
    unfold allocatedRefinedPeriodLog
    positivity
  have hcutoff := (allocatedRefinedPeriodCutoff_bounds m hP).2
  obtain ⟨_, hpSource, _, _, _, _, _, hSourceLog, _, _, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hc hP he hEraw hEsite
  have hsize := allocatedCommonScale_cutoff_window (G := G) B U b hR hσ
    hdimSmall hp hc hP he hEraw
  have hblocks := allocatedUniformBlocks_spectrum_bound B rowSets
    (by simpa only [Fintype.card_fin] using hdimSmall) hBlocks
  have hgamma (a : activeAxes) : principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤
        LayerSamplerScale.value S :=
    principalProfileSize_le_natScale (hR _).le (hR1 _) _
      (LayerSamplerScale.value S) (LayerSamplerScale.positive S)
  exact exists_allocated_uniform_period_sampling_of_sizes B U b hR hσ S
    (fun q : AllocatedRefinedPeriodIndex m P => (q.val : ℕ)) cutoff sitePeriods
    hcutoffLog hcutoff hSourceLog hw hv hEsite hdimSmall
    (hvars.trans hpSource) (fun j => (hI j).trans hpSource) (fun j => (hn j).trans hpSource)
    (allocatedRefinedPeriodIndex_power m hP)
    (fun q => (Nat.mul_le_mul_left _ q.property).trans hsize)
    hgamma (fun _ => rfl) (fun a => hblocks (ig a.val))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem original_common_period_scale_upper
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hEraw : 0 ≤ Eraw) (hEsite : 0 ≤ Esite) (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c) :
    ((LayerSamplerScale.value S) : ℝ) ≤ Real.exp sourceParameter := by
  obtain ⟨_, _, _, _, _, _, _, _, hscale, _, _⟩ :=
    allocatedCommonRefinedSourceLog_bounds m hp hc hP he hEraw hEsite
  have hupper := allocatedCommonScale_upper (G := G) B U b hR hσ rows
    (by simpa only [Fintype.card_fin] using hdimSmall) (fun _ => Subtype.val_injective)
    hp hc hP he hEraw hvars hI hn hRi hσi
  exact hupper.trans (Real.exp_le_exp.mpr hscale)

end Erdos3.VectorPolynomial

end

end OAI
