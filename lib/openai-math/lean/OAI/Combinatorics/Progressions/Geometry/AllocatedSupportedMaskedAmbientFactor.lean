import OAI.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff
import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueAmbientFactor

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J
local notation "RI" => MaskedSiteResidueIndex n E
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

theorem exists_allocated_supported_masked_ambient_factor
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lout := Lcut + max (L * Lcoord) (2 * period)
    ∃ g : (RI → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ,
      LipschitzWith Lout g ∧ (∀ z, ‖g z‖ ≤ 1) ∧
      (∀ z, (∃ i, 1 / 4 < ‖z.2 i‖) → g z = 0) ∧
      ∀ w : MixedCoveredJetSource I single E n d, w ∈ region →
        g ((fun i => (((mixedCoveredSiteResidueIntegers d w i : ℝ) / period : ℝ) : UnitAddCircle)),
          coveredJetAmbientTorus U d (chart w)) =
          allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f (chart w) / 4 := by
  intro Lcoord Lcut Lout
  let F := fun z => f (coordinateZeroProjection (allocatedGridAxis (I := I) U b S.value) z)
  have hF : LipschitzWith L F := by
    simpa only [F, Function.comp_def, mul_one] using hf.comp (coordinateZeroProjection_lipschitz (allocatedGridAxis (I := I) U b S.value))
  obtain ⟨g₀, hg₀, hgb, hgv⟩ := exists_allocated_residue_ambient_factor U b o hb bW d period
    hR Cforward hforward K hK label F hF (fun z => hf1 _)
  let χ := allocatedBufferedTorusCutoff (R := R) U b o r hr
  have hχ := allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget
  have hχL : LipschitzWith Lcut χ :=
    allocatedBufferedTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget Cforward hforward K hK
  have hχCL : LipschitzWith Lcut (fun z : (RI → UnitAddCircle) × (ambient → UnitAddCircle) => (χ z.2 : ℂ)) := by
    simpa only [one_mul, mul_one, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp (hχL.comp LipschitzWith.prod_snd)
  have hχb (z : (RI → UnitAddCircle) × (ambient → UnitAddCircle)) : ‖(χ z.2 : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ z.2).1]
    exact (hχ z.2).2
  refine ⟨fun z => (χ z.2 : ℂ) * g₀ z, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul, mul_one, add_comm] using
      lipschitz_mul_of_bounds _ _ hχCL hg₀ (Bf := 1) (Bg := 1) hχb hgb
  · intro z
    rw [norm_mul]
    exact (mul_le_mul (hχb z) (hgb z) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro z hz
    have hzero := allocatedBufferedTorusCutoff_zero_outside_quarter U b o r hr hR C hC hchart hbudget z.2 hz
    change (allocatedBufferedTorusCutoff U b o r hr z.2 : ℂ) * g₀ z = 0
    rw [hzero, Complex.ofReal_zero, zero_mul]
  · intro w hw
    dsimp only
    rw [hgv w hw, allocatedMaskedSiteChartFactor_normalized B U b S o hb bW d r hr period label f w hw]
    have hsmall : ∀ i, |mixedJetAmbientPoint U b o w.1 i| < 1 / 2 := by
      rintro ⟨j, t, i⟩
      exact ((hw j (mem_univ j) t (mem_univ t)).1 i).trans_lt (by norm_num)
    have hχv : χ (coveredJetAmbientTorus U d (chart w)) =
        normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
          (allocatedFullMixedSiteValue (R := R) U b
            (fun j => mixedArrayRegroup _ _ _ ((Prod.fst w) j) ())) := by
      dsimp only [χ]
      rw [coveredJetAmbientTorus_chart U b hb o bW d w,
        allocatedBufferedTorusCutoff_local U b o r hr hR C hC hchart hbudget _ hsmall]
      exact congrArg _ (allocatedFullAmbientSiteCoordinates_point U b o w.1)
    rw [hχv]
    dsimp only [F, bufferedCoordinateProjection]
    ring

end Erdos3.VectorPolynomial

end

end OAI
