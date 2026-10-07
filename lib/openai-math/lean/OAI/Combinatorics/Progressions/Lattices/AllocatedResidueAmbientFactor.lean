import OAI.Combinatorics.Progressions.Estimates.AllocatedMaskedFactorBounds

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

theorem exists_allocated_residue_ambient_factor
    (hR : ∀ j, 0 < R j) (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    let Lout := max (L * (K * ∑ j, Cforward j * Fintype.card (J j))) (2 * period)
    ∃ g : (RI → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ,
      LipschitzWith Lout g ∧ (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ w : MixedCoveredJetSource I single E n d, w ∈ region →
        g ((fun i => (((mixedCoveredSiteResidueIntegers d w i : ℝ) / period : ℝ) : UnitAddCircle)),
          coveredJetAmbientTorus U d (chart w)) =
          ((if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0) *
            f (allocatedFullMixedSiteValue (R := R) U b
              (fun j => mixedArrayRegroup _ _ _ ((Prod.fst w) j) ()))) / 4 := by
  intro Lout
  let F := f
  let decode := fun a : RI → ZMod period =>
    ((fun j i => a (.inl ⟨j,i⟩)), (fun j i => a (.inr ⟨j,i⟩)))
  let raw := fun a : RI → ZMod period => fun v : ambient → ℝ =>
    if decode a = label then F (allocatedFullAmbientSiteCoordinates (R := R) U b o v) else 0
  have hFl : LipschitzWith L F := hf
  have hFb : ∀ z, ‖F z‖ ≤ 1 := hf1
  have hraw (a) : LipschitzWith (L * (K * ∑ j, Cforward j * Fintype.card (J j))) (raw a) := by
    dsimp only [raw]
    split_ifs
    · exact hFl.comp (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR Cforward hforward K hK)
    · apply LipschitzWith.of_dist_le_mul
      intro v w
      simp only [dist_self]
      positivity
  have hrawb (a) (v) : ‖raw a v‖ ≤ 1 := by
    dsimp only [raw]
    split_ifs
    · exact hFb _
    · simp only [norm_zero, zero_le_one]
  obtain ⟨g₀, hg₀, hgb, hgv⟩ := exists_residue_quarter_extension (fun _ : RI => period)
    (period : ℝ≥0) (L * (K * ∑ j, Cforward j * Fintype.card (J j))) (fun _ => le_rfl) raw hraw hrawb
  refine ⟨fun z => g₀ z / 4, lipschitz_complex_div_four g₀ Lout hg₀,
    fun z => complex_div_four_norm_le (hgb z), ?_⟩
  intro w hw
  rw [coveredJetAmbientTorus_chart U b hb o bW d w]
  have hsmall : ∀ i, |mixedJetAmbientPoint U b o w.1 i| ≤ 1 / 4 := by
    rintro ⟨j, t, i⟩
    exact (hw j (mem_univ j) t (mem_univ t)).1 i
  have hv := hgv (fun i => (mixedCoveredSiteResidueIntegers d w i : ZMod period))
    (mixedJetAmbientPoint U b o w.1) hsmall
  have hc : (residueTuplePoint (fun _ : RI => period)
      (fun i => (mixedCoveredSiteResidueIntegers d w i : ZMod period))) =
      (fun i => (((mixedCoveredSiteResidueIntegers d w i : ℝ) / period : ℝ) : UnitAddCircle)) := by
    funext i
    exact ZMod.toAddCircle_intCast _
  rw [hc] at hv
  dsimp only
  rw [hv]
  congr 1
  dsimp only [raw]
  rw [allocatedFullAmbientSiteCoordinates_point]
  have hdecode : decode (fun i => (mixedCoveredSiteResidueIntegers d w i : ZMod period)) =
      mixedCoveredSiteResidue d period w := by
    apply Prod.ext
    · rfl
    · funext j i
      exact Int.cast_natCast _
  rw [hdecode]
  change (if mixedCoveredSiteResidue d period w = label then F _ else 0) =
    (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0) * F _
  split_ifs <;> simp only [one_mul, zero_mul]

end Erdos3.VectorPolynomial

end

end OAI
