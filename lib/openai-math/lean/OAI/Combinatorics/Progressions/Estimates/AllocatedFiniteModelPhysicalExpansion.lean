import OAI.Combinatorics.Progressions.Geometry.AllocatedSupportedMaskedAmbientFactor
import OAI.Combinatorics.Progressions.Sampling.AllocatedFiniteModelGridCover

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {O J : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_nsmul_output (d : ℕ) (y : EuclideanJetLayers U O) :
    coveredJetAmbientTorus U d y = d • coveredJetAmbientTorus U 1 y := by
  funext a
  simp [coveredJetAmbientTorus, quotientIntegerCover, map_nsmul]

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_mk (d : ℕ) (v : ∀ j, O j → euclideanSubspace (U j)) :
    coveredJetAmbientTorus U d (fun j t => QuotientAddGroup.mk (v j t)) =
      fun a => (((d : ℝ) * (v a.1 a.2.1).val a.2.2 : ℝ) : UnitAddCircle) := by
  funext a
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (quotientIntegerCover _ d (QuotientAddGroup.mk' _ (v a.1 a.2.1)))) a.2.2 = _
  rw [quotientIntegerCover_mk, euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk,
    euclideanSubspaceArrayEquiv_apply]
  rfl

theorem ambient_nsmul_lipschitz {A : Type*} [Fintype A] (d : ℕ) :
    LipschitzWith (d : ℝ≥0) (fun z : A → UnitAddCircle => d • z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, ← smul_sub]
  simpa only [dist_eq_norm, NNReal.coe_natCast] using (norm_nsmul_le (a := z - w) (n := d))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

noncomputable def rowsAmbientSite
    (s : Finset α)
    (z : JetAmbientIndex (fun j => {t : Finset α // t ∈ rowSets j}) J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle :=
  fun a => ∑ t, rowRestrictedSiteMatrix (rowSets a.1) s t • z ⟨a.1, t, a.2.2⟩

omit [Fintype α] in
theorem rowsAmbientSite_eq (s : Finset α) (d : ℕ)
    (y : EuclideanJetLayers U (fun j => {t : Finset α // t ∈ rowSets j})) :
    rowsAmbientSite rowSets s (coveredJetAmbientTorus U d y) =
      coveredJetAmbientTorus U d (coveredRowsSiteValue rowSets U y s) := by
  funext a
  simp only [rowsAmbientSite, coveredRowsSiteValue, coveredJetAmbientTorus,
    map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]

omit [Fintype α] in
theorem rowsAmbientSite_lipschitz (s : Finset α) :
    LipschitzWith (∑ j : Fin m, ((rowSets j).card : ℝ≥0))
      (rowsAmbientSite (J := J) rowSets s) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, t, i⟩
  have hterm (r : {t : Finset α // t ∈ rowSets j}) :
      dist (rowRestrictedSiteMatrix (rowSets j) s r • z ⟨j,r,i⟩)
        (rowRestrictedSiteMatrix (rowSets j) s r • w ⟨j,r,i⟩) ≤ dist z w := by
    simp only [rowRestrictedSiteMatrix, booleanReconstructionMatrix]
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨j,r,i⟩
    · simpa only [zero_zsmul, dist_self] using (dist_nonneg : 0 ≤ dist z w)
  have hc : ((rowSets j).card : ℝ≥0) ≤ ∑ j : Fin m, ((rowSets j).card : ℝ≥0) :=
    Finset.single_le_sum (f := fun j : Fin m => ((rowSets j).card : ℝ≥0))
      (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _r : {t : Finset α // t ∈ rowSets j}, dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun r _ => hterm r))
    _ = ((rowSets j).card : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

end Erdos3.VectorPolynomial

end

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

theorem exists_allocated_masked_cover_factor
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    ∃ g : ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith (max (L * (K * ∑ j, Cforward j * Fintype.card (J j)) * period) (4 * period)) g ∧
      (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ (u : ∀ j, euclideanSubspace (U j)) (y : EuclideanJetLayers U single),
        (∀ j, (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) = y j ()) →
        allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y =
          2 * (allocatedBufferedTorusCutoff (R := R) U b o r hr (coveredJetAmbientTorus U d y) : ℂ) *
            g (fun a => (((u a.1).val a.2 / period : ℝ) : UnitAddCircle)) := by
  classical
  let decode := fun a : ∀ j, Fin (n j) ⊕ E j → ZMod period =>
    ((fun j i => a j (.inl i)), (fun j i => a j (.inr i)))
  let F := fun a (v : (Σ j, J j) → ℝ) =>
    if decode a = label then
      f (coordinateZeroProjection (allocatedGridAxis (I := I) U b S.value)
        (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered v))) else 0
  let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
  have hFl (a) : LipschitzWith (L * Lcoord) (F a) := by
    dsimp only [F]
    split_ifs
    · simpa only [mul_one, one_mul, mul_assoc, Function.comp_def] using
        hf.comp ((coordinateZeroProjection_lipschitz (allocatedGridAxis (I := I) U b S.value)).comp
          ((allocatedFullAmbientSiteCoordinates_lipschitz U b o hR Cforward hforward K hK).comp
            singleSiteFromLayered_lipschitz))
    · apply LipschitzWith.of_dist_le_mul
      intro v w
      simp only [dist_self]
      positivity
  have hFb (a) (v) : ‖F a v‖ ≤ (1 : ℝ≥0) := by
    dsimp only [F]
    split_ifs
    · exact hf1 _
    · simp
  obtain ⟨g₀, hg₀, hgb, hgv⟩ := exists_layered_full_residue_covered_extension
    (fun j => euclideanSubspace (U j)) bW b hb period d hdiv F (L * Lcoord) 1 hFl hFb
  refine ⟨fun z => g₀ z / 2, ?_, ?_, ?_⟩
  · apply lipschitz_complex_div_two
    simpa only [mul_one] using hg₀
  · intro z
    apply complex_div_two_norm_le
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one, mul_one] using hgb z
  · intro u y hu
    have hcut := allocatedBufferedTorusCutoff_eq_siteChart U b o r hr hR C hC hchart hbudget B S hb bW d y
    by_cases hc : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y = 0
    · rw [allocatedMaskedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr period label f y hc,
        hcut, hc, mul_zero, zero_mul]
    have hy : y ∈ chart '' region := by
      by_contra hn
      exact hc (restrictedComplexChartDensity_zero _ _ _ _ hn)
    obtain ⟨w, hw, rfl⟩ := hy
    have hu' (j : Fin m) : (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ()), w.2 j ()) := hu j
    have hsmall (j : Fin m) (i : J j) :
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ())) i| ≤ 1 / 4 :=
      (hw j (mem_univ j) () (mem_univ ())).1 i
    have hv := hgv u (fun j => orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (w.1 j) ()))
      (fun j => w.2 j ()) hu' hsmall
    dsimp only [F] at hv
    rw [allocatedFullAmbientSiteCoordinates_layered_point (R := R) U b o
      (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())] at hv
    change g₀ _ = (if mixedCoveredSiteResidue d period w = label then
      f (coordinateZeroProjection (allocatedGridAxis (I := I) U b S.value)
        (allocatedFullMixedSiteValue (R := R) U b (fun j => mixedArrayRegroup _ _ _ (w.1 j) ()))) else 0) at hv
    dsimp only
    rw [hv, allocatedMaskedSiteChartFactor_normalized B U b S o hb bW d r hr period label f w hw]
    rw [hcut, allocatedBufferedSiteChartFactor,
      restrictedComplexChartDensity_apply _ _ _ _
        (mixedCoveredJetChart_injOn U o b hb bW d _
          (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hw]
    dsimp only [allocatedBufferedMixedSiteFactor, bufferedCoordinateProjection]
    simp only [Complex.ofReal_one]
    split_ifs <;> ring

end Erdos3.VectorPolynomial

end

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

theorem exists_allocated_masked_ambient_lift
    (hdiv : period ∣ d)
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
    let Lout := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    ∃ F : (ambient → UnitAddCircle) → ℂ,
      LipschitzWith Lout F ∧ (∀ z, ‖F z‖ ≤ 1) ∧
      ∀ y : EuclideanJetLayers U single,
        allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y =
          2 * F (coveredJetAmbientTorus U 1 y) := by
  intro Lcoord Lcut Lout
  obtain ⟨g, hg, hgb, hgv⟩ := exists_allocated_masked_cover_factor B U b S o hb bW d r hr period
    hdiv hR C hC hchart hbudget Cforward hforward K hK label f hf hf1
  let χ := allocatedBufferedTorusCutoff (R := R) U b o r hr
  have hχ := allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget
  have hχL : LipschitzWith Lcut χ :=
    allocatedBufferedTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget Cforward hforward K hK
  let e := fun z : ambient → UnitAddCircle => fun a : Σ j, J j => z ⟨a.1, (), a.2⟩
  have he : LipschitzWith 1 e := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro a
    simpa only [one_mul] using dist_le_pi_dist z w ⟨a.1, (), a.2⟩
  let F := fun z : ambient → UnitAddCircle =>
    (χ (d • z) : ℂ) * g ((d / period) • e z)
  have hχCL : LipschitzWith (Lcut * d) (fun z : ambient → UnitAddCircle => (χ (d • z) : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp
      (hχL.comp (ambient_nsmul_lipschitz d))
  have hgL : LipschitzWith (max (L * Lcoord * period) (4 * period) * (d / period : ℕ))
      (fun z : ambient → UnitAddCircle => g ((d / period) • e z)) := by
    simpa only [mul_one, Function.comp_def, Lcoord] using hg.comp ((ambient_nsmul_lipschitz (d / period)).comp he)
  have hχb (z : ambient → UnitAddCircle) : ‖(χ (d • z) : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
    exact (hχ _).2
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [one_mul, add_comm] using
      lipschitz_mul_of_bounds _ _ hχCL hgL hχb (Bf := 1) (Bg := 1) (fun z => hgb _)
  · intro z
    exact (norm_mul _ _).trans_le
      ((mul_le_mul (hχb z) (hgb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  · intro y
    choose v hv using fun j => QuotientAddGroup.mk'_surjective
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup (y j ())
    have hy : (fun j (_ : Unit) => QuotientAddGroup.mk (v j)) = y := by
      funext j t
      cases t
      exact hv j
    have hu (j) :
        (QuotientAddGroup.mk ((d : ℝ)⁻¹ • ((d : ℝ) • v j)) :
          euclideanSubspace (U j) ⧸
            (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) = y j () := by
      rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d)), one_smul]
      exact hv j
    have hz : coveredJetAmbientTorus U 1 y =
        fun a => ((v a.1).val a.2.2 : UnitAddCircle) := by
      rw [← hy, coveredJetAmbientTorus_mk]
      simp only [Nat.cast_one, one_mul]
    have hratio : (d : ℝ) / period = (d / period : ℕ) := by
      apply (div_eq_iff (Nat.cast_ne_zero.mpr (NeZero.ne period))).mpr
      exact_mod_cast (Nat.div_mul_cancel hdiv).symm
    have heq : (fun a : Σ j, J j => ((((d : ℝ) • v a.1).val a.2 / period : ℝ) : UnitAddCircle)) =
        (d / period) • e (coveredJetAmbientTorus U 1 y) := by
      rw [hz]
      funext a
      change (((d : ℝ) * (v a.1).val a.2 / period : ℝ) : UnitAddCircle) =
        (d / period) • ((v a.1).val a.2 : UnitAddCircle)
      rw [mul_div_right_comm, hratio]
      simpa only [nsmul_eq_mul] using (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := d / period) (x := (v a.1).val a.2))
    rw [hgv _ y hu, heq, coveredJetAmbientTorus_nsmul_output]
    dsimp only [F]
    ring

end Erdos3.VectorPolynomial

end

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

theorem exists_allocated_physical_masked_factor
    (hdiv : period ∣ d)
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
    let Lout := Lcut + max (L * Lcoord * period) (4 * period)
    ∃ g : (ambient → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith Lout g ∧ (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hm : ∀ j e, coefficients (p j) e ∈ U j) (t : X → ℝ),
        allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f
          (BooleanCubeKernel.physicalSingleSiteValue U d p hm t) =
          2 * g ((fun a => (eval t (p a.1) a.2.2 : UnitAddCircle)),
            (fun a => ((eval t (p a.1) a.2 / period : ℝ) : UnitAddCircle))) := by
  intro Lcoord Lcut Lout
  obtain ⟨g₀, hg₀, hgb, hgv⟩ := exists_allocated_masked_cover_factor B U b S o hb bW d r hr period
    hdiv hR C hC hchart hbudget Cforward hforward K hK label f hf hf1
  let χ := allocatedBufferedTorusCutoff (R := R) U b o r hr
  have hχ := allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget
  have hχL : LipschitzWith Lcut χ :=
    allocatedBufferedTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget Cforward hforward K hK
  have hχCL : LipschitzWith Lcut
      (fun z : (ambient → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle) => (χ z.1 : ℂ)) := by
    simpa only [one_mul, mul_one, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp (hχL.comp LipschitzWith.prod_fst)
  have hχb (z : (ambient → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) : ‖(χ z.1 : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ z.1).1]
    exact (hχ z.1).2
  refine ⟨fun z => (χ z.1 : ℂ) * g₀ z.2, ?_, ?_, ?_⟩
  · simpa only [one_mul, mul_one, add_comm, Function.comp_def] using
      lipschitz_mul_of_bounds _ _ hχCL (hg₀.comp LipschitzWith.prod_snd)
        (Bf := 1) (Bg := 1) hχb (fun z => hgb z.2)
  · intro z
    rw [norm_mul]
    exact (mul_le_mul (hχb z) (hgb z.2) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro X p hm t
    have h := hgv (BooleanCubeKernel.physicalEuclideanSitePoint U p hm t)
      (BooleanCubeKernel.physicalSingleSiteValue U d p hm t)
      (fun j => (BooleanCubeKernel.physicalSingleSiteValue_eq_mk U p hm d t j).symm)
    rw [BooleanCubeKernel.physicalSingleSiteValue_ambient] at h
    simpa only [BooleanCubeKernel.physicalEuclideanSitePoint_apply, χ, mul_assoc] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

theorem exists_allocated_physical_masked_expansion
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lout := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → Finset (Fin dim) →
        ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label k s, LipschitzWith Lout (g label k s)) ∧
      (∀ label k s z, ‖g label k s z‖ ≤ 1) ∧
      ∀ {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
        (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
        allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
          (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
          ∑ label, ∑ k, ((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k) *
              ∏ s, g label k s
                ((fun a => (eval (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)) (p a.1) a.2.2 : UnitAddCircle)),
                  (fun a => ((eval (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)) (p a.1) a.2 / period : ℝ) : UnitAddCircle))) := by
  intro Lcoord Lout
  have hex (label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
      (k : T) (s : Finset (Fin dim)) :=
    exists_allocated_physical_masked_factor B U b S o hb bW d r hr period hdiv hR C hC hchart hbudget
      Cforward hforward K hK (label s) (f k s) (hf k s) (hf1 k s)
  choose g hL hg hv using hex
  refine ⟨g, hL, hg, ?_⟩
  intro X p hp hm v
  unfold allocatedProductChartIdealApproximation
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  have hs (s : Finset (Fin dim)) := hv label k s p hm
    (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ))
  simp_rw [BooleanCubeKernel.coveredRowsSiteValue_physical U d p hm hp v, hs]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_long_physical_expansion_identity
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lout := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → Finset (Fin dim) →
        ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label k s, LipschitzWith Lout (g label k s)) ∧
      (∀ label k s z, ‖g label k s z‖ ≤ 1) ∧
      AllocatedLongPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW a f p hm g := by
  intro Lcoord Lout
  obtain ⟨g, hg, hbnd, hv⟩ := exists_allocated_physical_masked_expansion B U b S x y₀ q d period r hr hb o bW
    hdiv hR C hC hchart hbudget Cforward hforward K hK a f hf hf1
  exact ⟨g, hg, hbnd, hv p hp hm⟩

theorem exists_allocated_grid_physical_expansion_identity
    (hR : ∀ j, 0 < R j)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) *
      (Fintype.card (Finset (Fin dim)) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      AllocatedGridPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  classical
  obtain ⟨g, hg, _hcoeff, hv⟩ := exists_allocated_finite_model_grid_cover B U b hR S d hb o bW e he Q hQ
    Cforward hforward K hK r hr C hC hchart hbudget
  exact ⟨g, hg, hv x y₀ q period a f p hp hm⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_finite_model_physical_expansion
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    let Lgrid := fun k => max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * commonSitePeriod e k) (4 * commonSitePeriod e k)
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → (∀ a, (e a).Term) → Finset (Fin dim) →
        (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
          ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label i k s, LipschitzWith (Llong + Lgrid k) (g label i k s)) ∧
      (∀ label i k s z, ‖g label i k s z‖ ≤ 1) ∧
      AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  classical
  intro Lcoord Llong Lgrid
  have hsite (j : Fin m) : C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4 := by
    exact siteBudget_of_rowBudget (Nat.cast_nonneg _) (by exact_mod_cast Fintype.card_pos)
      (mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))) (hbudget j)
  obtain ⟨gl, hgl, hglb, hlong⟩ := exists_allocated_long_physical_expansion_identity B U b S x y₀ q d period r hr hb o bW
    hdiv hR C hC hchart hsite Cforward hforward K hK a f hf hf1 p hp hm
  obtain ⟨gg, hgg, hgrid⟩ := exists_allocated_grid_physical_expansion_identity B U b S x y₀ q d period r hr hb o bW e hR he Q hQ
    Cforward hforward K hK C hC hchart hbudget a f p hp hm
  exact join_allocated_physical_expansions B U b S x y₀ q d period r hr hb o bW e a f p hm gl gg hgl
    (fun k s => (hgg k s).1) hglb (fun k s => (hgg k s).2)
    hlong hgrid

theorem exists_allocated_finite_model_uniform_physical_expansion
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (Pperiod Vmax : ℝ≥0) (hPperiod : (period : ℝ≥0) ≤ Pperiod)
    (hVmax : ∀ a, V a ≤ Vmax) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * Pperiod) (4 * Pperiod)
    let Lgrid := max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}) (4 * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → (∀ a, (e a).Term) → Finset (Fin dim) →
        (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
          ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label i k s, LipschitzWith (Llong + Lgrid) (g label i k s)) ∧
      (∀ label i k s z, ‖g label i k s z‖ ≤ 1) ∧
      AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  intro Lcoord Llong Lgrid
  obtain ⟨g, hg, hgb, hidentity⟩ := exists_allocated_finite_model_physical_expansion
    B U b S x y₀ q d period r hr hb o bW e hdiv hR C hC hchart hbudget
    Cforward hforward K hK a f hf hf1 he Q hQ p hp hm
  refine ⟨g, ?_, hgb, hidentity⟩
  intro label i k s
  apply (hg label i k s).weaken
  have hk : (commonSitePeriod e k : ℝ≥0) ≤ Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} := by
    exact_mod_cast commonSitePeriod_le_pow e he hVmax k
  apply add_le_add
  · exact add_le_add le_rfl (max_le_max (mul_le_mul_of_nonneg_left hPperiod zero_le) (mul_le_mul_of_nonneg_left hPperiod zero_le))
  · exact max_le_max (mul_le_mul_of_nonneg_left hk zero_le) (mul_le_mul_of_nonneg_left hk zero_le)

end Erdos3.VectorPolynomial

end

end OAI
