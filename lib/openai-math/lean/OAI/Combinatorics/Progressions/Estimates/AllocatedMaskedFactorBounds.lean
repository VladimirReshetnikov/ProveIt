import OAI.Combinatorics.Progressions.Geometry.AllocatedMaskedChartProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

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
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d quarter

local notation "coordinates" => (fun w : MixedCoveredJetSource I single E n d =>
  allocatedFullMixedSiteValue (R := R) U b (fun j => mixedArrayRegroup _ _ _ ((Prod.fst w) j) ()))
local notation "buffered" => bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value) r hr

theorem allocatedMaskedSiteChartFactor_normalized
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (w : MixedCoveredJetSource I single E n d) (hw : w ∈ region) :
    allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f (chart w) =
      (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0) *
        buffered f (coordinates w) := by
  rw [allocatedMaskedSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hw]
  simp only [Complex.ofReal_one, one_mul, allocatedBufferedMixedSiteFactor]
  split_ifs <;> simp

theorem exists_allocated_masked_normalized_factor
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    ∃ F : (LayerSamplerAxis I n → ℝ) → ℂ,
      (∀ z, ‖F z‖ ≤ 1) ∧
      LipschitzWith (L + Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) F ∧
      HasCompactSupport F ∧
      (∀ z, F z = (normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr z : ℂ) *
        f (coordinateZeroProjection (allocatedGridAxis (I := I) U b S.value) z)) ∧
      ∀ label (w : MixedCoveredJetSource I single E n d), w ∈ region →
        allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f (chart w) =
          (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0) * F (coordinates w) := by
  refine ⟨buffered f, bufferedCoordinateProjection_norm_le _ r hr f hf1,
    bufferedCoordinateProjection_lipschitz _ r hr f hf hf1,
    bufferedCoordinateProjection_hasCompactSupport _ r hr f, fun _ => rfl, ?_⟩
  exact fun label w hw => allocatedMaskedSiteChartFactor_normalized B U b S o hb bW d r hr period label f w hw

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedMaskedSiteChartFactor_enlarge
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (Ω : ∀ j, Unit → Set (EuclideanSpace ℝ (J j)))
    (hquarter : ∀ j t, standardLatticeClosedQuarterBox (J j) ⊆ Ω j t)
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f =
      restrictedComplexChartDensity chart (mixedCoveredJetRegion U o b d Ω) 1 (fun w =>
        if mixedCoveredSiteResidue d period w = label then buffered f (coordinates w) else 0) := by
  unfold allocatedMaskedSiteChartFactor
  apply restrictedComplexChartDensity_enlarge chart region _
    (mixedCoveredJetRegion_mono U o b d hquarter) (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
  intro w hw
  have hbuf : buffered f (coordinates w) ≠ 0 := by
    intro hzero
    apply hw
    dsimp only
    split_ifs <;> simp_all [allocatedBufferedMixedSiteFactor]
  exact allocatedBufferedMixedSiteFactor_nonzero_mem_quarter B U b S r hr f hR o d w hbuf C hC hchart hbudget

include hR hC hchart hbudget in
theorem allocatedMaskedSiteChartFactor_smallBox
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (w : MixedCoveredJetSource I single E n d)
    (hw : w ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeSmallBox (J j))) :
    allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f (chart w) =
      (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0) * buffered f (coordinates w) := by
  rw [allocatedMaskedSiteChartFactor_enlarge B U b S o hb bW d r hr period hR C hC hchart hbudget label f
    (fun j (_ : Unit) => standardLatticeSmallBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) (fun _ _ => Set.Subset.rfl)]
  rw [restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Set.Subset.rfl)) hw]
  simp only [Complex.ofReal_one, one_mul]
  split_ifs <;> simp

include hR hC hchart hbudget in
theorem allocatedMaskedPhysicalSite_normalized
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (u : X → ℝ)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (w : MixedCoveredJetSource I single E n d)
    (hw : w ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeSmallBox (J j)))
    (hphysical : chart w = BooleanCubeKernel.physicalSingleSiteValue U d p hm u) :
    allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f
        (BooleanCubeKernel.physicalSingleSiteValue U d p hm u) =
      (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0) *
        (normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr (coordinates w) : ℂ) *
        f (allocatedNormalizedMixedSiteValue B U b S
          (fun j => mixedArrayRegroup _ _ _ ((Prod.fst w) j) ())) := by
  rw [← hphysical, allocatedMaskedSiteChartFactor_smallBox B U b S o hb bW d r hr period hR C hC hchart hbudget label f w hw]
  rw [bufferedCoordinateProjection, allocatedFullMixedSiteValue_projection, mul_assoc]

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

abbrev MaskedSiteResidueIndex (n : Fin m → ℕ) (E : Fin m → Type*) :=
  (Σ j, Fin (n j)) ⊕ (Σ j, E j)

noncomputable def mixedCoveredSiteResidueIntegers
    (w : MixedCoveredJetSource I (fun _ => Unit) E n d) : MaskedSiteResidueIndex n E → ℤ
  | .inl ⟨j, i⟩ => (w.1 j).2 i ()
  | .inr ⟨j, i⟩ => (w.2 j () i).val

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J
local notation "RI" => MaskedSiteResidueIndex n E
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

theorem exists_allocated_masked_ambient_factor
    (hR : ∀ j, 0 < R j) (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    let Lbuf := L + Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)
    let Lout := max (Lbuf * (K * ∑ j, Cforward j * Fintype.card (J j))) (2 * period)
    ∃ g : (RI → UnitAddCircle) × (ambient → UnitAddCircle) → ℂ,
      LipschitzWith Lout g ∧ (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ w : MixedCoveredJetSource I single E n d, w ∈ region →
        g ((fun i => (((mixedCoveredSiteResidueIntegers d w i : ℝ) / period : ℝ) : UnitAddCircle)),
          coveredJetAmbientTorus U d (chart w)) =
          allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f (chart w) / 4 := by
  intro Lbuf Lout
  let F := bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value) r hr f
  let decode := fun a : RI → ZMod period =>
    ((fun j i => a (.inl ⟨j,i⟩)), (fun j i => a (.inr ⟨j,i⟩)))
  let raw := fun a : RI → ZMod period => fun v : ambient → ℝ =>
    if decode a = label then F (allocatedFullAmbientSiteCoordinates (R := R) U b o v) else 0
  have hFl : LipschitzWith Lbuf F := bufferedCoordinateProjection_lipschitz _ r hr f hf hf1
  have hFb : ∀ z, ‖F z‖ ≤ 1 := bufferedCoordinateProjection_norm_le _ r hr f hf1
  have hraw (a) : LipschitzWith (Lbuf * (K * ∑ j, Cforward j * Fintype.card (J j))) (raw a) := by
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
    (period : ℝ≥0) (Lbuf * (K * ∑ j, Cforward j * Fintype.card (J j))) (fun _ => le_rfl) raw hraw hrawb
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
  rw [allocatedMaskedSiteChartFactor_normalized B U b S o hb bW d r hr period label f w hw]
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

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem bufferedCoordinateProjection_lipschitz_uniform
    {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]
    (r : ℝ≥0) (hr : 0 < r) (hr1 : 1 ≤ r)
    (f : (D → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    LipschitzWith (L + Fintype.card D * normalizedSiteCutoffBound)
      (bufferedCoordinateProjection P r hr f) := by
  apply (bufferedCoordinateProjection_lipschitz P r hr f hf hf1).weaken
  apply add_le_add le_rfl
  apply div_le_self (by positivity)
  exact (by norm_num : (1 : ℝ≥0) ≤ 2).trans (le_mul_of_one_le_right (by norm_num) hr1)

namespace VectorPolynomial

theorem mixedCoveredSiteResidueLabels_card
    {m : ℕ} (n : Fin m → ℕ) (E : Fin m → Type*) [∀ j, Fintype (E j)]
    (V : Type*) [Fintype V] (period : ℕ) [NeZero period] :
    Fintype.card (V → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) =
      period ^ (((∑ j, n j) + ∑ j, Fintype.card (E j)) * Fintype.card V) := by
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
    ZMod.card, Finset.prod_pow_eq_pow_sum, ← pow_add, ← pow_mul]

theorem mixedCoveredSiteResidueLabels_card_le_exp
    {m : ℕ} (n : Fin m → ℕ) (E : Fin m → Type*) [∀ j, Fintype (E j)]
    (V : Type*) [Fintype V] (period : ℕ) [NeZero period]
    {P : ℝ} (hp : (period : ℝ) ≤ Real.exp P) :
    (Fintype.card (V → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) : ℝ) ≤
      Real.exp ((((∑ j, n j) + ∑ j, Fintype.card (E j)) * Fintype.card V : ℕ) * P) := by
  rw [mixedCoveredSiteResidueLabels_card n E V period, Nat.cast_pow]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg period) hp _).trans_eq (Real.exp_nat_mul _ _).symm

end VectorPolynomial
end Erdos3

end

end OAI
