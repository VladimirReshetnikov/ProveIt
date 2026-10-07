import OAI.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueCenterMix
import OAI.Combinatorics.Progressions.Linear.FiniteCenteredKernel

namespace OAI

section

namespace Erdos3

theorem pmf_translate_apply {A : Type*} [AddCommGroup A]
    (p : PMF A) (anchor x : A) :
    p.map (fun y => anchor + y) x = p (x - anchor) := by
  have h := pmf_map_injective_at p (fun y => anchor + y)
    (fun _ _ h => add_left_cancel h) (x - anchor)
  have he : anchor + (x - anchor) = x := by abel
  simpa only [he] using h

noncomputable def translatedSelectedResidueDensityPMF {K I : Type*}
    [Fintype K] [Fintype I]
    (anchor : K × I → ℤ)
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V (fun x => D (anchor + x))) :
    PMF (K × I → ℤ) :=
  (selectedResidueDensityPMF modulus G V hV hZ (fun x => D (anchor + x))
    (fun _ => hD0 _) hD).map (fun x => anchor + x)

theorem translatedSelectedResidueDensityPMF_toReal {K I : Type*}
    [Fintype K] [Fintype I]
    (anchor : K × I → ℤ)
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V (fun x => D (anchor + x)))
    (x : K × I → ℤ) :
    (translatedSelectedResidueDensityPMF anchor modulus G V hV hZ D hD0 hD x).toReal =
      (selectedResidueSmoothPMF modulus G V hV hZ (x - anchor)).toReal * D x /
        selectedResidueDensityMass modulus G V (fun y => D (anchor + y)) := by
  have he : anchor + (x - anchor) = x := by abel
  simp only [translatedSelectedResidueDensityPMF, pmf_translate_apply,
    selectedResidueDensityPMF_toReal, he]

theorem translatedSelectedResidueDensityPMF_support {K I : Type*}
    [Fintype K] [Fintype I]
    (anchor : K × I → ℤ)
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V (fun x => D (anchor + x)))
    (x : K × I → ℤ)
    (hx : 0 < (translatedSelectedResidueDensityPMF anchor modulus G V hV hZ D hD0 hD x).toReal) :
    x - anchor ∈ rectangularWeightIndices 0 V 1 ∧
      columnResiduePattern modulus (x - anchor) ∈ G ∧ 0 < D x := by
  rw [translatedSelectedResidueDensityPMF_toReal] at hx
  have hmul := (lt_div_iff₀ hD).mp hx
  simp only [zero_mul] at hmul
  rcases mul_pos_iff.mp hmul with hpos | hneg
  · obtain ⟨href, hdensity⟩ := hpos
    refine ⟨?_, ?_, hdensity⟩
    · by_contra hn
      rw [selectedResidueSmoothPMF_toReal,
        selectedResidueSmoothWeight_zero_off modulus G V hV _ hn, zero_div] at href
      exact (lt_irrefl 0) href
    · by_contra hn
      simp only [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight,
        hn, ite_false, zero_div] at href
      exact (lt_irrefl 0) href
  · exact False.elim ((not_lt_of_ge ENNReal.toReal_nonneg) hneg.1)

end Erdos3

end

section

namespace Erdos3

theorem translatedSelectedResidueDensityPMF_complex_mean {K I : Type*}
    [Fintype K] [Fintype I] (anchor : K × I → ℤ)
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V (fun x => D (anchor + x)))
    (φ : (K × I → ℤ) → ℂ) :
    (∑' y, ((translatedSelectedResidueDensityPMF anchor modulus G V hV hZ D hD0 hD y).toReal : ℂ) * φ y) =
      ∑' x, ((selectedResidueDensityPMF modulus G V hV hZ (fun z => D (anchor + z))
        (fun _ => hD0 _) hD x).toReal : ℂ) * φ (anchor + x) :=
  pmf_map_injective_expectation _ _ (fun _ _ h => add_left_cancel h) φ

end Erdos3

end

section

namespace Erdos3

theorem pmf_map_injective_real_expectation {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) (φ : Y → ℝ) :
    (∑' y, (p.map f y).toReal * φ y) = ∑' x, (p x).toReal * φ (f x) := by
  have hs : Function.support (fun y => (p.map f y).toReal * φ y) ⊆ Set.range f := by
    intro y hy
    by_contra hn
    have hz := pmf_map_zero_off_range p f y hn
    exact hy (by simp only [hz, ENNReal.toReal_zero, zero_mul])
  have he := hf.tsum_eq hs
  simpa only [pmf_map_injective_at p f hf] using he.symm

theorem translatedSelectedResidueDensityPMF_mean {K I : Type*}
    [Fintype K] [Fintype I] (anchor : K × I → ℤ)
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V (fun x => D (anchor + x)))
    (φ : (K × I → ℤ) → ℝ) :
    (∑' y, (translatedSelectedResidueDensityPMF anchor modulus G V hV hZ D hD0 hD y).toReal * φ y) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ (fun z => D (anchor + z))
        (fun _ => hD0 _) hD x).toReal * φ (anchor + x) :=
  pmf_map_injective_real_expectation _ _ (fun _ _ h => add_left_cancel h) φ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty) (anchor : B → K × I → ℤ)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
variable (hD : ∀ a, 0 < selectedResidueDensityMass modulus T W (fun u => D (anchor a + u)))

noncomputable def selectedAnchoredMixture :
    FiniteProbabilityWeights (A × rectangularWeightIndices 0 W 1) :=
  (FiniteProbabilityWeights.uniformFinset A hA).joint (fun a =>
    selectedResidueTiltedFiniteLaw modulus T W hW hZ (fun u => D (anchor a.val + u))
      (fun _ => hD0 _) (hD a.val))

theorem selectedAnchoredMixture_mean (f : B → (K × I → ℤ) → ℝ) :
    (selectedAnchoredMixture A hA anchor modulus T W hW hZ D hD0 hD).mean
      (fun z => f z.1.val (anchor z.1.val + z.2.val)) =
    𝔼 a ∈ A, ∑' z, (translatedSelectedResidueDensityPMF (anchor a) modulus T W hW hZ
      D hD0 (hD a) z).toReal * f a z := by
  rw [selectedAnchoredMixture, FiniteProbabilityWeights.joint_mean]
  have he (a : B) := selectedResidueTiltedFiniteLaw_mean modulus T W hW hZ
    (fun u => D (anchor a + u)) (fun _ => hD0 _) (hD a) (fun u => f a (anchor a + u))
  change (FiniteProbabilityWeights.uniformFinset A hA).mean
    (fun a => (selectedResidueTiltedFiniteLaw modulus T W hW hZ
      (fun u => D (anchor a.val + u)) (fun _ => hD0 _) (hD a.val)).mean
        (fun u => f a.val (anchor a.val + u.val))) = _
  simp_rw [he]
  rw [FiniteProbabilityWeights.uniformFinset_mean A hA (fun a =>
    ∑' z, (selectedResidueDensityPMF modulus T W hW hZ
      (fun u => D (anchor a + u)) (fun _ => hD0 _) (hD a) z).toReal * f a (anchor a + z))]
  apply Finset.expect_congr rfl
  intro a _
  exact (translatedSelectedResidueDensityPMF_mean (anchor a) modulus T W hW hZ
    D hD0 (hD a) (f a)).symm

theorem selectedAnchoredMixture_weight (z : A × rectangularWeightIndices 0 W 1) :
    (selectedAnchoredMixture A hA anchor modulus T W hW hZ D hD0 hD).weight z =
      (A.card : ℝ)⁻¹ * (translatedSelectedResidueDensityPMF (anchor z.1.val)
        modulus T W hW hZ D hD0 (hD z.1.val) (anchor z.1.val + z.2.val)).toReal := by
  rw [translatedSelectedResidueDensityPMF_toReal]
  have he : anchor z.1.val + z.2.val - anchor z.1.val = z.2.val := by abel
  rw [he]
  change (FiniteProbabilityWeights.uniformFinset A hA).weight z.1 *
    (selectedResidueTiltedFiniteLaw modulus T W hW hZ
      (fun u => D (anchor z.1.val + u)) (fun _ => hD0 _) (hD z.1.val)).weight z.2 = _
  rw [selectedResidueTiltedFiniteLaw, FiniteProbabilityWeights.reweightPositive_weight,
    selectedResidueFiniteLaw_densityMass modulus T W hW hZ (fun u => D (anchor z.1.val + u))]
  simp only [
    FiniteProbabilityWeights.uniformFinset, FiniteProbabilityWeights.uniform,
    Fintype.card_coe,
    selectedResidueFiniteLaw, finiteSupportProbability, selectedResidueSmoothPMF_toReal]

theorem selectedAnchoredMixture_pos_iff (z : A × rectangularWeightIndices 0 W 1) :
    0 < (selectedAnchoredMixture A hA anchor modulus T W hW hZ D hD0 hD).weight z ↔
      0 < (translatedSelectedResidueDensityPMF (anchor z.1.val)
        modulus T W hW hZ D hD0 (hD z.1.val) (anchor z.1.val + z.2.val)).toReal := by
  rw [selectedAnchoredMixture_weight]
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  exact mul_pos_iff_of_pos_left (inv_pos.mpr hc)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueTiltedFiniteLaw_complexMean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D) (f : (K × I → ℤ) → ℂ) :
    (selectedResidueTiltedFiniteLaw modulus T W hW hZ D hD0 hD).complexMean (fun z => f z.val) =
      ∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ) * f z := by
  rw [selectedResidueTiltedFiniteLaw, FiniteProbabilityWeights.reweightPositive_complexMean,
    selectedResidueDensityPMF_complexMean,
    selectedResidueFiniteLaw_densityMass modulus T W hW hZ D,
    selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => (D z : ℂ) * f z)]

theorem selectedAnchoredMixture_complexMean {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty) (anchor : B → K × I → ℤ)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : ∀ a, 0 < selectedResidueDensityMass modulus T W (fun u => D (anchor a + u)))
    (f : B → (K × I → ℤ) → ℂ) :
    (selectedAnchoredMixture A hA anchor modulus T W hW hZ D hD0 hD).complexMean
      (fun z => f z.1.val (anchor z.1.val + z.2.val)) =
      𝔼 a ∈ A, ∑' z, ((translatedSelectedResidueDensityPMF (anchor a) modulus T W hW hZ
        D hD0 (hD a) z).toReal : ℂ) * f a z := by
  rw [selectedAnchoredMixture, FiniteProbabilityWeights.joint_complexMean]
  have he (a : B) := selectedResidueTiltedFiniteLaw_complexMean modulus T W hW hZ
    (fun u => D (anchor a + u)) (fun _ => hD0 _) (hD a) (fun u => f a (anchor a + u))
  change (FiniteProbabilityWeights.uniformFinset A hA).complexMean
    (fun a => (selectedResidueTiltedFiniteLaw modulus T W hW hZ
      (fun u => D (anchor a.val + u)) (fun _ => hD0 _) (hD a.val)).complexMean
        (fun u => f a.val (anchor a.val + u.val))) = _
  simp_rw [he]
  rw [FiniteProbabilityWeights.uniformFinset_complexMean A hA (fun a =>
    ∑' z, ((selectedResidueDensityPMF modulus T W hW hZ
      (fun u => D (anchor a + u)) (fun _ => hD0 _) (hD a) z).toReal : ℂ) * f a (anchor a + z))]
  apply Finset.expect_congr rfl
  intro a _
  exact (translatedSelectedResidueDensityPMF_complex_mean (anchor a) modulus T W hW hZ
    D hD0 (hD a) (f a)).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem translatedSelectedResidueDensityPMF_integrable_test {C K I : Type*}
    [MeasurableSpace C] [Fintype K] [Fintype I]
    (μ : Measure C) [IsFiniteMeasure μ] (anchor : K × I → ℤ)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : C → (K × I → ℤ) → ℝ) (hDm : ∀ z, Measurable (fun c => D c z))
    (hD0 : ∀ c z, 0 ≤ D c z)
    (hD : ∀ c, 0 < selectedResidueDensityMass modulus T W (fun u => D c (anchor + u)))
    (f : (K × I → ℤ) → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    Integrable (fun c => ∑' z, ((translatedSelectedResidueDensityPMF anchor modulus T W hW hZ
      (D c) (hD0 c) (hD c) z).toReal : ℂ) * f z) μ := by
  simp_rw [translatedSelectedResidueDensityPMF_complex_mean,
    selectedResidueDensityPMF_normalizedDensityTest]
  apply (selectedResidueFiniteLaw modulus T W hW hZ).normalizedDensityTest_integrable μ
    (fun c u => D c (anchor + u.val)) (fun u => hDm _) (fun c u => hD0 c _)
  · intro c
    rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (fun u => D c (anchor + u))]
    exact hD c
  · exact fun u => hf _

theorem integral_selectedAnchoredMixture_complexMean {B C K I : Type*}
    [MeasurableSpace C] [Fintype K] [Fintype I]
    (μ : Measure C) [IsFiniteMeasure μ] (A : Finset B) (hA : A.Nonempty)
    (anchor : B → K × I → ℤ) (modulus : I → ℕ)
    (T : Finset (ColumnResiduePattern K I modulus)) (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : C → (K × I → ℤ) → ℝ) (hDm : ∀ z, Measurable (fun c => D c z))
    (hD0 : ∀ c z, 0 ≤ D c z)
    (hD : ∀ a c, 0 < selectedResidueDensityMass modulus T W (fun u => D c (anchor a + u)))
    (f : B → (K × I → ℤ) → ℂ) (hf : ∀ a z, ‖f a z‖ ≤ 1) :
    (∫ c, (selectedAnchoredMixture A hA anchor modulus T W hW hZ (D c) (hD0 c)
      (fun a => hD a c)).complexMean (fun z => f z.1.val (anchor z.1.val + z.2.val)) ∂μ) =
      𝔼 a ∈ A, ∫ c, ∑' z, ((translatedSelectedResidueDensityPMF (anchor a) modulus T W hW hZ
        (D c) (hD0 c) (hD a c) z).toReal : ℂ) * f a z ∂μ := by
  let g := fun c a => ∑' z, ((translatedSelectedResidueDensityPMF (anchor a) modulus T W hW hZ
    (D c) (hD0 c) (hD a c) z).toReal : ℂ) * f a z
  have he (c : C) :
      (selectedAnchoredMixture A hA anchor modulus T W hW hZ (D c) (hD0 c)
        (fun a => hD a c)).complexMean (fun z => f z.1.val (anchor z.1.val + z.2.val)) =
      (FiniteProbabilityWeights.uniformFinset A hA).complexMean (fun a => g c a.val) := by
    rw [selectedAnchoredMixture_complexMean, FiniteProbabilityWeights.uniformFinset_complexMean A hA (g c)]
  simp_rw [he]
  rw [FiniteProbabilityWeights.integral_complexMean]
  · exact FiniteProbabilityWeights.uniformFinset_complexMean A hA (fun a => ∫ c, g c a ∂μ)
  · intro a
    exact translatedSelectedResidueDensityPMF_integrable_test μ (anchor a.val) modulus T W hW hZ
      D hDm hD0 (hD a.val) (f a.val) (hf a.val)

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty) (anchor : B → Option K × I → ℤ)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
variable (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (D : (Option K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
variable (hD : ∀ a, 0 < selectedResidueDensityMass modulus T W (fun u => D (anchor a + u)))
variable (root : K → ℤ) (Q : Finset (I → ℤ)) (hQ : Q.Nonempty) {C ε : ℝ}
variable (hdom : ∀ φ : (I → ℝ) → ℝ, (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
  (𝔼 a ∈ A, ∑' z, (translatedSelectedResidueDensityPMF (anchor a)
    modulus T W hW hZ D hD0 (hD a) z).toReal * φ (physicalAffineSite root z)) ≤
    C * (𝔼 x ∈ Q, φ (fun i => (x i : ℝ))) + ε)

include hdom in
theorem selectedAnchoredMixture_physical_excess_le {Y : Type*} [Fintype Y] (F : (I → ℝ) → Y) :
    ((FiniteProbabilityWeights.uniformFinset Q hQ).fiberLaw
      (fun x => F (fun i => (x.val i : ℝ)))).excessMass
      ((selectedAnchoredMixture A hA anchor modulus T W hW hZ D hD0 hD).fiberLaw
        (fun z => F (physicalAffineSite root (anchor z.1.val + z.2.val)))) C ≤ ε := by
  apply FiniteProbabilityWeights.excessMass_le_of_mass_le
  intro S
  rw [FiniteProbabilityWeights.fiberLaw_mass_indicator, FiniteProbabilityWeights.fiberLaw_mass_indicator,
    selectedAnchoredMixture_mean A hA anchor modulus T W hW hZ D hD0 hD
      (fun _ z => if F (physicalAffineSite root z) ∈ S then 1 else 0),
    FiniteProbabilityWeights.uniformFinset_mean Q hQ
      (fun x => if F (fun i => (x i : ℝ)) ∈ S then 1 else 0)]
  apply hdom (fun v => if F v ∈ S then 1 else 0)
  intro v
  split_ifs <;> constructor <;> norm_num

include hdom in
theorem selectedAnchoredMixture_physical_tail_le {Y : Type*} [Fintype Y] (F : (I → ℝ) → Y) :
    let p := (FiniteProbabilityWeights.uniformFinset Q hQ).fiberLaw
      (fun x => F (fun i => (x.val i : ℝ)))
    let q := (selectedAnchoredMixture A hA anchor modulus T W hW hZ D hD0 hD).fiberLaw
      (fun z => F (physicalAffineSite root (anchor z.1.val + z.2.val)))
    q.mass (Finset.univ.filter (fun y => 2*C*p.weight y < q.weight y)) ≤ 2*ε :=
  FiniteProbabilityWeights.mass_above_double_cap_le_of_excess _ _
    (selectedAnchoredMixture_physical_excess_le A hA anchor modulus T W hW hZ D hD0 hD
      root Q hQ hdom F)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedAnchoredMixture_integer_box_excess_tail {B K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (A : Finset B) (hA : A.Nonempty) (anchor : B → Option K × I → ℤ)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (Option K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : ∀ a, 0 < selectedResidueDensityMass modulus T W (fun u => D (anchor a + u)))
    (root : K → ℤ) (N : I → ℕ) (hN : (integerBox N).Nonempty) {C ε : ℝ}
    (hdom : ∀ φ : (I → ℝ) → ℝ, (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
      (𝔼 a ∈ A, ∑' z, (translatedSelectedResidueDensityPMF (anchor a)
        modulus T W hW hZ D hD0 (hD a) z).toReal * φ (physicalAffineSite root z)) ≤
        C * (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + ε) :
    let q := (selectedAnchoredMixture A hA anchor modulus T W hW hZ D hD0 hD).fiberLaw
      (fun z => integerBoxObservation N hN (physicalAffineSite root (anchor z.1.val + z.2.val)))
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).excessMass q C ≤ ε ∧
      q.mass (Finset.univ.filter (fun x => 2*C/(integerBox N).card < q.weight x)) ≤ 2*ε := by
  have he := selectedAnchoredMixture_physical_excess_le A hA anchor modulus T W hW hZ
    D hD0 hD root (integerBox N) hN hdom (integerBoxObservation N hN)
  rw [integerBoxObservation_reference] at he
  refine ⟨he, ?_⟩
  have ht := FiniteProbabilityWeights.mass_above_double_cap_le_of_excess _ _ he
  simpa only [FiniteProbabilityWeights.uniformFinset_weight, div_eq_mul_inv] using ht

end Erdos3.BooleanCubeKernel

end

end OAI
