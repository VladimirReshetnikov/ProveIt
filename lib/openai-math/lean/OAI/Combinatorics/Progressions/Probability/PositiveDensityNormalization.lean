import OAI.Combinatorics.Progressions.Estimates.PreparedModularProductivityPrecision
import OAI.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

noncomputable def selectedJointDensityMass (D : B → (K × I → ℤ) → ℝ) : ℝ :=
  𝔼 a ∈ A, selectedResidueDensityMass modulus T W (D a)

noncomputable def selectedJointReference :
    FiniteProbabilityWeights (A × rectangularWeightIndices 0 W 1) :=
  (FiniteProbabilityWeights.uniformFinset A hA).prod (selectedResidueFiniteLaw modulus T W hW hZ)

theorem selectedJointReference_densityMass (D : B → (K × I → ℤ) → ℝ) :
    (selectedJointReference A hA modulus T W hW hZ).mean (fun z => D z.1.val z.2.val) =
      selectedJointDensityMass A modulus T W D := by
  rw [selectedJointReference, FiniteProbabilityWeights.mean_prod]
  simp_rw [selectedResidueFiniteLaw_densityMass]
  exact FiniteProbabilityWeights.uniformFinset_mean A hA
    (fun a => selectedResidueDensityMass modulus T W (D a))

include hA in
theorem selectedJointDensityMass_bounds (D : B → (K × I → ℤ) → ℝ) {a b : ℝ}
    (hD : ∀ x, selectedResidueDensityMass modulus T W (D x) ∈ Set.Icc a b) :
    selectedJointDensityMass A modulus T W D ∈ Set.Icc a b := by
  rw [selectedJointDensityMass, ← FiniteProbabilityWeights.uniformFinset_mean A hA]
  exact (FiniteProbabilityWeights.uniformFinset A hA).mean_mem_Icc _ (fun x => hD x.val)

include hA in
theorem selectedJointDensityMass_close (D : B → (K × I → ℤ) → ℝ) {ε : ℝ}
    (hD : ∀ x, |selectedResidueDensityMass modulus T W (D x)-1| ≤ ε) :
    |selectedJointDensityMass A modulus T W D-1| ≤ ε := by
  rw [selectedJointDensityMass, ← FiniteProbabilityWeights.uniformFinset_mean A hA]
  exact (FiniteProbabilityWeights.uniformFinset A hA).abs_mean_sub_const_le _ 1 ε (fun x => hD x.val)

noncomputable def selectedJointFiniteLaw (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D) :
    FiniteProbabilityWeights (A × rectangularWeightIndices 0 W 1) :=
  (selectedJointReference A hA modulus T W hW hZ).reweightPositive
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val)
    (by rw [selectedJointReference_densityMass]; exact hD)

theorem selectedJointFiniteLaw_weight (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D)
    (z : A × rectangularWeightIndices 0 W 1) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).weight z =
      (A.card : ℝ)⁻¹ * (selectedResidueSmoothPMF modulus T W hW hZ z.2.val).toReal *
        D z.1.val z.2.val / selectedJointDensityMass A modulus T W D := by
  rw [selectedJointFiniteLaw, FiniteProbabilityWeights.reweightPositive_weight,
    selectedJointReference_densityMass, selectedResidueSmoothPMF_toReal]
  simp only [selectedJointReference, FiniteProbabilityWeights.prod,
    FiniteProbabilityWeights.uniformFinset, FiniteProbabilityWeights.uniform, Fintype.card_coe,
    selectedResidueFiniteLaw, finiteSupportProbability]

theorem selectedJointFiniteLaw_complexMean (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D)
    (f : B → (K × I → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).complexMean
      (fun z => f z.1.val z.2.val) =
      (selectedJointReference A hA modulus T W hW hZ).normalizedDensityTest
        (fun z => D z.1.val z.2.val) (fun z => f z.1.val z.2.val) := by
  rw [selectedJointFiniteLaw, FiniteProbabilityWeights.reweightPositive_complexMean_eq_normalizedDensityTest]

theorem selectedJointFiniteLaw_local_comparison (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlocal : ∀ a, 0 < selectedResidueDensityMass modulus T W (D a))
    (f : B → (K × I → ℤ) → ℂ) (hf : ∀ a z, ‖f a z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ a, |selectedResidueDensityMass modulus T W (D a)-1| ≤ ε) :
    ‖(selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).complexMean
        (fun z => f z.1.val z.2.val) -
      (𝔼 a ∈ A, ∑' z, ((selectedResidueDensityPMF modulus T W hW hZ (D a) (hD0 a) (hlocal a) z).toReal : ℂ) *
        f a z)‖ ≤ 2*ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus T W hW hZ
  have h := p.joint_normalization_compare q (fun z => D z.1.val z.2.val)
    (fun z => hD0 z.1.val z.2.val)
    (fun a => by
      change 0 < q.mean (fun y => D a.val y.val)
      rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (D a.val)]
      exact hlocal a.val)
    (by change 0 < (selectedJointReference A hA modulus T W hW hZ).mean _
        rw [selectedJointReference_densityMass]; exact hD)
    (fun z => f z.1.val z.2.val) (fun z => hf z.1.val z.2.val)
    (fun a => by
      change |q.mean (fun y => D a.val y.val)-1| ≤ ε
      rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (D a.val)]
      exact hclose a.val)
  rw [selectedJointFiniteLaw_complexMean]
  change ‖(p.prod q).normalizedDensityTest _ _ - _‖ ≤ _
  have he (a : B) := selectedResidueDensityPMF_normalizedDensityTest modulus T W hW hZ
    (D a) (hD0 a) (hlocal a) (f a)
  have hm := FiniteProbabilityWeights.uniformFinset_complexMean A hA
    (fun a => q.normalizedDensityTest (fun z => D a z.val) (fun z => f a z.val))
  dsimp only [p] at h
  rw [hm] at h
  simpa only [he] using h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem prod_reweightPositive_mean_le_of_conditional
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (D : X × Y → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hglobal : 0 < (p.prod q).mean D)
    (hlocal : ∀ x, 0 < q.mean (fun y => D (x, y)))
    (f : X × Y → ℝ) {ε : ℝ}
    (hbound : ∀ x,
      (q.reweightPositive (fun y => D (x, y)) (fun y => hD0 (x, y)) (hlocal x)).mean
        (fun y => f (x, y)) ≤ ε) :
    ((p.prod q).reweightPositive D hD0 hglobal).mean f ≤ ε := by
  have hraw (x) : q.mean (fun y => D (x, y) * f (x, y)) ≤
      ε * q.mean (fun y => D (x, y)) := by
    exact (div_le_iff₀ (hlocal x)).mp (by simpa only [reweightPositive_mean] using hbound x)
  rw [reweightPositive_mean]
  apply (div_le_iff₀ hglobal).mpr
  rw [mean_prod, mean_prod]
  calc
    _ ≤ p.mean (fun x => ε * q.mean (fun y => D (x, y))) := p.mean_mono hraw
    _ = _ := by
      change (∑ x, p.weight x * (ε * q.mean (fun y => D (x, y)))) =
        ε * ∑ x, p.weight x * q.mean (fun y => D (x, y))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end FiniteProbabilityWeights

theorem selectedJointFiniteLaw_conditional_event_le
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern K I modulus))
    (width : K × I → ℝ) (hwidth : ∀ z, 0 < width z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells width z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus cells width D)
    (hlocal : ∀ a, 0 < selectedResidueDensityMass modulus cells width (D a))
    (event : B → (K × I → ℤ) → Prop) {ε : ℝ}
    (hbound : ∀ a,
      (∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ
        (D a) (hD0 a) (hlocal a) z).toReal * (if event a z then 1 else 0)) ≤ ε) :
    (selectedJointFiniteLaw A hA modulus cells width hwidth hZ D hD0 hD).mean
      (fun z => if event z.1.val z.2.val then 1 else 0) ≤ ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus cells width hwidth hZ
  have hlocal' (a : A) : 0 < q.mean (fun z => D a.val z.val) := by
    rw [selectedResidueFiniteLaw_densityMass]
    exact hlocal a.val
  have hglobal : 0 < (p.prod q).mean (fun z => D z.1.val z.2.val) := by
    change 0 < (selectedJointReference A hA modulus cells width hwidth hZ).mean _
    rw [selectedJointReference_densityMass]
    exact hD
  apply FiniteProbabilityWeights.prod_reweightPositive_mean_le_of_conditional p q
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val) hglobal hlocal'
    (fun z => if event z.1.val z.2.val then 1 else 0)
  intro a
  change (selectedResidueTiltedFiniteLaw modulus cells width hwidth hZ
    (D a.val) (hD0 a.val) (hlocal a.val)).mean (fun z => if event a.val z.val then 1 else 0) ≤ ε
  rw [selectedResidueTiltedFiniteLaw_mean modulus cells width hwidth hZ (D a.val)
    (hD0 a.val) (hlocal a.val) (fun z => if event a.val z then 1 else 0)]
  exact hbound a.val

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedJointDensityMass_smooth_mass_pos
    {B K I : Type*} [Fintype K] [Fintype I]
    (bases : Finset B) (modulus : I → ℕ)
    (cells : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (D : B → (K × I → ℤ) → ℝ)
    (hD : 0 < selectedJointDensityMass bases modulus cells W D) :
    0 < ∑' z, selectedResidueSmoothWeight modulus cells W z := by
  have hn : 0 ≤ ∑' z, selectedResidueSmoothWeight modulus cells W z :=
    tsum_nonneg (selectedResidueSmoothWeight_nonneg modulus cells W)
  by_contra h
  have hz : (∑' z, selectedResidueSmoothWeight modulus cells W z) = 0 :=
    le_antisymm (le_of_not_gt h) hn
  have he : selectedJointDensityMass bases modulus cells W D = 0 := by
    simp [selectedJointDensityMass, selectedResidueDensityMass, finiteDensityMass, hz]
  exact (ne_of_gt hD) he

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
variable (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
variable (hD : 0 < selectedJointDensityMass A modulus cells W D)

theorem selectedJointFiniteLaw_mass_le_reference
    {a C : ℝ} (ha : 0 < a)
    (hmass : a ≤ selectedJointDensityMass A modulus cells W D)
    (hcap : ∀ z : A × rectangularWeightIndices 0 W 1, D z.1.val z.2.val ≤ C)
    (F : Finset (A × rectangularWeightIndices 0 W 1)) :
    (selectedJointFiniteLaw A hA modulus cells W hW hZ D hD0 hD).mass F ≤
      (C / a) * (selectedJointReference A hA modulus cells W hW hZ).mass F := by
  let p := selectedJointReference A hA modulus cells W hW hZ
  let φ := fun z : A × rectangularWeightIndices 0 W 1 => if z ∈ F then (1 : ℝ) else 0
  have hφ : ∀ z, 0 ≤ φ z := fun z => by dsimp only [φ]; split_ifs <;> norm_num
  have hcapMean : p.mean (fun z => D z.1.val z.2.val * φ z) ≤ C * p.mean φ := by
    rw [← p.mean_const_mul]
    exact p.mean_mono fun z => mul_le_mul_of_nonneg_right (hcap z) (hφ z)
  have hm : a ≤ p.mean (fun z => D z.1.val z.2.val) := by
    simpa only [p, selectedJointReference_densityMass] using hmass
  have hp : 0 < p.mean (fun z => D z.1.val z.2.val) := ha.trans_le hm
  have h := p.reweightPositive_test_le (fun z => D z.1.val z.2.val)
    (fun z => hD0 z.1.val z.2.val) hp φ hφ (C := C) (ε := 0) ha hm (by simpa using hcapMean)
  simpa only [selectedJointFiniteLaw, φ, FiniteProbabilityWeights.mean_indicator,
    add_zero, div_mul_eq_mul_div, p] using h

theorem selectedJointReference_retained_mass
    {C ρ : ℝ} (hC : 0 < C)
    (hmass : (1 / 2 : ℝ) ≤ selectedJointDensityMass A modulus cells W D)
    (hcap : ∀ z : A × rectangularWeightIndices 0 W 1, D z.1.val z.2.val ≤ C)
    (F : Finset (A × rectangularWeightIndices 0 W 1))
    (hF : ρ < (selectedJointFiniteLaw A hA modulus cells W hW hZ D hD0 hD).mass F) :
    ρ / (2 * C) < (selectedJointReference A hA modulus cells W hW hZ).mass F := by
  have h := selectedJointFiniteLaw_mass_le_reference A hA modulus cells W hW hZ D hD0 hD
    (by norm_num : (0 : ℝ) < 1 / 2) hmass hcap F
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC)).mpr
  have h' := hF.trans_le h
  convert h' using 1; ring

theorem selectedJointReference_retained_exp_mass
    {P Q : ℝ}
    (hmass : (1 / 2 : ℝ) ≤ selectedJointDensityMass A modulus cells W D)
    (hcap : ∀ z : A × rectangularWeightIndices 0 W 1,
      D z.1.val z.2.val ≤ Real.exp P)
    (F : Finset (A × rectangularWeightIndices 0 W 1))
    (hF : Real.exp (-Q) <
      (selectedJointFiniteLaw A hA modulus cells W hW hZ D hD0 hD).mass F) :
    Real.exp (-(Q + P + 1)) <
      (selectedJointReference A hA modulus cells W hW hZ).mass F := by
  have ht := selectedJointReference_retained_mass A hA modulus cells W hW hZ
    D hD0 hD (Real.exp_pos P) hmass hcap F hF
  apply lt_of_le_of_lt _ ht
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos P))).mpr
  calc
    Real.exp (-(Q + P + 1)) * (2 * Real.exp P) =
        2 * (Real.exp (-(Q + P + 1)) * Real.exp P) := by ring
    _ = 2 * Real.exp (-(Q + 1)) := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 1 * Real.exp (-(Q + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-Q) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B K I Y : Type*} [Fintype K] [Fintype I] [Fintype Y]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
variable (hD : 0 < selectedJointDensityMass A modulus T W D)

theorem selectedJointFiniteLaw_weighted_expectation (f : B → (K × I → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).complexMean
      (fun z => f z.1.val z.2.val) =
      (𝔼 a ∈ A, ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
        (f a z * (D a z : ℂ))) / (selectedJointDensityMass A modulus T W D : ℂ) := by
  rw [selectedJointFiniteLaw_complexMean, FiniteProbabilityWeights.normalizedDensityTest,
    selectedJointReference_densityMass, selectedJointReference,
    FiniteProbabilityWeights.complexMean_prod]
  rw [FiniteProbabilityWeights.uniformFinset_complexMean A hA
    (fun a => (selectedResidueFiniteLaw modulus T W hW hZ).complexMean
      (fun z => (D a z.val : ℂ) * f a z.val))]
  congr 1
  apply Finset.expect_congr rfl
  intro a _
  rw [selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun z => (D a z : ℂ) * f a z)]
  apply tsum_congr
  intro z
  ring

noncomputable def selectedJointTupleLaw (p : FiniteProbabilityWeights Y) :
    FiniteProbabilityWeights (Y × (A × rectangularWeightIndices 0 W 1)) :=
  p.prod (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD)

theorem selectedJointTupleLaw_complexMean (p : FiniteProbabilityWeights Y)
    (f : Y → B → (K × I → ℤ) → ℂ) :
    (selectedJointTupleLaw A hA modulus T W hW hZ D hD0 hD p).complexMean
      (fun z => f z.1 z.2.1.val z.2.2.val) =
      𝔼 a ∈ A, p.complexMean (fun y => ∑' z,
        ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
          (f y a z * (D a z : ℂ))) / (selectedJointDensityMass A modulus T W D : ℂ) := by
  have hdiv (g : Y → ℂ) (z : ℂ) :
      p.complexMean (fun y => g y / z) = p.complexMean g / z := by
    simp only [FiniteProbabilityWeights.complexMean, mul_div_assoc, Finset.sum_div]
  rw [selectedJointTupleLaw, FiniteProbabilityWeights.complexMean_prod]
  simp_rw [selectedJointFiniteLaw_weighted_expectation]
  rw [hdiv, p.complexMean_finset_expect]
  simp only [Finset.expect_eq_sum_div_card, Finset.sum_div, div_div, mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B K X : Type*} [Fintype K] [Fintype X]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
variable (T : Finset (ColumnResiduePattern K X modulus))
variable (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
variable (hc : ∀ r : T, 0 < shiftedSmoothProductMass
  (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
  (residueProfileWidth modulus V))

theorem selectedJointReference_residue_expectation (f : B → (K × X → ℤ) → ℂ) :
    (selectedJointReference A hA modulus T V hV hZ).complexMean
      (fun z => f z.1.val z.2.val) =
      𝔼 a ∈ A, ∑ r : T,
        (((∑' y, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V y) /
          (∑' y, selectedResidueSmoothWeight modulus T V y) : ℝ) : ℂ) *
        ∑' z, ((residueSmoothIndexPMF (columnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) *
          f a (residueLatticeArray (columnResidueRepresentative modulus r.val) modulus z) := by
  rw [selectedJointReference, FiniteProbabilityWeights.complexMean_prod]
  simp_rw [selectedResidueFiniteLaw_complexMean]
  rw [FiniteProbabilityWeights.uniformFinset_complexMean A hA
    (fun a => ∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * f a z)]
  simp_rw [selectedResidueSmoothPMF_mixture modulus hmodulus T V hV hZ hc,
    residueSmoothPMF_expectation]

theorem selectedJointFiniteLaw_residue_expectation (density : B → (K × X → ℤ) → ℝ)
    (hdensity : ∀ a z, 0 ≤ density a z)
    (hmass : 0 < selectedJointDensityMass A modulus T V density)
    (f : B → (K × X → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T V hV hZ density hdensity hmass).complexMean
      (fun z => f z.1.val z.2.val) =
      (𝔼 a ∈ A, ∑ r : T,
        (((∑' y, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V y) /
          (∑' y, selectedResidueSmoothWeight modulus T V y) : ℝ) : ℂ) *
        ∑' z, ((residueSmoothIndexPMF (columnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) *
          ((density a (residueLatticeArray (columnResidueRepresentative modulus r.val) modulus z) : ℂ) *
            f a (residueLatticeArray (columnResidueRepresentative modulus r.val) modulus z))) /
        (selectedJointDensityMass A modulus T V density : ℂ) := by
  rw [selectedJointFiniteLaw_complexMean, FiniteProbabilityWeights.normalizedDensityTest,
    selectedJointReference_densityMass,
    selectedJointReference_residue_expectation A hA modulus hmodulus T V hV hZ hc
      (fun a z => (density a z : ℂ) * f a z)]

namespace BooleanCubeKernel

theorem selectedJointFiniteLaw_physical_cube {B K X α : Type*} [Fintype K] [Fintype X]
    (A : Finset B) (hA : A.Nonempty) (base : B → X → ℤ)
    (root : K → ℤ) (D : Matrix α K ℤ)
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (T : Finset (ColumnResiduePattern (Option K) X modulus))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V))
    (density : B → (Option K × X → ℤ) → ℝ) (hdensity : ∀ a z, 0 ≤ density a z)
    (hmass : 0 < selectedJointDensityMass A modulus T V density)
    (φ : B → (X → (Unit ⊕ α) → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T V hV hZ density hdensity hmass).complexMean
      (fun z => φ z.1.val (physicalCubeRootDifferences root D (base z.1.val) z.2.val)) =
      (𝔼 a ∈ A, ∑ r : T,
        (((∑' y, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V y) /
          (∑' y, selectedResidueSmoothWeight modulus T V y) : ℝ) : ℂ) *
        ∑' z, ((residueSmoothIndexPMF (columnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) *
          ((density a (residueLatticeArray (columnResidueRepresentative modulus r.val) modulus z) : ℂ) *
            φ a (physicalCubeResidueCoordinates root D (base a)
              (columnResidueRepresentative modulus r.val) modulus z))) /
        (selectedJointDensityMass A modulus T V density : ℂ) := by
  simpa only [physicalCubeRootDifferences_residue] using
    selectedJointFiniteLaw_residue_expectation A hA modulus hmodulus T V hV hZ hc
      density hdensity hmass (fun a z => φ a (physicalCubeRootDifferences root D (base a) z))

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def residueCoordinateProductLaw {K X : Type*} [Fintype K] [Fintype X]
    (residue : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : PMF (X → K → ℤ) :=
  dependentProductPMF (fun x => shiftedSmoothProductPMF
    (fun k => residueProfileCenter residue modulus (k, x))
    (fun k => residueProfileWidth modulus V (k, x))
    (fun k => residueProfileWidth_pos modulus V hmodulus hV (k, x))
    (shiftedSmoothProductMass_slice_pos _ _ (residueProfileWidth_pos modulus V hmodulus hV) hZ x))

theorem residueSmoothIndexPMF_grouped {K X : Type*} [Fintype K] [Fintype X]
    (residue : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) :
    (residueSmoothIndexPMF residue modulus hmodulus V hV hZ).map (spatialCoordinateArrayEquiv K X) =
      residueCoordinateProductLaw residue modulus hmodulus V hV hZ :=
  shiftedSmoothProductPMF_grouped _ _ (residueProfileWidth_pos modulus V hmodulus hV) hZ

theorem residueSmoothIndexPMF_grouped_expectation {K X : Type*} [Fintype K] [Fintype X]
    (residue : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ z).toReal : ℂ) * φ z) =
      ∑' z, ((residueCoordinateProductLaw residue modulus hmodulus V hV hZ z).toReal : ℂ) *
        φ ((spatialCoordinateArrayEquiv K X).symm z) :=
  shiftedSmoothProductPMF_grouped_expectation _ _ (residueProfileWidth_pos modulus V hmodulus hV) hZ φ

theorem selectedJointFiniteLaw_grouped_expectation {B K X : Type*} [Fintype K] [Fintype X]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (T : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V))
    (density : B → (K × X → ℤ) → ℝ) (hdensity : ∀ a z, 0 ≤ density a z)
    (hmass : 0 < selectedJointDensityMass A modulus T V density)
    (f : B → (K × X → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T V hV hZ density hdensity hmass).complexMean
        (fun z => f z.1.val z.2.val) =
      (𝔼 a ∈ A, ∑ r : T,
        (((∑' y, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V y) /
          (∑' y, selectedResidueSmoothWeight modulus T V y) : ℝ) : ℂ) *
        ∑' z, ((residueCoordinateProductLaw (columnResidueRepresentative modulus r.val)
          modulus hmodulus V hV (hc r) z).toReal : ℂ) *
          ((density a (residueLatticeArray (columnResidueRepresentative modulus r.val) modulus
            ((spatialCoordinateArrayEquiv K X).symm z)) : ℂ) *
            f a (residueLatticeArray (columnResidueRepresentative modulus r.val) modulus
              ((spatialCoordinateArrayEquiv K X).symm z)))) /
        (selectedJointDensityMass A modulus T V density : ℂ) := by
  rw [selectedJointFiniteLaw_residue_expectation A hA modulus hmodulus T V hV hZ hc density hdensity hmass f]
  simp_rw [residueSmoothIndexPMF_grouped_expectation]

end Erdos3

end

section

namespace Erdos3

theorem positiveProjectionAccuracy_mass_bound {p : ℝ} (hp : 0 ≤ p) :
    3 * positiveProjectionAccuracy p ≤ Real.exp (-p) ∧
      3 * positiveProjectionAccuracy p ≤ 1 / 2 := by
  have hfour : (3 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have htwo : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hnine : (9 : ℝ) ≤ Real.exp 4 := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (2 : ℝ)]
  have hsix : (6 : ℝ) ≤ Real.exp (2 * p + 4) :=
    (by linarith : (6 : ℝ) ≤ Real.exp 4).trans (Real.exp_le_exp.mpr (by linarith))
  constructor
  · calc
      _ ≤ Real.exp 4 * Real.exp (-(2 * p + 4)) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = Real.exp (-(2 * p)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ = 3 / Real.exp (2 * p + 4) := by
        simp only [positiveProjectionAccuracy, Real.exp_neg, div_eq_mul_inv]
      _ ≤ 3 / (6 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsix
      _ = 1 / 2 := by norm_num

theorem positiveProjectionAccuracy_normalizer {p Z : ℝ} (hp : 0 ≤ p)
    (hZ : |Z - 1| ≤ 3 * positiveProjectionAccuracy p) :
    |Z - 1| ≤ Real.exp (-p) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Z ∧ Z⁻¹ ≤ 2 := by
  have he := positiveProjectionAccuracy_mass_bound hp
  have hhalf := hZ.trans he.2
  have hlo : 1 / 2 ≤ Z := by have h := (abs_le.mp hhalf).1; linarith
  have hhi : Z ≤ 3 / 2 := by have h := (abs_le.mp hhalf).2; linarith
  have hpos : 0 < Z := by linarith
  refine ⟨hZ.trans he.1, ⟨hlo, hhi⟩, hpos, ?_⟩
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlo
  simpa only [one_div, inv_div, inv_one, div_one, inv_inv] using h

theorem selectedJointDensityMass_positive_accuracy {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty) (modulus : I → ℕ)
    (T : Finset (ColumnResiduePattern K I modulus)) (W : K × I → ℝ)
    (D : B → (K × I → ℤ) → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ a, |selectedResidueDensityMass modulus T W (D a) - 1| ≤
      3 * positiveProjectionAccuracy p) :
    let Z := selectedJointDensityMass A modulus T W D
    |Z - 1| ≤ Real.exp (-p) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Z ∧ Z⁻¹ ≤ 2 :=
  positiveProjectionAccuracy_normalizer hp (selectedJointDensityMass_close A hA modulus T W D hD)

end Erdos3

end

end OAI
