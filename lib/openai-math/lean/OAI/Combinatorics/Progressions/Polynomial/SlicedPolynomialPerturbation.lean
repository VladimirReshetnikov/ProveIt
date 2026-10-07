/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements unchanged. Prove finite regularity below infinity explicitly. -/
import OAI.Compat.FinsetInj
import OAI.Combinatorics.Progressions.Estimates.JointBooleanStability

namespace OAI

section

namespace Erdos3

theorem parameterPolynomialMap_mass_c2_bounds
    {Z I O : Type*} [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ o, realPolynomialMass (p o) ≤ C) {t : ℝ} (ht : |t| ≤ 1)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let M := polynomialMassC2Budget (Fintype.card (PolynomialParameter Z I)) d C
    ‖parameterPolynomialMap p t z x‖ ≤ M ∧
      ‖fderiv ℝ (parameterPolynomialMap p t z) x‖ ≤ M ∧
      ‖fderiv ℝ (fderiv ℝ (parameterPolynomialMap p t z)) x‖ ≤ M := by
  have hb := polynomialVectorMap_mass_c2_bounds p hd hC hmass
    (polynomialParameterPoint t z x) (polynomialParameterPoint_unit_box ht hz hx)
  have hdom := polynomialMassC2Budget_dominates (Fintype.card (PolynomialParameter Z I)) d hC
  have he : parameterPolynomialMap p t z =
      fun y => polynomialVectorMap p (polynomialParameterPoint t z 0 + polynomialParameterInjection Z I y) :=
    funext (fun y => congrArg (polynomialVectorMap p) (polynomialParameterPoint_affine t z y))
  refine ⟨hb.1.trans hdom.1, ?_, ?_⟩
  · rw [he]
    apply affineSlice_fderiv_norm_le _ _ _ x
      ((polynomialVectorMap_contDiff p).differentiable (by norm_num) _)
      (polynomialParameterInjection_norm_le Z I)
    rw [← polynomialParameterPoint_affine]
    exact hb.2.1.trans hdom.2.1
  · rw [he]
    apply affineSlice_second_fderiv_norm_le _ ((polynomialVectorMap_contDiff p).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num))
      _ _ x (polynomialParameterInjection_norm_le Z I)
    rw [← polynomialParameterPoint_affine]
    exact hb.2.2.trans hdom.2.2

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators ContDiff

theorem realPolynomialMass_divMonomial_le {I : Type*}
    (p : MvPolynomial I ℝ) (s : I →₀ ℕ) :
    realPolynomialMass (p.divMonomial s) ≤ realPolynomialMass p := by
  classical
  unfold realPolynomialMass
  simp only [MvPolynomial.coeff_divMonomial]
  apply Finset.sum_le_sum_of_injOn (fun m => s + m)
  · exact (add_right_injective s).injOn
  · intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    exact MvPolynomial.mem_support_iff.mpr (by
      simpa only [MvPolynomial.coeff_divMonomial] using MvPolynomial.mem_support_iff.mp hm)
  · intro m hm
    exact le_rfl
  · intro m hm hnot
    exact abs_nonneg _

theorem parameterPolynomialMap_mass_difference
    {Z I O : Type*} [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial (PolynomialParameter Z I) ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ o, realPolynomialMass (p o) ≤ C) {t : ℝ} (ht : |t| ≤ 1)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let M := polynomialMassC2Budget (Fintype.card (PolynomialParameter Z I)) d C
    ‖parameterPolynomialMap p t z x - parameterPolynomialMap p 0 z x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (parameterPolynomialMap p t z) x -
        fderiv ℝ (parameterPolynomialMap p 0 z) x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (fderiv ℝ (parameterPolynomialMap p t z)) x -
        fderiv ℝ (fderiv ℝ (parameterPolynomialMap p 0 z)) x‖ ≤ |t| * M := by
  let q := fun o => (p o).divMonomial (Finsupp.single none 1)
  have hq := parameterPolynomialMap_mass_c2_bounds q
    (fun o i => mvPolynomial_div_single_degreeOf_le (p o) none i (hd o i)) hC
    (fun o => (realPolynomialMass_divMonomial_le (p o) _).trans (hmass o)) ht z hz x hx
  exact factoredDifference_c2_bounds _ _ _ t
    ((parameterPolynomialMap_contDiff p t z).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num))
    ((parameterPolynomialMap_contDiff p 0 z).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num))
    ((parameterPolynomialMap_contDiff q t z).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num))
    (parameterPolynomialMap_sub_zero p t z) x hq.1 hq.2.1 hq.2.2

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPolynomialScale (N O Z m d : ℕ) (C M a δ A η : ℝ) : ℝ :=
  slicedPrincipalC2Tolerance N O m C a δ A η / (1 + polynomialMassC2Budget Z d M)

theorem slicedPolynomialScale_spec
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {m d : ℕ} (hdegree : ∀ j, Fintype.card (F j) ≤ m)
    {C M a δ η : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) :
    let t := slicedPolynomialScale (Fintype.card (Σ j, B j × F j)) (Fintype.card D)
      (Fintype.card (PolynomialParameter Z ((Σ j, B j × F j)))) m d C M a δ A η
    0 < t ∧ t ≤ 1 ∧
    ∀ (c : ∀ j, B j → ℝ) (lower width : ∀ j, B j × F j → ℝ)
      (b : ∀ j, B j) (i : ∀ j, F j),
      (∀ j p, |lower j p| + |width j p| ≤ 1) →
      (∀ j, (∑ b, |c j b|) ≤ C) → (∀ j, a ≤ |c j (b j)|) →
      (∀ j l, δ ≤ width j (b j, l)) →
      (∀ j l, l ≠ i j → 0 ≤ lower j (b j, l)) →
      ∀ p : (Σ _j : D, Unit) → MvPolynomial (PolynomialParameter Z ((Σ j, B j × F j))) ℝ,
      (∀ o v, (p o).degreeOf v ≤ d) → (∀ o, realPolynomialMass (p o) ≤ M) →
      ∀ (z : Z → ℝ), (∀ v, |z v| ≤ 1) →
      (parameterPolynomialMap p 0 z = jointSlicedPrincipal c lower width) →
      ∀ s : ℝ, |s| ≤ t →
      ∀ φ : ((Σ _j : D, Unit) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |mappedTest (unitBoxMeasure (Σ j, B j × F j)) (jointSlicedPrincipal c lower width) φ -
          mappedTest (unitBoxMeasure (Σ j, B j × F j)) (parameterPolynomialMap p s z) φ| ≤ η := by
  classical
  let N := Fintype.card (Σ j, B j × F j)
  let L := polynomialMassC2Budget (Fintype.card (PolynomialParameter Z (Σ j, B j × F j))) d M
  have hL : 0 ≤ L := polynomialMassC2Budget_nonneg _ _ hM
  let ε := slicedPrincipalC2Tolerance N (Fintype.card D) m C a δ A η
  have hε := slicedPrincipalC2Tolerance_spec (B := B) (F := F) hdegree hC ha hδ hδone hη A hA
  have ht : 0 < ε / (1 + L) := div_pos hε.1 (by linarith)
  have htε : ε / (1 + L) ≤ ε := (div_le_self hε.1.le (by linarith))
  refine ⟨ht, htε.trans hε.2.1, ?_⟩
  intro c lower width b i hwidth hc hprincipal hw hlower p hp hmass z hz hzero s hs φ hφ hφone
  have hs1 : |s| ≤ 1 := hs.trans (htε.trans hε.2.1)
  have hsε : |s| * L ≤ ε := by
    have hh := (le_div_iff₀ (by linarith : 0 < 1 + L)).mp hs
    nlinarith [abs_nonneg s]
  apply hε.2.2 c lower width b i hwidth hc hprincipal hw hlower
    (parameterPolynomialMap p s z) ((parameterPolynomialMap_contDiff p s z).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num))
    _ φ hφ hφone
  intro x hx
  have herr := parameterPolynomialMap_mass_difference p hp hM hmass hs1 z hz x hx
  rw [hzero] at herr
  exact ⟨herr.1.trans hsε, herr.2.1.trans hsε, herr.2.2.trans hsε⟩

theorem jointSlicedPrincipal_polynomial_tail_comparison
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ j, Fintype (B j)] [∀ j, Fintype (F j)]
    [∀ j, DecidableEq (B j)] [∀ j, DecidableEq (F j)]
    (c : ∀ j, B j → ℝ) (lower width : ∀ j, B j × F j → ℝ)
    (b : ∀ j, B j) (i : ∀ j, F j)
    {m d : ℕ} (hdegree : ∀ j, Fintype.card (F j) ≤ m)
    {C M a δ η : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hwidth : ∀ j p, |lower j p| + |width j p| ≤ 1)
    (hc : ∀ j, (∑ b, |c j b|) ≤ C) (hprincipal : ∀ j, a ≤ |c j (b j)|)
    (hw : ∀ j l, δ ≤ width j (b j, l))
    (hlower : ∀ j l, l ≠ i j → 0 ≤ lower j (b j, l))
    (q : (Σ _j : D, Unit) → MvPolynomial (Σ j, B j × F j) ℝ)
    (hqdegree : ∀ o v, (q o).degreeOf v ≤ d) (hqmass : ∀ o, realPolynomialMass (q o) ≤ M)
    (t : ℝ)
    (ht : |t| * polynomialMassC2Budget (Fintype.card (Σ j, B j × F j)) d M ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η)
    (shift : (Σ _j : D, Unit) → ℝ)
    (φ : ((Σ _j : D, Unit) → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |mappedTest (unitBoxMeasure (Σ j, B j × F j))
        (fun x => shift + jointSlicedPrincipal c lower width x) φ -
      mappedTest (unitBoxMeasure (Σ j, B j × F j))
        (fun x => shift + jointSlicedPrincipal c lower width x + t • polynomialVectorMap q x) φ| ≤ η := by
  classical
  let U := jointSlicedPrincipal c lower width
  let V := fun x => U x + t • polynomialVectorMap q x
  have hU : ContDiff ℝ 2 U := (jointSlicedPrincipal_contDiff c lower width).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have hq : ContDiff ℝ 2 (polynomialVectorMap q) := (polynomialVectorMap_contDiff q).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have hV : ContDiff ℝ 2 V := hU.add (hq.const_smul t)
  have hε := slicedPrincipalC2Tolerance_spec (B := B) (F := F) hdegree hC ha hδ hδone hη A hA
  have herr := hε.2.2 c lower width b i hwidth hc hprincipal hw hlower V hV
  have hclose : ∀ x, (∀ p, |x p| ≤ 1) →
      ‖V x - U x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η ∧
      ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η := by
    intro x hx
    have hb := polynomialVectorMap_mass_c2_bounds q hqdegree hM hqmass x hx
    have hdom := polynomialMassC2Budget_dominates (Fintype.card (Σ j, B j × F j)) d hM
    have he := factoredDifference_c2_bounds V U (polynomialVectorMap q) t hV hU hq
      (fun x => add_sub_cancel_left (U x) _) x (hb.1.trans hdom.1)
      (hb.2.1.trans hdom.2.1) (hb.2.2.trans hdom.2.2)
    exact ⟨he.1.trans ht, he.2.1.trans ht, he.2.2.trans ht⟩
  have he := herr hclose (fun y => φ (shift + y)) (hφ.comp (measurable_const.add measurable_id))
    (fun y => hφone (shift + y))
  simpa only [mappedTest, V, U, add_assoc] using he

end Erdos3

end

end OAI
