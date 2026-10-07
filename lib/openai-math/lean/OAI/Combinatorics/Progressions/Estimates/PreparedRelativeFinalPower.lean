/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.PreparedFinalScalarPowerBudget
import OAI.Combinatorics.Progressions.Linear.RelativePatchRankTightening

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight

theorem centeredFiniteProbabilityMeasure_ae_centers [SFinite μ]
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z) :
    ∀ᵐ c ∂μ, ∀ x, 0 < (law c).weight x → P (c, x) := by
  have hprod := (ae_withDensity_iff
    (centeredFiniteWeightDensity_measurable law hweight).ennreal_ofReal).mp hP
  apply (Measure.ae_ae_of_ae_prod hprod).mono
  intro c hc x hx
  exact (Measure.ae_count_iff.mp hc) x (ne_of_gt (ENNReal.ofReal_pos.mpr hx))

theorem exists_center_with_good_mass [IsProbabilityMeasure μ]
    (F : C → Finset Ω) (hF : ∀ x, MeasurableSet {c | x ∈ F c})
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z)
    {δ : ℝ} (hδ : 0 < δ)
    (hmass : δ ≤ (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F z.1}) :
    ∃ c, δ / 2 < (law c).mass (F c) ∧
      ∀ x, 0 < (law c).weight x → P (c, x) := by
  have hPc := centeredFiniteProbabilityMeasure_ae_centers μ law hweight P hP
  have hint := centeredFinite_mass_integrable μ law hweight F hF
  rw [centeredFiniteProbabilityMeasure_real_finite_events_of_measurable_membership
    μ law hweight F hF] at hmass
  by_contra h
  have hbound : ∀ᵐ c ∂μ, (law c).mass (F c) ≤ δ / 2 := by
    filter_upwards [hPc] with c hc
    by_contra hgt
    exact h ⟨c, lt_of_not_ge hgt, hc⟩
  have hi := integral_mono_ae hint (integrable_const (δ / 2)) hbound
  rw [integral_const] at hi
  simp only [probReal_univ, smul_eq_mul, one_mul] at hi
  linarith

theorem exists_center_finite_good_event [IsProbabilityMeasure μ]
    (event : Set (C × Ω)) (hevent : MeasurableSet event)
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z)
    {δ : ℝ} (hδ : 0 < δ)
    (hmass : δ ≤ (centeredFiniteProbabilityMeasure μ law).real event) :
    ∃ (c : C) (G : Finset Ω), δ / 2 < (law c).mass G ∧
      ∀ x ∈ G, (c, x) ∈ event ∧ 0 < (law c).weight x ∧ P (c, x) := by
  classical
  let F : C → Finset Ω := fun c => Finset.univ.filter (fun x => (c, x) ∈ event)
  have hF (x : Ω) : MeasurableSet {c | x ∈ F c} := by
    simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and, Set.preimage, id_eq] using
      hevent.preimage (measurable_id.prodMk (measurable_const (a := x)))
  have heq : {z : C × Ω | z.2 ∈ F z.1} = event := by
    ext z
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Prod.mk.eta]
  obtain ⟨c, hc, hPc⟩ := exists_center_with_good_mass μ law hweight F hF P hP hδ
    (by simpa only [heq] using hmass)
  let G := (F c).filter (fun x => 0 < (law c).weight x)
  have hG : (law c).mass G = (law c).mass (F c) := by
    unfold FiniteProbabilityWeights.mass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hw : 0 < (law c).weight x
    · simp only [hw, ite_true]
    · simp only [hw, ite_false]
      exact (le_antisymm (le_of_not_gt hw) ((law c).nonneg x)).symm
  refine ⟨c, G, by rwa [hG], ?_⟩
  intro x hx
  obtain ⟨hxF, hxpos⟩ := Finset.mem_filter.mp hx
  exact ⟨(Finset.mem_filter.mp hxF).2, hxpos, hPc x hxpos⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem exists_center_finite_productive_good_event
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (A : Set (C × Ω)) (hA : MeasurableSet A)
    (bad : Set (C × Ω)) (hbad : MeasurableSet bad)
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z)
    {gain : ℝ} (hgain : 0 < gain)
    (hAmass : gain / 4 ≤ (centeredFiniteProbabilityMeasure μ law).real A)
    (hbadmass : (centeredFiniteProbabilityMeasure μ law).real bad ≤ gain / 16) :
    ∃ (c : C) (G : Finset Ω), gain / 16 < (law c).mass G ∧
      ∀ x ∈ G, (c, x) ∈ A ∧ (c, x) ∉ bad ∧
        0 < (law c).weight x ∧ P (c, x) := by
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  have hdiff := le_measureReal_sdiff
    (μ := centeredFiniteProbabilityMeasure μ law) (s₁ := A) (s₂ := bad)
  have hmass : 3 * gain / 16 ≤ (centeredFiniteProbabilityMeasure μ law).real (A \ bad) := by
    linarith only [hAmass, hbadmass, hdiff]
  obtain ⟨c, G, hG, hgood⟩ := exists_center_finite_good_event μ law hweight
    (A \ bad) (hA.diff hbad) P hP (by positivity : 0 < 3 * gain / 16) hmass
  refine ⟨c, G, by linarith only [hG, hgain], ?_⟩
  intro x hx
  obtain ⟨⟨hAx, hnotbad⟩, hpos, hPx⟩ := hgood x hx
  exact ⟨hAx, hnotbad, hpos, hPx⟩

theorem exists_center_finite_productive_good_event_avoiding_residual
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (A : Set (C × Ω)) (hA : MeasurableSet A)
    (bad : Set (C × Ω)) (hbad : MeasurableSet bad)
    (residual : Set (C × Ω)) (hResidual : MeasurableSet residual)
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z)
    {gain : ℝ} (hgain : 0 < gain)
    (hAmass : gain / 4 ≤ (centeredFiniteProbabilityMeasure μ law).real A)
    (hbadmass : (centeredFiniteProbabilityMeasure μ law).real bad ≤ gain / 16)
    (hResidualMass : (centeredFiniteProbabilityMeasure μ law).real residual ≤ gain / 32) :
    ∃ (c : C) (G : Finset Ω), gain / 16 < (law c).mass G ∧
      ∀ x ∈ G, (c, x) ∈ A ∧ (c, x) ∉ bad ∧ (c, x) ∉ residual ∧
        0 < (law c).weight x ∧ P (c, x) := by
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  have hunion : (centeredFiniteProbabilityMeasure μ law).real (bad ∪ residual) ≤
      gain / 16 + gain / 32 :=
    (measureReal_union_le bad residual).trans (add_le_add hbadmass hResidualMass)
  have hdiff := le_measureReal_sdiff
    (μ := centeredFiniteProbabilityMeasure μ law) (s₁ := A) (s₂ := bad ∪ residual)
  have hmass : 5 * gain / 32 ≤
      (centeredFiniteProbabilityMeasure μ law).real (A \ (bad ∪ residual)) := by
    linarith only [hAmass, hunion, hdiff]
  obtain ⟨c, G, hG, hgood⟩ := exists_center_finite_good_event μ law hweight
    (A \ (bad ∪ residual)) (hA.diff (hbad.union hResidual)) P hP
    (by positivity : 0 < 5 * gain / 32) hmass
  refine ⟨c, G, by linarith only [hG, hgain], ?_⟩
  intro x hx
  obtain ⟨⟨hAx, hnotunion⟩, hpos, hPx⟩ := hgood x hx
  exact ⟨hAx, (fun hb => hnotunion (Or.inl hb)),
    (fun hr => hnotunion (Or.inr hr)), hpos, hPx⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_centered_joint_fixed_patch_function (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {C Ω X T : Type*}
      [MeasurableSpace C] [Fintype Ω] [Nonempty Ω]
      [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype X] [Fintype T]
      (μ : Measure C) [IsProbabilityMeasure μ]
      (law : C → FiniteProbabilityWeights Ω)
      (_hweight : ∀ x, Measurable (fun c => (law c).weight x))
      (productive : Finset Ω),
      0 < (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} →
      ∀ (D : ℕ) (p : ℝ), 0 ≤ p → (D : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      ∀ (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℤ)
        (score : Ω → T → ℝ), (∀ h t, |score h t| ≤ 1) →
      (∀ h ∈ productive, ∃ (d : ℕ) (patch : PolynomialPatch X s d),
        d ≤ D ∧ (patch.kernel.lip : ℝ) ≤ Real.exp p ∧
        Real.exp (-p) ≤ (localLaw h).mean
          (fun t => score h t * patch.value (fun i => (point h t i : ℝ)))) →
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots X d w) (localForm : Ω → PolynomialSlots X d w)
        (retained : Finset Ω),
        d ≤ D ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        MeasurableSet {z : C × Ω | z.2 ∈ retained} ∧
        (((centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive}) /
          ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-((p + 2) ^ E)) ≤
          (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ retained} ∧
        ∀ z : C × Ω, z.2 ∈ retained →
          Real.exp (-((p + 2) ^ E)) ≤ (localLaw z.2).mean
            (fun t => score z.2 t * (B.shearTransformedSlots hw
              ((localForm z.2).loweringAt (fun i => (point z.2 t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_varying_rank_fixed_patch_function s
  refine ⟨E, hE, ?_⟩
  intro C Ω X T _ _ _ _ _ _ _ μ _ law hweight productive hmass D p hp hD hX
    localLaw point score hscore hpatch
  let outer := integratedFiniteProbabilityWeights μ law hweight
  have houter : 0 < outer.mass productive := by
    rwa [integratedFiniteProbabilityWeights_mass_eq_joint]
  have hnonempty : productive.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at houter
  obtain ⟨h₀, hh₀⟩ := hnonempty
  obtain ⟨d₀, patch₀, hd₀, hlip₀, _⟩ := hpatch h₀ hh₀
  have hall (h : Ω) : ∃ (d : ℕ) (patch : PolynomialPatch X s d),
      d ≤ D ∧ (patch.kernel.lip : ℝ) ≤ Real.exp p ∧
      (h ∈ productive → Real.exp (-p) ≤ (localLaw h).mean
        (fun t => score h t * patch.value (fun i => (point h t i : ℝ)))) := by
    by_cases hh : h ∈ productive
    · obtain ⟨d, patch, hd, hlip, hpositive⟩ := hpatch h hh
      exact ⟨d, patch, hd, hlip, fun _ => hpositive⟩
    · exact ⟨d₀, patch₀, hd₀, hlip₀, fun hmem => (hh hmem).elim⟩
  choose d patch hd hlip hpositive using hall
  obtain ⟨d', w, hw, Ψ, B, localForm, retained, hd', hpos, hws, hΨ, hB,
      hsub, hretained, hlocal⟩ :=
    hfixed outer productive d patch D p hd houter hp hD hX hlip
      localLaw point score hscore hpositive
  refine ⟨d', w, hw, Ψ, B, localForm, retained, hd', hpos, hws, hΨ, hB,
    hsub, ?_, ?_, fun z hz => hlocal z.2 hz⟩
  · exact (Finset.measurableSet retained).preimage measurable_snd
  · simpa only [outer, integratedFiniteProbabilityWeights_mass_eq_joint] using hretained

theorem exists_centered_joint_fixed_patch_function_ae (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {C Ω X T : Type*}
      [MeasurableSpace C] [Fintype Ω] [Nonempty Ω]
      [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype X] [Fintype T]
      (μ : Measure C) [IsProbabilityMeasure μ]
      (law : C → FiniteProbabilityWeights Ω)
      (_hweight : ∀ x, Measurable (fun c => (law c).weight x))
      (productive : Finset Ω),
      0 < (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} →
      ∀ (D : ℕ) (p : ℝ), 0 ≤ p → (D : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      ∀ (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℤ)
        (score : Ω → T → ℝ), (∀ h t, |score h t| ≤ 1) →
      (∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z.2 ∈ productive →
        ∃ (d : ℕ) (patch : PolynomialPatch X s d),
        d ≤ D ∧ (patch.kernel.lip : ℝ) ≤ Real.exp p ∧
        Real.exp (-p) ≤ (localLaw z.2).mean
          (fun t => score z.2 t * patch.value (fun i => (point z.2 t i : ℝ)))) →
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots X d w) (localForm : Ω → PolynomialSlots X d w)
        (retained : Finset Ω),
        d ≤ D ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        MeasurableSet {z : C × Ω | z.2 ∈ retained} ∧
        (((centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive}) /
          ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-((p + 2) ^ E)) ≤
          (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ retained} ∧
        ∀ z : C × Ω, z.2 ∈ retained →
          Real.exp (-((p + 2) ^ E)) ≤ (localLaw z.2).mean
            (fun t => score z.2 t * (B.shearTransformedSlots hw
              ((localForm z.2).loweringAt (fun i => (point z.2 t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_centered_joint_fixed_patch_function s
  refine ⟨E, hE, ?_⟩
  intro C Ω X T _ _ _ _ _ _ _ μ _ law hweight productive hmass D p hp hD hX
    localLaw point score hscore hpatch
  let eligible := fun h : Ω => ∃ (d : ℕ) (patch : PolynomialPatch X s d),
    d ≤ D ∧ (patch.kernel.lip : ℝ) ≤ Real.exp p ∧
      Real.exp (-p) ≤ (localLaw h).mean
        (fun t => score h t * patch.value (fun i => (point h t i : ℝ)))
  let good := productive.filter eligible
  have hsame : (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ good} =
      (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} := by
    apply measureReal_congr
    filter_upwards [hpatch] with z hz
    apply propext
    simp only [good, Finset.mem_filter]
    exact ⟨And.left, fun hh => ⟨hh, hz hh⟩⟩
  have hgood : 0 < (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ good} := by
    rwa [hsame]
  obtain ⟨d, w, hw, Ψ, B, localForm, retained, hd, hpos, hws, hΨ, hB,
      hsub, hmeas, hretained, hlocal⟩ :=
    hfixed μ law hweight good hgood D p hp hD hX localLaw point score hscore
      (fun h hh => (Finset.mem_filter.mp hh).2)
  refine ⟨d, w, hw, Ψ, B, localForm, retained, hd, hpos, hws, hΨ, hB,
    hsub.trans (Finset.filter_subset _ _), hmeas, ?_, hlocal⟩
  rwa [hsame] at hretained

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_centered_joint_returned_patch_normalization_ae (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {C Ω X T : Type*}
      [MeasurableSpace C] [Fintype Ω] [Nonempty Ω]
      [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype X] [Fintype T] [Nonempty T]
      (μ : Measure C) [IsProbabilityMeasure μ]
      (law : C → FiniteProbabilityWeights Ω)
      (_hweight : ∀ x, Measurable (fun c => (law c).weight x))
      (productive : Finset Ω),
      0 < (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} →
      ∀ (D : ℕ) (p : ℝ), 0 ≤ p → (D : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      ∀ (Allowed : Ω → FiniteProbabilityWeights T → Prop)
        (point : Ω → T → X → ℤ) (score : Ω → T → ℝ), (∀ h t, |score h t| ≤ 1) →
      (∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z.2 ∈ productive →
        ∃ (d : ℕ) (patch : PolynomialPatch X s d) (localLaw : FiniteProbabilityWeights T),
          Allowed z.2 localLaw ∧ d ≤ D ∧ (patch.kernel.lip : ℝ) ≤ Real.exp p ∧
          Real.exp (-p) ≤ localLaw.mean
            (fun t => score z.2 t * patch.value (fun i => (point z.2 t i : ℝ)))) →
      ∃ (localLaw : Ω → FiniteProbabilityWeights T)
        (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots X d w) (localForm : Ω → PolynomialSlots X d w)
        (retained : Finset Ω),
        d ≤ D ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        MeasurableSet {z : C × Ω | z.2 ∈ retained} ∧
        (((centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive}) /
          ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-((p + 2) ^ E)) ≤
          (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ retained} ∧
        (∀ h ∈ retained, Allowed h (localLaw h)) ∧
        ∀ z : C × Ω, z.2 ∈ retained →
          Real.exp (-((p + 2) ^ E)) ≤ (localLaw z.2).mean
            (fun t => score z.2 t * (B.shearTransformedSlots hw
              ((localForm z.2).loweringAt (fun i => (point z.2 t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_centered_joint_fixed_patch_function s
  refine ⟨E, hE, ?_⟩
  intro C Ω X T _ _ _ _ _ _ _ _ μ _ law hweight productive hmass D p hp hD hX
    Allowed point score hscore hpatch
  let eligible := fun h : Ω => ∃ l : FiniteProbabilityWeights T, Allowed h l ∧
    ∃ (d : ℕ) (patch : PolynomialPatch X s d), d ≤ D ∧ (patch.kernel.lip : ℝ) ≤ Real.exp p ∧
      Real.exp (-p) ≤ l.mean (fun t => score h t * patch.value (fun i => (point h t i : ℝ)))
  let good := productive.filter eligible
  have hsame : (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ good} =
      (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} := by
    apply measureReal_congr
    filter_upwards [hpatch] with z hz
    apply propext
    constructor
    · exact fun hh => (Finset.mem_filter.mp hh).1
    · intro hh
      obtain ⟨d, patch, l, hAllowed, hd, hlip, hpositive⟩ := hz hh
      exact Finset.mem_filter.mpr ⟨hh, l, hAllowed, d, patch, hd, hlip, hpositive⟩
  let localLaw : Ω → FiniteProbabilityWeights T := fun h =>
    if he : eligible h then Classical.choose he else FiniteProbabilityWeights.uniform T
  have hlocal (h : Ω) (he : eligible h) : Allowed h (localLaw h) ∧
      ∃ (d : ℕ) (patch : PolynomialPatch X s d), d ≤ D ∧ (patch.kernel.lip : ℝ) ≤ Real.exp p ∧
        Real.exp (-p) ≤ (localLaw h).mean
          (fun t => score h t * patch.value (fun i => (point h t i : ℝ))) := by
    dsimp only [localLaw]
    rw [dite_eq_left he]
    exact Classical.choose_spec he
  have hgood : 0 < (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ good} := by
    rwa [hsame]
  obtain ⟨d, w, hw, Ψ, B, localForm, retained, hd, hpos, hws, hΨ, hB,
      hsub, hmeas, hretained, hnormalized⟩ :=
    hfixed μ law hweight good hgood D p hp hD hX localLaw point score hscore
      (fun h hh => (hlocal h (Finset.mem_filter.mp hh).2).2)
  refine ⟨localLaw, d, w, hw, Ψ, B, localForm, retained, hd, hpos, hws, hΨ, hB,
    hsub.trans (Finset.filter_subset _ _), hmeas, ?_, ?_, hnormalized⟩
  · rwa [hsame] at hretained
  · intro h hh
    exact (hlocal h (Finset.mem_filter.mp (hsub hh)).2).1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

def RelativeReturnedFiberLaw {X : Type*} [Fintype X] [DecidableEq X]
    (keep : X → Prop) [DecidablePred keep] (N : X → ℕ) (cost : ℝ)
    (law : FiniteProbabilityWeights (integerBox N)) : Prop :=
  ∃ (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (q : ℕ), 0 < q ∧
    ∃ (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
      (hlen : ∀ i, 0 < S.length i),
      (∀ i, Real.exp (-cost) * (N i.val : ℝ) ≤ (S.length i : ℝ)) ∧
      law = S.fiberSliceLaw hlen fixed hfixed

theorem RelativeReturnedFiberLaw.mono {X : Type*} [Fintype X] [DecidableEq X]
    {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {cost cost' : ℝ}
    {law : FiniteProbabilityWeights (integerBox N)}
    (h : RelativeReturnedFiberLaw keep N cost law) (hcost : cost ≤ cost') :
    RelativeReturnedFiberLaw keep N cost' law := by
  obtain ⟨fixed, hfixed, q, hq, S, hlen, hlength, hlaw⟩ := h
  refine ⟨fixed, hfixed, q, hq, S, hlen, ?_, hlaw⟩
  intro i
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)).trans (hlength i)

theorem exists_centered_joint_returned_fiber_normalization_ae (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {C Ω X : Type*}
      [MeasurableSpace C] [Fintype Ω] [Nonempty Ω]
      [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype X] [DecidableEq X]
      (μ : Measure C) [IsProbabilityMeasure μ]
      (law : C → FiniteProbabilityWeights Ω)
      (_hweight : ∀ x, Measurable (fun c => (law c).weight x))
      (productive : Finset Ω),
      0 < (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive} →
      ∀ (N : X → ℕ) (keep : X → Prop) [DecidablePred keep],
      (∀ i, 0 < N i) →
      ∀ (rankBound : ℕ) (p cost : ℝ), 0 ≤ p →
      (rankBound : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p → cost ≤ p →
      ∀ (f : Ω → (X → ℤ) → ℝ) (target : ℝ),
      (∀ h x, x ∈ integerBox N → f h x ∈ Set.Icc (0 : ℝ) 1) →
      target ∈ Set.Icc (0 : ℝ) 1 →
      (∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, z.2 ∈ productive →
        ∃ (fixed : {i // ¬keep i} → ℤ),
          (∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ)) ∧
          RelativePatchSliceConclusion s (fun i : {i // keep i} => N i.val)
            (fun u => f z.2 (finiteSplitPoint keep u fixed)) target rankBound cost) →
      ∃ (localLaw : Ω → FiniteProbabilityWeights (integerBox N))
        (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots X d w) (localForm : Ω → PolynomialSlots X d w)
        (retained : Finset Ω),
        d ≤ rankBound ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        MeasurableSet {z : C × Ω | z.2 ∈ retained} ∧
        (((centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ productive}) /
          ((rankBound + 1) * (s + 1) ^ rankBound : ℕ)) *
            Real.exp (-((p + 2) ^ E)) ≤
          (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ retained} ∧
        (∀ h ∈ retained, RelativeReturnedFiberLaw keep N cost (localLaw h)) ∧
        ∀ z : C × Ω, z.2 ∈ retained →
          Real.exp (-((p + 2) ^ E)) ≤ (localLaw z.2).mean
            (fun t => (f z.2 t.val - target) * (B.shearTransformedSlots hw
              ((localForm z.2).loweringAt (fun i => (t.val i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hnormalize⟩ := exists_centered_joint_returned_patch_normalization_ae s
  refine ⟨E, hE, ?_⟩
  intro C Ω X _ _ _ _ _ _ _ μ _ law hweight productive hmass N keep _ hN
    rankBound p cost hp hrank hX hcost f target hf htarget hslice
  let : Nonempty (integerBox N) := by
    refine ⟨⟨fun _ => 0, (mem_integerBox N _).mpr ?_⟩⟩
    intro i
    exact ⟨le_rfl, by exact_mod_cast hN i⟩
  apply hnormalize μ law hweight productive hmass rankBound p hp hrank hX
    (fun _ => RelativeReturnedFiberLaw keep N cost)
    (fun _ t => t.val) (fun h t => f h t.val - target)
  · intro h t
    obtain ⟨hf0, hf1⟩ := hf h t.val t.property
    exact abs_le.mpr ⟨by linarith [htarget.2], by linarith [htarget.1]⟩
  · filter_upwards [hslice] with z hz
    intro hproductive
    obtain ⟨fixed, hfixed, hreturned⟩ := hz hproductive
    obtain ⟨d, Qfull, localLaw, hd, _, hlip, hscore, q, hq, S, hlen, hlength, hlaw⟩ :=
      hreturned.exists_fiber_law_with_slice fixed hfixed (fun i => hN i.val)
    refine ⟨d, Qfull, localLaw, ?_, hd, ?_, ?_⟩
    · exact ⟨fixed, hfixed, q, hq, S, hlen, hlength, hlaw⟩
    · exact hlip.trans (Real.exp_le_exp.mpr hcost)
    · exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hscore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem exists_relative_finite_returned_fiber_normalization (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {Ω X : Type*}
      [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
      (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω),
      0 < outer.mass productive →
      ∀ (N : X → ℕ) (keep : X → Prop) [DecidablePred keep],
      (∀ i, 0 < N i) → ∀ (p : ℝ), 0 ≤ p →
      ∀ (target : ℝ), target ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (rankBound : ℕ) (f : Ω → (X → ℤ) → ℝ),
      (∀ h x, x ∈ integerBox N → f h x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ h ∈ productive, ∃ (fixed : {i // ¬keep i} → ℤ),
        (∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ)) ∧
        RelativePatchSliceConclusion s (fun i : {i // keep i} => N i.val)
          (fun u => f h (finiteSplitPoint keep u fixed)) target rankBound p) →
      let q := p + (Fintype.card X : ℝ) + 2
      let D := min rankBound ⌊p⌋₊
      ∃ (localLaw : Ω → FiniteProbabilityWeights (integerBox N))
        (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots X d w) (localForm : Ω → PolynomialSlots X d w)
        (retained : Finset Ω),
        d ≤ D ∧ d ≤ rankBound ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ outer.mass retained ∧
        (∀ h ∈ retained, RelativeReturnedFiberLaw keep N p (localLaw h)) ∧
        ∀ h ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw h).mean
          (fun t => (f h t.val - target) * (B.shearTransformedSlots hw
            ((localForm h).loweringAt (fun i => (t.val i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hnormalize⟩ := exists_varying_rank_fixed_patch_function s
  refine ⟨E, hE, ?_⟩
  intro Ω X _ _ _ _ outer productive hmass N keep _ hN p hp target ht
    rankBound f hf hreturn q D
  have hdata (h : Ω) (hh : h ∈ productive) :
      ∃ (d : ℕ) (Q : PolynomialPatch X s d)
        (law : FiniteProbabilityWeights (integerBox N)),
        d ≤ D ∧ (Q.kernel.lip : ℝ) ≤ Real.exp p ∧
        Real.exp (-p) ≤ law.mean
          (fun x => (f h x.val - target) * Q.value (fun i => (x.val i : ℝ))) ∧
        RelativeReturnedFiberLaw keep N p law := by
    obtain ⟨fixed, hfixed, hslice⟩ := hreturn h hh
    obtain ⟨d, Q, law, hd, _, hlip, hscore, r, hr, S, hlen, hlength, hlaw⟩ :=
      hslice.tighten_rank.exists_fiber_law_with_slice fixed hfixed (fun i => hN i.val)
    exact ⟨d, Q, law, hd, hlip, hscore, fixed, hfixed, r, hr, S, hlen, hlength, hlaw⟩
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  obtain ⟨h₀, hh₀⟩ := hne
  obtain ⟨ddefault, Qdefault, lawdefault, hddefault, hlipdefault, _, _⟩ := hdata h₀ hh₀
  have hall (h : Ω) : ∃ (d : ℕ) (Q : PolynomialPatch X s d)
      (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ D ∧ (Q.kernel.lip : ℝ) ≤ Real.exp p ∧
      (h ∈ productive → Real.exp (-p) ≤ law.mean
        (fun x => (f h x.val - target) * Q.value (fun i => (x.val i : ℝ)))) ∧
      (h ∈ productive → RelativeReturnedFiberLaw keep N p law) := by
    by_cases hh : h ∈ productive
    · obtain ⟨d, Q, law, hd, hlip, hscore, hslice⟩ := hdata h hh
      exact ⟨d, Q, law, hd, hlip, fun _ => hscore, fun _ => hslice⟩
    · exact ⟨ddefault, Qdefault, lawdefault, hddefault, hlipdefault,
        fun hmem => (hh hmem).elim, fun hmem => (hh hmem).elim⟩
  choose d patch localLaw hd hlip hpositive hslice using hall
  have hpq : p ≤ q := by dsimp only [q]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card X)]
  have hq : 0 ≤ q := hp.trans hpq
  have hD : (D : ℝ) ≤ q :=
    (Nat.cast_le.mpr (Nat.min_le_right rankBound ⌊p⌋₊)).trans ((Nat.floor_le hp).trans hpq)
  have hX : (Fintype.card X : ℝ) ≤ q := by dsimp only [q]; linarith
  let point := fun (_ : Ω) (x : integerBox N) => x.val
  let score := fun h (x : integerBox N) => f h x.val - target
  have hscore (h) (x : integerBox N) : |score h x| ≤ 1 := by
    dsimp only [score]
    obtain ⟨hf0, hf1⟩ := hf h x.val x.property
    exact abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨d', w, hw, Ψ, B, localForm, retained, hd', hpos, hws, hΨ, hB,
      hsub, hmass', hlocal⟩ :=
    hnormalize outer productive d patch D q hd hmass hq hD hX
      (fun h => (hlip h).trans (Real.exp_le_exp.mpr hpq)) localLaw point score hscore
      (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hpositive h hh))
  exact ⟨localLaw, d', w, hw, Ψ, B, localForm, retained, hd',
    hd'.trans (Nat.min_le_left _ _), hpos, hws, hΨ, hB, hsub, hmass',
    fun h hh => hslice h (hsub hh), hlocal⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

namespace AllocatedExternalCandidateSamplerFamily

variable [MeasurableSpace A.Path] [MeasurableSingletonClass A.Path]

theorem exists_normalized_retained_center_of_event
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [IsProbabilityMeasure μ]
    {V Y T : Type*} [Fintype T] {d : ℕ} {w : Fin d → ℕ}
    (hw : Monotone w) (Ψ : PatchKernel d) (Bslots : PolynomialSlots V d w)
    (localForm : A.Path → PolynomialSlots Y d w)
    (localLaw : A.Path → FiniteProbabilityWeights T)
    (point : A.Path → T → Y → ℤ) (score : A.Path → T → ℝ)
    (retained : Finset A.Path)
    (Allowed : A.Path → FiniteProbabilityWeights T → Prop)
    (hAllowed : ∀ z ∈ retained, Allowed z (localLaw z))
    {scoreThreshold : ℝ}
    (hscore : ∀ z : CoefficientTorus (K := LayerSamplerVariables G I n B) U × A.Path,
      z.2 ∈ retained → scoreThreshold ≤ (localLaw z.2).mean
        (fun t => score z.2 t * (Bslots.shearTransformedSlots hw
          ((localForm z.2).loweringAt (fun i => (point z.2 t i : ℝ)))).patchValue Ψ))
    (event : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U × A.Path))
    (hevent : MeasurableSet event)
    (hretained : ∀ z ∈ event, z.2 ∈ retained)
    (Recovery : CoefficientTorus (K := LayerSamplerVariables G I n B) U × A.Path → Prop)
    (hRecovery : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ A.law, Recovery z)
    {massThreshold : ℝ} (hmassPos : 0 < massThreshold)
    (hmass : massThreshold ≤ (centeredFiniteProbabilityMeasure μ A.law).real event) :
    ∃ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (selected : Finset A.Path),
      selected ⊆ retained ∧ massThreshold / 2 < (A center).law.mass selected ∧
      ∀ z ∈ selected, (center, z) ∈ event ∧ 0 < (A center).law.weight z ∧
        Recovery (center, z) ∧ Allowed z (localLaw z) ∧
        scoreThreshold ≤ (localLaw z).mean
          (fun t => score z t * (Bslots.shearTransformedSlots hw
            ((localForm z).loweringAt (fun i => (point z t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨center, selected, hmass', hselected⟩ :=
    exists_center_finite_good_event μ A.law A.weight_measurable event hevent
      Recovery hRecovery hmassPos hmass
  have hsub : selected ⊆ retained := fun z hz =>
    hretained (center, z) (hselected z hz).1
  refine ⟨center, selected, hsub, hmass', ?_⟩
  intro z hz
  obtain ⟨hevent', hpos, hrec⟩ := hselected z hz
  exact ⟨hevent', hpos, hrec, hAllowed z (hsub hz), hscore (center, z) (hsub hz)⟩

theorem exists_normalized_retained_center
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [IsProbabilityMeasure μ]
    {V Y T : Type*} [Fintype T] {d : ℕ} {w : Fin d → ℕ}
    (hw : Monotone w) (Ψ : PatchKernel d) (Bslots : PolynomialSlots V d w)
    (localForm : A.Path → PolynomialSlots Y d w)
    (localLaw : A.Path → FiniteProbabilityWeights T)
    (point : A.Path → T → Y → ℤ) (score : A.Path → T → ℝ)
    (retained : Finset A.Path)
    (Allowed : A.Path → FiniteProbabilityWeights T → Prop)
    (hAllowed : ∀ z ∈ retained, Allowed z (localLaw z))
    {scoreThreshold : ℝ}
    (hscore : ∀ z : CoefficientTorus (K := LayerSamplerVariables G I n B) U × A.Path,
      z.2 ∈ retained → scoreThreshold ≤ (localLaw z.2).mean
        (fun t => score z.2 t * (Bslots.shearTransformedSlots hw
          ((localForm z.2).loweringAt (fun i => (point z.2 t i : ℝ)))).patchValue Ψ))
    (Recovery : CoefficientTorus (K := LayerSamplerVariables G I n B) U × A.Path → Prop)
    (hRecovery : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ A.law, Recovery z)
    {massThreshold : ℝ} (hmassPos : 0 < massThreshold)
    (hmass : massThreshold ≤
      (centeredFiniteProbabilityMeasure μ A.law).real {z | z.2 ∈ retained}) :
    ∃ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (selected : Finset A.Path),
      selected ⊆ retained ∧ massThreshold / 2 < (A center).law.mass selected ∧
      ∀ z ∈ selected, 0 < (A center).law.weight z ∧ Recovery (center, z) ∧
        Allowed z (localLaw z) ∧ scoreThreshold ≤ (localLaw z).mean
          (fun t => score z t * (Bslots.shearTransformedSlots hw
            ((localForm z).loweringAt (fun i => (point z t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨center, selected, hsub, hmass', hselected⟩ :=
    A.exists_normalized_retained_center_of_event μ hw Ψ Bslots localForm localLaw point score
      retained Allowed hAllowed hscore {z | z.2 ∈ retained}
      ((Finset.measurableSet retained).preimage measurable_snd) (fun _ hz => hz)
      Recovery hRecovery hmassPos hmass
  exact ⟨center, selected, hsub, hmass', fun z hz => (hselected z hz).2⟩

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFinalScalarBudget_ready_requirements
    (m degree D Dmod cardVars : ℕ)
    {t childCost preparationP crtBudget qcap qnative cost : ℝ}
    (ht : 1 ≤ t) (hchild : childCost ≤ t)
    (hRank : (degree : ℝ) * D ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hCRTzero : 0 ≤ crtBudget) (hCRT : crtBudget ≤ t)
    (hPrepzero : 0 ≤ preparationP) (hPrep : preparationP ≤ t)
    (hNorm : (((childCost + (cardVars : ℝ) + 2) + 2) ^
      (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ t)
    (hcap : qcap ≤ t) (hnative : qnative ≤ t) (hcost : cost ≤ t) :
    let budget := preparedFinalScalarBudget m degree t
    1 ≤ budget ∧
      childCost + (degree : ℝ) * D ≤ budget ∧
      (Dmod : ℝ) ≤ budget ∧
      2048 * crtBudget ^ 3 +
        (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget ∧
      2 * (((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget ∧
      qcap ≤ budget ∧ qnative ≤ budget ∧ cost ≤ budget := by
  intro budget
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hcube : 0 ≤ 2048 * t ^ 3 := mul_nonneg (by norm_num) (pow_nonneg ht0 _)
  have hpower : 0 ≤ (t + 2) ^ (preparedIntegralBasisExponent m + 1) :=
    pow_nonneg (by linarith only [ht0]) _
  have hdegree : 0 ≤ (degree : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht0
  have htwo : 2 * t + 1 ≤ budget := by
    dsimp only [budget, preparedFinalScalarBudget]
    linarith only [hcube, hpower, hdegree]
  have htBudget : t ≤ budget := (by linarith only [ht0] : t ≤ 2 * t + 1).trans htwo
  have hmatrixBase : 2048 * t ^ 3 +
      (t + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget := by
    dsimp only [budget, preparedFinalScalarBudget]
    linarith only [ht0, hdegree]
  have hmatrix : 2048 * crtBudget ^ 3 +
      (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget := by
    apply le_trans _ hmatrixBase
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hCRTzero hCRT 3) (by norm_num))
      (pow_le_pow_left₀ (by linarith only [hPrepzero])
        (by linarith only [hPrep] : preparationP + 2 ≤ t + 2)
        (preparedIntegralBasisExponent m + 1))
  refine ⟨ht.trans htBudget, ?_, hDmod.trans htBudget, hmatrix, ?_,
    hcap.trans htBudget, hnative.trans htBudget, hcost.trans htBudget⟩
  · exact (by linarith only [hchild, hRank] : childCost + (degree : ℝ) * D ≤
      2 * t + 1).trans htwo
  · exact (by linarith only [hNorm] :
      2 * (((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤
          2 * t + 1).trans htwo

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeFinalEnvelope
    (degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount p : ℝ) : ℝ :=
  2 + (p + 2) ^ preparationPower + (p + 2) ^ requiredPower +
    ((p + 2) ^ basePower + 2) ^ inputPower + (⌈discount⁻¹⌉₊ : ℝ) +
      (p + 2) ^ basePower + degree * p

theorem preparedRelativeFinalEnvelope_bounds
    (degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) {p K : ℝ} (hp : 0 ≤ p)
    (hK : K ≤ ((p + 2) ^ basePower + 2) ^ inputPower) :
    let t := preparedRelativeFinalEnvelope degree basePower inputPower
      preparationPower requiredPower discount p
    1 ≤ t ∧
      max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1) ≤ t ∧
      K ≤ t ∧ discount⁻¹ ≤ t ∧ (p + 2) ^ basePower ≤ t ∧
      (degree : ℝ) * p ≤ t ∧ max 1 (max discount⁻¹ K) ≤ t := by
  intro t
  have hb : 0 ≤ p + 2 := by linarith only [hp]
  have hprep := pow_nonneg hb preparationPower
  have hreq := pow_nonneg hb requiredPower
  have hbase := pow_nonneg hb basePower
  have hinput := pow_nonneg (add_nonneg hbase (by norm_num : (0 : ℝ) ≤ 2)) inputPower
  have hceil := Nat.cast_nonneg (α := ℝ) ⌈discount⁻¹⌉₊
  have hdegree := mul_nonneg (Nat.cast_nonneg (α := ℝ) degree) hp
  have hinv : discount⁻¹ ≤ (⌈discount⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have ht : 1 ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hbase, hinput, hceil, hdegree]
  have hlate : max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1) ≤ t := by
    apply max_le <;> dsimp only [t, preparedRelativeFinalEnvelope] <;>
      linarith only [hprep, hreq, hbase, hinput, hceil, hdegree]
  have hKt : K ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hK, hprep, hreq, hbase, hceil, hdegree]
  have hit : discount⁻¹ ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hinv, hprep, hreq, hbase, hinput, hdegree]
  have hbt : (p + 2) ^ basePower ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hinput, hceil, hdegree]
  have hdt : (degree : ℝ) * p ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hbase, hinput, hceil]
  exact ⟨ht, hlate, hKt, hit, hbt, hdt, max_le ht (max_le hit hKt)⟩

theorem preparedRelativeFinalEnvelope_ready_requirements
    (m degree D Dmod cardVars basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) {p K childCost preparationP qcap qnative cost : ℝ}
    (hp : 0 ≤ p) (hK : K ≤ ((p + 2) ^ basePower + 2) ^ inputPower)
    (hD : (D : ℝ) ≤ p) (hDmod : (Dmod : ℝ) ≤ K)
    (hchild : childCost ≤ (p + 2) ^ basePower)
    (hPrepzero : 0 ≤ preparationP)
    (hPrep : preparationP ≤ max ((p + 2) ^ basePower)
      (max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1)))
    (hNorm : (((childCost + (cardVars : ℝ) + 2) + 2) ^
      (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤
        (p + 2) ^ basePower)
    (hcap : qcap ≤ K) (hnative : qnative ≤ K) (hcost : cost ≤ K) :
    let t := preparedRelativeFinalEnvelope degree basePower inputPower
      preparationPower requiredPower discount p
    let crtBudget := max 1 (max discount⁻¹ K)
    let budget := preparedFinalScalarBudget m degree t
    1 ≤ budget ∧
      childCost + (degree : ℝ) * D ≤ budget ∧
      (Dmod : ℝ) ≤ budget ∧
      2048 * crtBudget ^ 3 +
        (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget ∧
      2 * (((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget ∧
      qcap ≤ budget ∧ qnative ≤ budget ∧ cost ≤ budget := by
  intro t crtBudget budget
  obtain ⟨ht, hLateT, hKT, _, hBT, hDegreeT, hCRTT⟩ :=
    preparedRelativeFinalEnvelope_bounds degree basePower inputPower
      preparationPower requiredPower discount hp hK
  have hCRTzero : 0 ≤ crtBudget := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  exact preparedFinalScalarBudget_ready_requirements m degree D Dmod cardVars
    ht (hchild.trans hBT)
    ((mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg degree)).trans hDegreeT)
    (hDmod.trans hKT) hCRTzero hCRTT hPrepzero
    (hPrep.trans (max_le hBT hLateT)) (hNorm.trans hBT)
    (hcap.trans hKT) (hnative.trans hKT) (hcost.trans hKT)

theorem exists_preparedRelativeFinalExtraction_power
    (m degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) :
    ∃ passagePower : ℕ, 2 ≤ passagePower ∧ ∀ p : ℝ, 0 ≤ p →
      let t := preparedRelativeFinalEnvelope degree basePower inputPower
        preparationPower requiredPower discount p
      spatialPatchExtractionCost (recoveredKernelScalarBudget
        (preparedFinalScalarBudget m degree t)) ≤ (p + 2) ^ passagePower := by
  let X : Polynomial ℕ := Polynomial.X
  let t : Polynomial ℕ := 2 + (X + 2) ^ preparationPower + (X + 2) ^ requiredPower +
    ((X + 2) ^ basePower + 2) ^ inputPower + Polynomial.C ⌈discount⁻¹⌉₊ +
      (X + 2) ^ basePower + Polynomial.C degree * X
  let B : Polynomial ℕ := 2048 * t ^ 3 +
    (t + 2) ^ (preparedIntegralBasisExponent m + 1) + 2 * t + 1 + Polynomial.C degree * t
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_fixed_power_budget (20 * (8 * (B + 1) ^ 2 + 1) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, t, X, preparedRelativeFinalEnvelope, preparedFinalScalarBudget,
    recoveredKernelScalarBudget, spatialPatchExtractionCost, Polynomial.eval₂_pow] using hbound p hp

theorem preparedRelativeFinalExtraction_side_floor
    {X : Type*} (N : X → ℕ) {p extraction : ℝ} {C passagePower : ℕ}
    (hp : 0 ≤ p) (hC : C ≤ passagePower)
    (hextraction : extraction ≤ (p + 2) ^ C)
    (hN : ∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) :
    extraction ≤ (p + 2) ^ passagePower ∧
      ∀ i, Real.exp extraction ≤ (N i : ℝ) := by
  have h := hextraction.trans (pow_le_pow_right₀ (by linarith only [hp]) hC)
  exact ⟨h, fun i => (Real.exp_le_exp.mpr h).trans (hN i)⟩

end Erdos3.VectorPolynomial

end

end OAI
