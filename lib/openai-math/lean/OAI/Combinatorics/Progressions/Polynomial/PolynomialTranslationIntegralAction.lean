import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationRealBCHCoordinates

namespace OAI

section

namespace Erdos3.PolynomialTranslationGroup

open MvPolynomial
variable {σ : Type*}

noncomputable def fromInteger :
    PolynomialTranslationGroupOver ℤ σ →* PolynomialTranslationGroup σ :=
  PolynomialTranslationGroupOver.rationalEquiv.symm.toMonoidHom.comp
    (PolynomialTranslationGroupOver.map (Int.castRingHom ℚ))

@[simp] theorem fromInteger_base (g : PolynomialTranslationGroupOver ℤ σ) (i : σ) :
    (fromInteger g).base i = (g.base i : ℚ) := rfl

@[simp] theorem fromInteger_polynomial (g : PolynomialTranslationGroupOver ℤ σ) :
    (fromInteger g).polynomial = MvPolynomial.map (Int.castRingHom ℚ) g.polynomial := rfl

noncomputable def integralGroup : Subgroup (PolynomialTranslationGroup σ) := fromInteger.range

theorem mem_integralGroup_iff (g : PolynomialTranslationGroup σ) :
    g ∈ integralGroup ↔ (∀ i, ∃ z : ℤ, g.base i = (z : ℚ)) ∧
      g.polynomial ∈ integerCoefficientPolynomials σ := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨fun i => ⟨h.base i, rfl⟩, ⟨h.polynomial, rfl⟩⟩
  · rintro ⟨hb, P, hP⟩
    choose b hb using hb
    refine ⟨⟨b, P⟩, ?_⟩
    apply PolynomialTranslationGroup.ext
    · exact (funext hb).symm
    · exact hP

theorem integralGroup_action_integral {g : PolynomialTranslationGroup σ}
    (hg : g ∈ integralGroup) (i : σ ⊕ Unit) :
    actionMonoidHom g (X i) ∈ integerCoefficientPolynomials (σ ⊕ Unit) := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨PolynomialTranslationGroupOver.actionHom h (X i), ?_⟩
  change MvPolynomial.map (Int.castRingHom ℚ)
    (PolynomialTranslationGroupOver.actionHom h (X i)) = _
  rw [PolynomialTranslationGroupOver.map_actionHom, MvPolynomial.map_X]
  rfl

theorem mem_integralGroup_iff_action (g : PolynomialTranslationGroup σ) :
    g ∈ integralGroup ↔
      ∀ i, actionMonoidHom g (X i) ∈ integerCoefficientPolynomials (σ ⊕ Unit) := by
  refine ⟨fun hg => integralGroup_action_integral hg, ?_⟩
  intro hg
  apply (mem_integralGroup_iff g).mpr
  have hb : ∀ i, ∃ z : ℤ, g.base i = (z : ℚ) := by
    intro i
    apply (integerCoefficientPolynomials_C_iff (σ := σ ⊕ Unit) (g.base i)).mp
    have h := (integerCoefficientPolynomials (σ ⊕ Unit)).sub_mem
      (hg (Sum.inl i)) (integerCoefficientPolynomials_X (Sum.inl i))
    change actionHom g (X (Sum.inl i)) - X (Sum.inl i) ∈ _ at h
    simpa only [actionHom_X_inl, add_sub_cancel_left] using h
  refine ⟨hb, ?_⟩
  apply (integerCoefficientPolynomials_translate_iff g.base hb g.polynomial).mp
  apply (integerCoefficientPolynomials_rename_iff Sum.inl Sum.inl_injective _).mp
  have h := (integerCoefficientPolynomials (σ ⊕ Unit)).sub_mem
    (hg (Sum.inr ())) (integerCoefficientPolynomials_X (Sum.inr ()))
  change actionHom g (X (Sum.inr ())) - X (Sum.inr ()) ∈ _ at h
  simpa only [actionHom_X_inr, add_sub_cancel_left] using h

theorem mem_integralGroup_iff_action_and_inverse (g : PolynomialTranslationGroup σ) :
    g ∈ integralGroup ↔
      (∀ i, actionMonoidHom g (X i) ∈ integerCoefficientPolynomials (σ ⊕ Unit)) ∧
      (∀ i, (actionMonoidHom g).symm (X i) ∈ integerCoefficientPolynomials (σ ⊕ Unit)) := by
  constructor
  · intro hg
    refine ⟨integralGroup_action_integral hg, ?_⟩
    intro i
    have h := integralGroup_action_integral (integralGroup.inv_mem hg) i
    simpa only [map_inv, AlgEquiv.aut_inv] using h
  · intro h
    exact (mem_integralGroup_iff_action g).mpr h.1

end Erdos3.PolynomialTranslationGroup

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem bchTranslationHom_mem_integralGroup_iff (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).Group) :
    bchTranslationHom w d hw hwd g ∈ PolynomialTranslationGroup.integralGroup ↔
      weightedShearGroupHom w d hwd g ∈ integerWeightedLoweringSubgroup (shearWeight w d) := by
  rw [PolynomialTranslationGroup.mem_integralGroup_iff_action, bchTranslationHom_action]
  rfl

theorem bchTranslation_integral_comap (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    PolynomialTranslationGroup.integralGroup.comap (bchTranslationHom w d hw hwd) =
      (integerWeightedLoweringSubgroup (shearWeight w d)).comap (weightedShearGroupHom w d hwd) := by
  ext g
  exact bchTranslationHom_mem_integralGroup_iff w d hw hwd g

end Erdos3.PolynomialTranslationLie

end

end OAI
