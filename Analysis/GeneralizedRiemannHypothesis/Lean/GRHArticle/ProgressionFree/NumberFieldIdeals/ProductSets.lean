import GRHArticle.ProgressionFree.NumberFieldIdeals.ProductSetDensity
import GRHArticle.ProgressionFree.NumberFieldIdeals.ProductAdmissibility

/-!
# Admissibility of the article's number-field product sets

The smooth set may be given directly as a set of ideals. Its exponent
profiles determine the smooth components, while the exterior
progression-free rules force a common rough component.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The admissibility assertion of `gpi:lem:product` under either ratio
convention. The exterior rules may be arbitrary progression-free sets of
exponents here, including ones of zero geometric mass. -/
theorem idealProductSet_admissible (S : Finset (HeightOneSpectrum (𝓞 K))) (integral : Bool)
    (F : Set (Ideal (𝓞 K))⁰) (hF : F ⊆ Set.range (smoothMultiplier S)) (hf : IdealAdmissible integral F)
    (A : HeightOneSpectrum (𝓞 K) → Set ℕ) (hA : ∀ p ∉ S, ThreeAPFree (A p)) :
    IdealAdmissible integral (⋃ J : F, (J.val * ·) '' idealRoughLocalRule S A) := by
  let T := (smoothMultiplier S) ⁻¹' F
  have him : smoothMultiplier S '' T ⊆ F := by
    rintro _ ⟨e,he,rfl⟩; exact he
  have hT : ProfileAdmissible integral T := (idealAdmissible_smoothMultiplier_image_iff S integral T).mp
    (fun _ _ _ ha hb hc ↦ hf (him ha) (him hb) (him hc))
  have hsub : (⋃ J : F, (J.val * ·) '' idealRoughLocalRule S A) ⊆
      ⋃ e : T, (smoothMultiplier S e.val * ·) '' idealRoughLocalRule S A := by
    intro I hI
    obtain ⟨J,hJ⟩ := Set.mem_iUnion.mp hI
    obtain ⟨e,he⟩ := hF J.property
    exact Set.mem_iUnion.mpr ⟨⟨e,show smoothMultiplier S e ∈ F from he.symm ▸ J.property⟩,by simpa only [he] using hJ⟩
  have h := idealAdmissible_smoothTemplateProducts S integral T hT A hA
    (Q := idealRoughLocalRule S A) (fun _ h ↦ h.1) (fun _ h ↦ h.2)
  exact fun _ _ _ ha hb hc ↦ h (hsub ha) (hsub hb) (hsub hc)

end GRHArticle.ProgressionFree.NumberFieldIdeals
