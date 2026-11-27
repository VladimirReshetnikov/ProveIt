import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughFibers

/-!
# Canonical rough and smooth factors of a nonzero ideal

Existence and uniqueness of the split give canonical factors and readback
lemmas for composing a rough ideal with a smooth ideal.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The part of a nonzero ideal with no prime factors in `S`. -/
noncomputable def idealRoughPart (S : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (𝓞 K))⁰) :
    (Ideal (𝓞 K))⁰ := (exists_rough_mul_smooth S I).choose

/-- The part of a nonzero ideal with all prime factors in `S`. -/
noncomputable def idealSmoothPart (S : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (𝓞 K))⁰) :
    (Ideal (𝓞 K))⁰ := (exists_rough_mul_smooth S I).choose_spec.2.choose

theorem idealRoughPart_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (𝓞 K))⁰) :
    idealRoughPart S I ∈ roughIdeals S := (exists_rough_mul_smooth S I).choose_spec.1

theorem idealSmoothPart_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (𝓞 K))⁰) :
    idealSmoothPart S I ∈ Set.range (smoothMultiplier S) :=
  (exists_rough_mul_smooth S I).choose_spec.2.choose_spec.1

theorem idealRoughPart_mul_smoothPart (S : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (𝓞 K))⁰) :
    idealRoughPart S I * idealSmoothPart S I = I := (exists_rough_mul_smooth S I).choose_spec.2.choose_spec.2

theorem idealRoughPart_mul_of_parts (S : Finset (HeightOneSpectrum (𝓞 K))) {g J : (Ideal (𝓞 K))⁰}
    (hg : g ∈ roughIdeals S) (hJ : J ∈ Set.range (smoothMultiplier S)) :
    idealRoughPart S (g*J) = g :=
  (eq_of_rough_mul_smooth_eq S (idealRoughPart_mem S _) hg (idealSmoothPart_mem S _) hJ
    (idealRoughPart_mul_smoothPart S _)).1

theorem idealSmoothPart_mul_of_parts (S : Finset (HeightOneSpectrum (𝓞 K))) {g J : (Ideal (𝓞 K))⁰}
    (hg : g ∈ roughIdeals S) (hJ : J ∈ Set.range (smoothMultiplier S)) :
    idealSmoothPart S (g*J) = J :=
  (eq_of_rough_mul_smooth_eq S (idealRoughPart_mem S _) hg (idealSmoothPart_mem S _) hJ
    (idealRoughPart_mul_smoothPart S _)).2

/-- The smooth cofactors of a set in the fiber over a fixed rough factor. -/
def idealSmoothFiber (S : Finset (HeightOneSpectrum (𝓞 K))) (A : Set (Ideal (𝓞 K))⁰)
    (g : (Ideal (𝓞 K))⁰) : Set (Ideal (𝓞 K))⁰ :=
  {J | J ∈ Set.range (smoothMultiplier S) ∧ g*J ∈ A}

omit [NumberField K] in
theorem idealSmoothFiber_subset_range (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : Set (Ideal (𝓞 K))⁰) (g : (Ideal (𝓞 K))⁰) :
    idealSmoothFiber S A g ⊆ Set.range (smoothMultiplier S) := fun _ h ↦ h.1

theorem idealAdmissible_idealSmoothFiber (S : Finset (HeightOneSpectrum (𝓞 K)))
    {integral : Bool} {A : Set (Ideal (𝓞 K))⁰} (hA : IdealAdmissible integral A)
    (g : (Ideal (𝓞 K))⁰) : IdealAdmissible integral (idealSmoothFiber S A g) := by
  intro a b c ha hb hc
  exact idealAdmissible_mul_preimage hA g ha.2 hb.2 hc.2

theorem idealSmoothPart_mem_idealSmoothFiber (S : Finset (HeightOneSpectrum (𝓞 K)))
    {A : Set (Ideal (𝓞 K))⁰} {I : (Ideal (𝓞 K))⁰} (hI : I ∈ A) :
    idealSmoothPart S I ∈ idealSmoothFiber S A (idealRoughPart S I) :=
  ⟨idealSmoothPart_mem S I, (idealRoughPart_mul_smoothPart S I).symm ▸ hI⟩

end GRHArticle.ProgressionFree.NumberFieldIdeals
