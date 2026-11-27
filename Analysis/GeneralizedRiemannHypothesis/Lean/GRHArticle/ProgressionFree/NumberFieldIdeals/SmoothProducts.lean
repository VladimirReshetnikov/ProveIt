import GRHArticle.ProgressionFree.NumberFieldIdeals.DisjointProducts
import GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteExponentProducts

/-!
# Arbitrary smooth templates in number fields

A smooth ideal is specified by its tuple of exponents on the finite
prime set. Distinct tuples have disjoint product sets on rough factors.
The product of the geometric series controls every subset of tuples.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The smooth ideal with the prescribed exponents and no other factors. -/
noncomputable def smoothMultiplier (S : Finset (HeightOneSpectrum (𝓞 K))) (e : S → ℕ) :
    (Ideal (𝓞 K))⁰ := ∏ p : S, primeIdeal p.val ^ e p

private theorem one_mem_rough (S : Finset (HeightOneSpectrum (𝓞 K))) :
    1 ∈ roughIdeals S := by
  intro p _ h
  rw [nonZeroDivisors_dvd_iff_dvd_coe] at h
  exact (Ideal.prime_of_isPrime p.ne_bot p.isPrime).not_unit (isUnit_of_dvd_one h)

/-- Multiplication by a smooth ideal specifies exactly the prime powers
observed on its finite prime set. -/
theorem mem_smoothMultiplier_image_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (e : S → ℕ)
    (I : (Ideal (𝓞 K))⁰) :
    I ∈ (smoothMultiplier S e * ·) '' roughIdeals S ↔
      ∀ p : S, p.val.asIdeal ^ e p ∣ I.val ∧ ¬ p.val.asIdeal ^ (e p+1) ∣ I.val := by
  classical
  let v (p : HeightOneSpectrum (𝓞 K)) := if hp : p ∈ S then e ⟨p,hp⟩ else 0
  have he : smoothMultiplier S e = ∏ p ∈ S, primeIdeal p ^ v p := by
    rw [← prod_coe_sort]
    exact prod_congr rfl fun p _ ↦ by simp [v,p.property]
  rw [he,mem_roughIdeals_mul_image_iff]
  constructor
  · intro h p
    simpa [v,p.property] using h p p.property
  · intro h p hp
    simpa [v,hp] using h ⟨p,hp⟩

private theorem equal_of_two_templates {S : Finset (HeightOneSpectrum (𝓞 K))} {e f : S → ℕ}
    {I : (Ideal (𝓞 K))⁰} (he : I ∈ (smoothMultiplier S e * ·) '' roughIdeals S)
    (hf : I ∈ (smoothMultiplier S f * ·) '' roughIdeals S) : e = f := by
  have hle {a b : S → ℕ} (ha : I ∈ (smoothMultiplier S a * ·) '' roughIdeals S)
      (hb : I ∈ (smoothMultiplier S b * ·) '' roughIdeals S) (p : S) : b p ≤ a p := by
    by_contra! hlt
    exact ((mem_smoothMultiplier_image_iff S a I).mp ha p).2
      ((pow_dvd_pow p.val.asIdeal hlt).trans ((mem_smoothMultiplier_image_iff S b I).mp hb p).1)
  exact funext fun p ↦ le_antisymm (hle hf he p) (hle he hf p)

theorem smoothMultiplier_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (smoothMultiplier S) := by
  have hm (e : S → ℕ) : smoothMultiplier S e ∈ (smoothMultiplier S e * ·) '' roughIdeals S :=
    ⟨1,one_mem_rough S,mul_one _⟩
  intro e f hef
  exact equal_of_two_templates (hm e) (hef.symm ▸ hm f)

theorem smoothMultiplier_invNorm (S : Finset (HeightOneSpectrum (𝓞 K))) (e : S → ℕ) :
    (absNorm (smoothMultiplier S e).val : ℝ)⁻¹ =
      ∏ p : S, (absNorm p.val.asIdeal : ℝ)⁻¹ ^ e p := by
  simp [smoothMultiplier,primeIdeal,Finset.prod_inv_distrib]

/-- The smooth reciprocal-norm series sums to the inverse rough density factor. -/
theorem hasSum_smoothMultiplier_invNorm (S : Finset (HeightOneSpectrum (𝓞 K))) :
    HasSum (fun e : S → ℕ ↦ (absNorm (smoothMultiplier S e).val : ℝ)⁻¹)
      (∏ p : S, (1-(absNorm p.val.asIdeal : ℝ)⁻¹)⁻¹) := by
  simp_rw [smoothMultiplier_invNorm]
  apply hasSum_finiteExponentProduct
  · intro p
    have h0 : 0 < absNorm p.val.asIdeal := absNorm_pos_of_nonZeroDivisors (primeIdeal p.val)
    have h1 : absNorm p.val.asIdeal ≠ 1 := fun h ↦ p.val.isPrime.ne_top (absNorm_eq_one_iff.mp h)
    have ht : (1:ℝ) < absNorm p.val.asIdeal := by exact_mod_cast (by omega : 1 < absNorm p.val.asIdeal)
    exact hasSum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ ht)
  · intros; positivity

/-- Any subset of smooth exponent tuples can be combined with a fixed
rough rule of known natural density, as in the article's product-set lemma. -/
theorem hasNaturalDensity_smoothTemplateProducts (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Set (S → ℕ)) {Q : Set (Ideal (𝓞 K))⁰} {d : ℝ} (hQ : Q ⊆ roughIdeals S)
    (hd : HasNaturalDensity Q d) :
    HasNaturalDensity (⋃ e : T, (smoothMultiplier S e.val * ·) '' Q)
      (d * ∑' e : T, (absNorm (smoothMultiplier S e.val).val : ℝ)⁻¹) := by
  rw [← tsum_mul_left]
  apply hasNaturalDensity_disjointMulImages (fun e : T ↦ smoothMultiplier S e.val)
    ((smoothMultiplier_injective S).comp Subtype.val_injective) (fun _ ↦ Q) (fun _ ↦ hd)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro I hi hj
    exact hij (Subtype.ext (equal_of_two_templates (Set.image_mono hQ hi) (Set.image_mono hQ hj)))
  · exact (hasSum_smoothMultiplier_invNorm S).summable.comp_injective Subtype.val_injective

end GRHArticle.ProgressionFree.NumberFieldIdeals
