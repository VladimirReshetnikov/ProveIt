import GRHArticle.ProgressionFree.NumberFieldIdeals.ProductAdmissibility

/-!
# Smooth and rough ideal fibers

The smooth part and rough part are unique. With squarefree rough factors,
any progression in a union of fibers belongs to a single fiber, even
when the smooth template depends on the rough factor.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem primeExponent_rough_inside (S : Finset (HeightOneSpectrum (𝓞 K)))
    {g : (Ideal (𝓞 K))⁰} (hg : g ∈ roughIdeals S) {p : HeightOneSpectrum (𝓞 K)} (hp : p ∈ S) :
    primeExponent p g = 0 := by
  simp only [primeExponent_eq_iff, pow_zero, one_dvd, zero_add, pow_one, true_and]
  exact fun h ↦ hg p hp ((nonZeroDivisors_dvd_iff_dvd_coe).mpr h)

theorem primeExponent_smooth_outside (S : Finset (HeightOneSpectrum (𝓞 K)))
    {J : (Ideal (𝓞 K))⁰} (hJ : J ∈ Set.range (smoothMultiplier S))
    {p : HeightOneSpectrum (𝓞 K)} (hp : p ∉ S) : primeExponent p J = 0 := by
  obtain ⟨e,rfl⟩ := hJ
  exact primeExponent_smoothMultiplier_outside S e hp

/-- Every ideal has a factorization with rough part `g` and smooth part `J`. -/
theorem exists_rough_mul_smooth (S : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (𝓞 K))⁰) :
    ∃ g ∈ roughIdeals S, ∃ J ∈ Set.range (smoothMultiplier S), g * J = I := by
  let e (p : S) := primeExponent p.val I
  have h : I ∈ (smoothMultiplier S e * ·) '' roughIdeals S :=
    (mem_smoothMultiplier_image_iff S e I).mpr fun p ↦ (primeExponent_eq_iff p.val I (e p)).mp rfl
  obtain ⟨g,hg,he⟩ := h
  exact ⟨g,hg,smoothMultiplier S e,Set.mem_range_self e,(mul_comm _ _).trans he⟩

/-- Uniqueness of smooth and rough factors in a nonzero ideal. -/
theorem eq_of_rough_mul_smooth_eq (S : Finset (HeightOneSpectrum (𝓞 K)))
    {g h J L : (Ideal (𝓞 K))⁰} (hg : g ∈ roughIdeals S) (hh : h ∈ roughIdeals S)
    (hJ : J ∈ Set.range (smoothMultiplier S)) (hL : L ∈ Set.range (smoothMultiplier S))
    (he : g*J = h*L) : g = h ∧ J = L := by
  have hgh : g = h := by
    apply primeExponent_ext
    intro p
    by_cases hp : p ∈ S
    · rw [primeExponent_rough_inside S hg hp, primeExponent_rough_inside S hh hp]
    · simpa only [primeExponent_mul, primeExponent_smooth_outside S hJ hp,
        primeExponent_smooth_outside S hL hp, add_zero] using congrArg (primeExponent p) he
  exact ⟨hgh, mul_left_cancel (hgh ▸ he)⟩

/-- Admissibility can be tested inside any multiplicative fiber. -/
theorem idealAdmissible_mul_preimage {integral : Bool} {A : Set (Ideal (𝓞 K))⁰}
    (hA : IdealAdmissible integral A) (g : (Ideal (𝓞 K))⁰) :
    IdealAdmissible integral ((g * ·) ⁻¹' A) := by
  intro a b c ha hb hc he hd
  apply mul_left_cancel (a := g)
  apply hA ha hb hc
  · calc
      (g*a)*(g*c) = (g*g)*(a*c) := by ac_rfl
      _ = (g*g)*(b*b) := congrArg ((g*g) * ·) he
      _ = (g*b)*(g*b) := by ac_rfl
  · intro hi
    obtain ⟨r,hr⟩ := hd hi
    exact ⟨r, by rw [hr,mul_assoc]⟩

/-- A union of smooth templates indexed by rough factors. -/
def roughFiberUnion (Q : Set (Ideal (𝓞 K))⁰) (T : (Ideal (𝓞 K))⁰ → Set (Ideal (𝓞 K))⁰) :
    Set (Ideal (𝓞 K))⁰ := ⋃ g : Q, (g.val * ·) '' T g.val

/-- Squarefree rough factors separate all forbidden progressions into
individual fibers, for both ratio conventions. -/
theorem idealAdmissible_roughFiberUnion (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {Q : Set (Ideal (𝓞 K))⁰}
    (hQ : Q ⊆ roughIdeals S)
    (hQsf : ∀ g ∈ Q, ∀ p ∉ S, primeExponent p g ≤ 1)
    (T : (Ideal (𝓞 K))⁰ → Set (Ideal (𝓞 K))⁰)
    (hT : ∀ g ∈ Q, T g ⊆ Set.range (smoothMultiplier S))
    (hTf : ∀ g ∈ Q, IdealAdmissible integral (T g)) :
    IdealAdmissible integral (roughFiberUnion (K := K) Q T) := by
  intro I J L hI hJ hL he hd
  obtain ⟨⟨g,hg⟩, a, ha, rfl⟩ := Set.mem_iUnion.mp hI
  obtain ⟨⟨h,hh⟩, b, hb, rfl⟩ := Set.mem_iUnion.mp hJ
  obtain ⟨⟨l,hl⟩, c, hc, rfl⟩ := Set.mem_iUnion.mp hL
  have hexp (p : HeightOneSpectrum (𝓞 K)) :
      primeExponent p g = primeExponent p h ∧ primeExponent p h = primeExponent p l := by
    by_cases hp : p ∈ S
    · rw [primeExponent_rough_inside S (hQ hg) hp, primeExponent_rough_inside S (hQ hh) hp,
        primeExponent_rough_inside S (hQ hl) hp]
      exact ⟨rfl,rfl⟩
    · have hm := congrArg (primeExponent p) he
      simp only [primeExponent_mul, primeExponent_smooth_outside S (hT g hg ha) hp,
        primeExponent_smooth_outside S (hT h hh hb) hp,
        primeExponent_smooth_outside S (hT l hl hc) hp, add_zero] at hm
      change primeExponent p g + primeExponent p l = primeExponent p h + primeExponent p h at hm
      have hg' := hQsf g hg p hp
      have hh' := hQsf h hh p hp
      have hl' := hQsf l hl p hp
      omega
  have egh : g = h := primeExponent_ext fun p ↦ (hexp p).1
  have ehl : h = l := primeExponent_ext fun p ↦ (hexp p).2
  subst l
  subst h
  apply congrArg (g * ·)
  apply hTf g hg ha hb hc
  · apply mul_left_cancel (a := g*g)
    calc
      (g*g)*(a*c) = (g*a)*(g*c) := by ac_rfl
      _ = (g*b)*(g*b) := he
      _ = (g*g)*(b*b) := by ac_rfl
  · intro hi
    obtain ⟨r, hr⟩ := hd hi
    exact ⟨r,mul_left_cancel (by simpa only [mul_assoc] using hr)⟩

end GRHArticle.ProgressionFree.NumberFieldIdeals
