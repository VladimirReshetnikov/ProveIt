import GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteLocalRules
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothAdmissibility

/-!
# Admissibility of ideal product sets

Separate the midpoint relation into the smooth profile and the individual
rough prime exponents. An integral quotient preserves the same condition
on the smooth profile.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem primeExponent_mul (p : HeightOneSpectrum (𝓞 K)) (I J : (Ideal (𝓞 K))⁰) :
    primeExponent p (I*J) = primeExponent p I + primeExponent p J := by
  have hp := Ideal.prime_of_isPrime p.ne_bot p.isPrime
  have hIJ : I.val * J.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp (I*J).property
  exact multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp hIJ)

theorem primeExponent_le_of_dvd (p : HeightOneSpectrum (𝓞 K)) {I J : (Ideal (𝓞 K))⁰}
    (h : I ∣ J) : primeExponent p I ≤ primeExponent p J := by
  obtain ⟨L,rfl⟩ := h
  rw [primeExponent_mul]
  exact Nat.le_add_right _ _

/-- Nonzero integral ideals are determined by their prime exponents. -/
theorem primeExponent_ext {I J : (Ideal (𝓞 K))⁰}
    (h : ∀ p : HeightOneSpectrum (𝓞 K), primeExponent p I = primeExponent p J) : I = J := by
  have hI : I.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hJ : J.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp J.property
  apply Subtype.ext
  calc
    I.val = ∏ᶠ p : HeightOneSpectrum (𝓞 K), p.maxPowDividing I.val :=
      (Ideal.finprod_heightOneSpectrum_factorization hI).symm
    _ = ∏ᶠ p : HeightOneSpectrum (𝓞 K), p.maxPowDividing J.val := by
      apply finprod_congr
      intro p
      rw [p.maxPowDividing_eq_pow_multiplicity hI, p.maxPowDividing_eq_pow_multiplicity hJ]
      exact congrArg (p.asIdeal ^ ·) (h p)
    _ = J.val := Ideal.finprod_heightOneSpectrum_factorization hJ

private theorem primeExponent_eq_zero_of_not_dvd (p : HeightOneSpectrum (𝓞 K)) (I : (Ideal (𝓞 K))⁰)
    (h : ¬ p.asIdeal ∣ I.val) : primeExponent p I = 0 := by
  rw [primeExponent_eq_iff]
  simpa only [pow_zero, zero_add, pow_one, one_dvd, true_and] using h

theorem primeExponent_smoothMultiplier_outside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : S → ℕ) {p : HeightOneSpectrum (𝓞 K)} (hp : p ∉ S) :
    primeExponent p (smoothMultiplier S e) = 0 := by
  classical
  apply primeExponent_eq_zero_of_not_dvd
  have hP := Ideal.prime_of_isPrime p.ne_bot p.isPrime
  have hprod : (smoothMultiplier S e).val = ∏ q : S, q.val.asIdeal ^ e q := by
    simp [smoothMultiplier, primeIdeal]
  rw [hprod]
  intro hd
  obtain ⟨q,_,hq⟩ := hP.exists_mem_finset_dvd hd
  have hq' := Ideal.prime_of_isPrime q.val.ne_bot q.val.isPrime
  have he := (hP.dvd_prime_iff_associated hq').mp (hP.dvd_of_dvd_pow hq)
  exact hp (HeightOneSpectrum.ext (associated_iff_eq.mp he) ▸ q.property)

/-- The in-set exponents of a smooth multiplier applied to a rough ideal
are exactly the prescribed smooth profile. -/
theorem primeExponent_mul_smooth_rough_inside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : S → ℕ) {J : (Ideal (𝓞 K))⁰} (hJ : J ∈ roughIdeals S) (p : S) :
    primeExponent p.val (smoothMultiplier S e * J) = e p := by
  apply (primeExponent_eq_iff _ _ _).mpr
  exact (mem_smoothMultiplier_image_iff S e _).mp ⟨J,hJ,rfl⟩ p

/-- Multiplying by a smooth ideal leaves all outside prime exponents unchanged. -/
theorem primeExponent_mul_smooth_rough_outside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e : S → ℕ) (J : (Ideal (𝓞 K))⁰) {p : HeightOneSpectrum (𝓞 K)} (hp : p ∉ S) :
    primeExponent p (smoothMultiplier S e * J) = primeExponent p J := by
  rw [primeExponent_mul, primeExponent_smoothMultiplier_outside S e hp, zero_add]

/-- A smooth admissible template remains admissible when combined with rough
factors satisfying independent progression-free outside rules. -/
theorem idealAdmissible_smoothTemplateProducts (S : Finset (HeightOneSpectrum (𝓞 K)))
    (integral : Bool) (T : Set (S → ℕ)) (hT : ProfileAdmissible integral T)
    (A : HeightOneSpectrum (𝓞 K) → Set ℕ) (hA : ∀ p ∉ S, ThreeAPFree (A p))
    {Q : Set (Ideal (𝓞 K))⁰} (hQ : Q ⊆ roughIdeals S)
    (hlocal : ∀ I ∈ Q, ∀ p ∉ S, primeExponent p I ∈ A p) :
    IdealAdmissible integral (⋃ e : T, (smoothMultiplier S e.val * ·) '' Q) := by
  intro I J L hI hJ hL he hdiv
  obtain ⟨a,I',ha,rfl⟩ := Set.mem_iUnion.mp hI
  obtain ⟨b,J',hb,rfl⟩ := Set.mem_iUnion.mp hJ
  obtain ⟨c,L',hc,rfl⟩ := Set.mem_iUnion.mp hL
  have hmid (p : HeightOneSpectrum (𝓞 K)) := (primeExponent_mul p _ _).symm.trans
    ((congrArg (primeExponent p) he).trans (primeExponent_mul p _ _))
  have hin (p : S) : a.val p + c.val p = b.val p + b.val p := by
    simpa only [primeExponent_mul_smooth_rough_inside _ _ (hQ ha),
      primeExponent_mul_smooth_rough_inside _ _ (hQ hb), primeExponent_mul_smooth_rough_inside _ _ (hQ hc)]
      using hmid p.val
  have hab : a.val = b.val := by
    apply hT a.property b.property c.property (funext hin)
    intro hi p
    simpa only [primeExponent_mul_smooth_rough_inside _ _ (hQ ha),
      primeExponent_mul_smooth_rough_inside _ _ (hQ hb)] using primeExponent_le_of_dvd p.val (hdiv hi)
  apply primeExponent_ext
  intro p
  by_cases hp : p ∈ S
  · let q : S := ⟨p,hp⟩
    calc
      primeExponent p (smoothMultiplier S a.val * I') = a.val q :=
        primeExponent_mul_smooth_rough_inside S a.val (hQ ha) q
      _ = b.val q := congrArg (fun e : S → ℕ ↦ e q) hab
      _ = primeExponent p (smoothMultiplier S b.val * J') :=
        (primeExponent_mul_smooth_rough_inside S b.val (hQ hb) q).symm
  · rw [primeExponent_mul_smooth_rough_outside _ _ _ hp, primeExponent_mul_smooth_rough_outside _ _ _ hp]
    apply hA p hp (hlocal I' ha p hp) (hlocal J' hb p hp) (hlocal L' hc p hp)
    simpa only [primeExponent_mul_smooth_rough_outside _ _ _ hp] using hmid p

end GRHArticle.ProgressionFree.NumberFieldIdeals
