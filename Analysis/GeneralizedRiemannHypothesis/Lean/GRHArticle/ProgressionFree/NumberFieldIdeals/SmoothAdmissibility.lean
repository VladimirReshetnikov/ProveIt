import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothProducts
import GRHArticle.ProgressionFree.NumberFieldIdeals.GreedyPredecessors

/-!
# Progression conventions for ideals and smooth exponent profiles

Multiplicative midpoints are additive midpoints of exponent profiles.
An integral quotient is precisely a coordinatewise nonnegative step.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- Admissibility of nonzero integral ideals for the chosen ratio convention.
The middle ideal is divisible by the first in the integral convention. -/
def IdealAdmissible (integral : Bool) (A : Set (Ideal (𝓞 K))⁰) : Prop :=
  ∀ ⦃a b c⦄, a ∈ A → b ∈ A → c ∈ A → a*c = b*b → (integral = true → a ∣ b) → a = b

omit [NumberField K] in
theorem idealAdmissible_fractional_iff (A : Set (Ideal (𝓞 K))⁰) :
    IdealAdmissible false A ↔ ThreeGPFree A := by
  constructor
  · intro h _ ha _ hb _ hc he
    exact h ha hb hc he (by simp)
  · intro h _ _ _ ha hb hc he _
    exact h ha hb hc he

/-- The integral convention excludes precisely progressions formed by
repeated multiplication by a nonidentity nonzero integral ideal. -/
theorem idealAdmissible_integral_iff (A : Set (Ideal (𝓞 K))⁰) :
    IdealAdmissible true A ↔ ∀ a r : (Ideal (𝓞 K))⁰,
      r ≠ 1 → a ∈ A → a*r ∈ A → a*r*r ∉ A := by
  constructor
  · intro h a r hr ha hb hc
    have he := h ha hb hc (by ac_rfl) (fun _ ↦ dvd_mul_right a r)
    exact hr (mul_left_cancel (by simpa only [mul_one] using he.symm : a*r = a*1))
  · intro h a b c ha hb hc he hd
    obtain ⟨r,rfl⟩ := hd rfl
    have hcr : c = a*r*r := mul_left_cancel (he.trans (by ac_rfl))
    by_cases hr : r = 1
    · simp [hr]
    · exact (h a r hr ha hb (hcr ▸ hc)).elim

/-- Additive midpoint formulation with a pointwise nonnegative step in the
integral convention. -/
def ProfileAdmissible {ι : Type*} (integral : Bool) (T : Set (ι → ℕ)) : Prop :=
  ∀ ⦃a b c⦄, a ∈ T → b ∈ T → c ∈ T → a+c = b+b → (integral = true → a ≤ b) → a = b

omit [NumberField K] in
theorem smoothMultiplier_add (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : S → ℕ) :
    smoothMultiplier S (a+b) = smoothMultiplier S a * smoothMultiplier S b := by
  simp only [smoothMultiplier, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

private theorem smoothMultiplier_mem_ownCyl (S : Finset (HeightOneSpectrum (𝓞 K))) (e : S → ℕ) :
    smoothMultiplier S e ∈ (smoothMultiplier S e * ·) '' roughIdeals S := by
  refine ⟨1, ?_, mul_one _⟩
  intro p _ hp
  rw [nonZeroDivisors_dvd_iff_dvd_coe] at hp
  exact (Ideal.prime_of_isPrime p.ne_bot p.isPrime).not_unit (isUnit_of_dvd_one hp)

/-- Divisibility among smooth ideals agrees with pointwise comparison of
their exponent profiles. -/
theorem smoothMultiplier_dvd_iff (S : Finset (HeightOneSpectrum (𝓞 K))) {a b : S → ℕ} :
    smoothMultiplier S a ∣ smoothMultiplier S b ↔ a ≤ b := by
  constructor
  · intro h p
    rw [nonZeroDivisors_dvd_iff_dvd_coe] at h
    obtain ⟨ha,_⟩ := (mem_smoothMultiplier_image_iff S a _).mp (smoothMultiplier_mem_ownCyl S a) p
    obtain ⟨_,hb⟩ := (mem_smoothMultiplier_image_iff S b _).mp (smoothMultiplier_mem_ownCyl S b) p
    by_contra! hlt
    exact hb ((pow_dvd_pow p.val.asIdeal hlt).trans (ha.trans h))
  · intro h
    refine ⟨smoothMultiplier S (fun p ↦ b p - a p), ?_⟩
    rw [← smoothMultiplier_add]
    congr 1
    funext p
    change b p = a p + (b p-a p)
    have hp : a p ≤ b p := h p
    omega

/-- Both progression conventions transport exactly along the smooth
exponent parameterization. -/
theorem idealAdmissible_smoothMultiplier_image_iff
    (S : Finset (HeightOneSpectrum (𝓞 K))) (integral : Bool) (T : Set (S → ℕ)) :
    IdealAdmissible integral (smoothMultiplier S '' T) ↔ ProfileAdmissible integral T := by
  constructor
  · intro h a b c ha hb hc he hd
    apply smoothMultiplier_injective S
    apply h (Set.mem_image_of_mem _ ha) (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc)
    · simpa only [smoothMultiplier_add] using congrArg (smoothMultiplier S) he
    · exact fun hi ↦ (smoothMultiplier_dvd_iff S).mpr (hd hi)
  · intro h I J L hI hJ hL he hd
    obtain ⟨a,ha,rfl⟩ := hI
    obtain ⟨b,hb,rfl⟩ := hJ
    obtain ⟨c,hc,rfl⟩ := hL
    apply congrArg (smoothMultiplier S)
    apply h ha hb hc
    · apply smoothMultiplier_injective S
      simpa only [smoothMultiplier_add] using he
    · exact fun hi ↦ (smoothMultiplier_dvd_iff S).mp (hd hi)

/-- The absolute norm of the smooth ideal with a given exponent profile. -/
noncomputable def profileNorm (S : Finset (HeightOneSpectrum (𝓞 K))) (e : S → ℕ) : ℕ :=
  absNorm (smoothMultiplier S e).val

theorem profileNorm_eq_prod (S : Finset (HeightOneSpectrum (𝓞 K))) (e : S → ℕ) :
    profileNorm S e = ∏ p : S, absNorm p.val.asIdeal ^ e p := by
  simp [profileNorm, smoothMultiplier, primeIdeal]

theorem primeIdeal_norm_gt_one (p : HeightOneSpectrum (𝓞 K)) : 1 < absNorm p.asIdeal := by
  have h₀ : 0 < absNorm p.asIdeal := absNorm_pos_of_nonZeroDivisors (primeIdeal p)
  have h₁ : absNorm p.asIdeal ≠ 1 := fun h ↦ p.isPrime.ne_top (absNorm_eq_one_iff.mp h)
  omega

theorem profileNorm_strict_of_le (S : Finset (HeightOneSpectrum (𝓞 K))) {a b : S → ℕ}
    (h : a ≤ b) (hne : a ≠ b) : profileNorm S a < profileNorm S b := by
  classical
  obtain ⟨p,hp⟩ : ∃ p : S, a p < b p := by
    by_contra! hn
    exact hne (funext fun p ↦ le_antisymm (h p) (hn p))
  rw [profileNorm_eq_prod, profileNorm_eq_prod]
  apply Finset.prod_lt_prod
  · exact fun q _ ↦ pow_pos (zero_lt_one.trans (primeIdeal_norm_gt_one q.val)) _
  · exact fun q _ ↦ Nat.pow_le_pow_right (zero_lt_one.trans (primeIdeal_norm_gt_one q.val)) (h q)
  · exact ⟨p, Finset.mem_univ _, Nat.pow_lt_pow_right (primeIdeal_norm_gt_one p.val) hp⟩

end GRHArticle.ProgressionFree.NumberFieldIdeals
