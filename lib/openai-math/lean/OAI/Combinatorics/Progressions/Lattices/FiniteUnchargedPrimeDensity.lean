import OAI.Combinatorics.Progressions.Fourier.FiniteCharacterOrderTail

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

private theorem finite_prime_depth_mass {p : ℕ} (hp : 2 ≤ p) (A : ℕ) :
    (∑ a ∈ Finset.range A, 1 / ((p : ℝ) ^ (a + 1)) ^ 2) ≤ 2 / (p : ℝ) ^ 2 := by
  let r : ℝ := 1 / (p : ℝ) ^ 2
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr : r ≤ 1 / 2 := by
    dsimp only [r]
    apply (div_le_div_iff₀ (pow_pos hp0 2) (by norm_num)).mpr
    nlinarith
  calc
    _ = r * ∑ a ∈ Finset.range A, r ^ a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [r]
      simp only [one_div, inv_pow]
      rw [pow_right_comm, pow_succ' _ a, mul_inv]
    _ ≤ r * ∑ a ∈ Finset.range A, (1 / (2 : ℝ)) ^ a := by
      apply mul_le_mul_of_nonneg_left _ hr0
      exact Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ hr0 hr a)
    _ ≤ r * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le A) hr0
    _ = _ := by dsimp only [r]; ring

theorem finiteCharacter_order_dvd_of_annihilation {H : Type*} [AddCommGroup H]
    (N : ℕ) (hN : ∀ x : H, N • x = 0) (χ : AddChar H ℂ) : orderOf χ ∣ N := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hN x]
  exact χ.map_zero_eq_one

theorem finiteCharacter_uncharged_prime_mass {I H : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (f : AddChar H ℂ → ℝ)
    (hdecay : ∀ χ, χ ≠ 1 → f χ ≤ 1 / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) :
    (∑ χ : AddChar H ℂ with χ ≠ 1, f χ) ≤ 2 / (p : ℝ) ^ 2 := by
  let S := Finset.univ.filter (fun χ : AddChar H ℂ => χ ≠ 1)
  let orders := (Finset.range A).image (fun a => p ^ (a + 1))
  have hmap : (S : Set (AddChar H ℂ)).MapsTo orderOf orders := by
    intro χ hχ
    obtain ⟨a, ha, heq⟩ := (Nat.dvd_prime_pow hp).mp
      (finiteCharacter_order_dvd_of_annihilation (p ^ A) hann χ)
    have ha0 : 0 < a := by
      by_contra hz
      have haZ : a = 0 := by omega
      have ho : orderOf χ = 1 := by simpa only [haZ, pow_zero] using heq
      exact (Finset.mem_filter.mp hχ).2 (orderOf_eq_one_iff.mp ho)
    exact Finset.mem_image.mpr ⟨a - 1, Finset.mem_range.mpr (by omega),
      by rw [Nat.sub_add_cancel ha0]; exact heq.symm⟩
  change (∑ χ ∈ S, f χ) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  have hinner (q : ℕ) (hq : q ∈ orders) :
      (∑ χ ∈ S with orderOf χ = q, f χ) ≤ 1 / (q : ℝ) ^ 2 := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
    have hq0 : 0 < p ^ (a + 1) := pow_pos hp.pos _
    have hqR : (0 : ℝ) < ((p ^ (a + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr hq0
    have hc : (S.filter (fun χ => orderOf χ = p ^ (a + 1))).card ≤
        (p ^ (a + 1)) ^ Fintype.card I :=
      (Finset.card_le_card (by
        intro χ hχ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hχ).2⟩)).trans
          (finiteCharacter_exactOrder_card_le π hπ _ hq0)
    calc
      _ ≤ ∑ _χ ∈ S with orderOf _χ = p ^ (a + 1),
          1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2) := by
        apply Finset.sum_le_sum
        intro χ hχ
        simpa only [(Finset.mem_filter.mp hχ).2] using
          hdecay χ (Finset.mem_filter.mp (Finset.mem_filter.mp hχ).1).2
      _ = (S.filter (fun χ => orderOf χ = p ^ (a + 1))).card *
          (1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((p ^ (a + 1) : ℕ) : ℝ) ^ Fintype.card I *
          (1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = _ := by
        rw [pow_add (((p ^ (a + 1) : ℕ) : ℝ)) (Fintype.card I) 2]
        field_simp
  calc
    _ ≤ ∑ q ∈ orders, 1 / (q : ℝ) ^ 2 := Finset.sum_le_sum hinner
    _ = ∑ a ∈ Finset.range A, 1 / ((p : ℝ) ^ (a + 1)) ^ 2 := by
      rw [Finset.sum_image]
      · simp only [Nat.cast_pow]
      · intro a _ b _ hab
        exact Nat.add_right_cancel (Nat.pow_right_injective hp.two_le hab)
    _ ≤ _ := finite_prime_depth_mass hp.two_le A

theorem finiteImage_uncharged_prime_density {I H X : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [Fintype X]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (w : FiniteProbabilityWeights X) (Y : X → H)
    (hdecay : ∀ χ : AddChar H ℂ, χ ≠ 1 → ‖finiteImageCharacteristic w Y χ‖ ≤
      1 / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) (z : H) :
    |(Fintype.card H : ℝ) * finiteImageMass w Y z - 1| ≤ 2 / (p : ℝ) ^ 2 := by
  have he := finiteImageFourier_truncation w Y {1} z (Nat.cast_nonneg (Fintype.card H))
  have hcard : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardC : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Complex.ofReal_natCast, div_self hcard, div_self hcardC, one_mul,
    Finset.sum_singleton, finiteImageCharacteristic, AddChar.one_apply,
    FiniteProbabilityWeights.complexMean_const, star_one, mul_one] at he
  have htail := finiteCharacter_uncharged_prime_mass π hπ hp hann _ hdecay
  have htail' : spectrumTail {1} (fun χ => ‖finiteImageCharacteristic w Y χ‖) ≤ 2 / (p : ℝ) ^ 2 := by
    simpa only [spectrumTail, Finset.mem_singleton, Finset.sum_filter, ite_not] using htail
  have hbound := he.trans htail'
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hbound

theorem finiteImage_uncharged_prime_density_rpow {I H X : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [Fintype X]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (w : FiniteProbabilityWeights X) (Y : X → H) {P : ℝ}
    (hP : ((Fintype.card I + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar H ℂ, χ ≠ 1 → ‖finiteImageCharacteristic w Y χ‖ ≤
      (orderOf χ : ℝ) ^ (-P)) (z : H) :
    |(Fintype.card H : ℝ) * finiteImageMass w Y z - 1| ≤ 2 / (p : ℝ) ^ 2 := by
  have hfull (χ : AddChar H ℂ) : ‖finiteImageCharacteristic w Y χ‖ ≤
      1 * (orderOf χ : ℝ) ^ (-P) := by
    by_cases hχ : χ = 1
    · subst χ
      simp only [finiteImageCharacteristic, AddChar.one_apply,
        FiniteProbabilityWeights.complexMean_const, norm_one, orderOf_one,
        Nat.cast_one, Real.one_rpow, mul_one, le_refl]
    · simpa only [one_mul] using hdecay χ hχ
  have hinteger := finiteCharacter_integer_decay_of_rpow (I := I)
    (show (0 : ℝ) ≤ 1 by norm_num) hP _ hfull
  exact finiteImage_uncharged_prime_density π hπ hp hann w Y (fun χ _ => hinteger χ) z

theorem finiteImage_uncharged_prime_quotient_density {I H X : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [Fintype X]
    {p A : ℕ} (hp : p.Prime)
    (q : (I → ZMod (p ^ A)) →+ H) (hq : Function.Surjective q)
    (w : FiniteProbabilityWeights X) (Y : X → H) {P : ℝ}
    (hP : ((Fintype.card I + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar H ℂ, χ ≠ 1 → ‖finiteImageCharacteristic w Y χ‖ ≤
      (orderOf χ : ℝ) ^ (-P)) (z : H) :
    |(Fintype.card H : ℝ) * finiteImageMass w Y z - 1| ≤ 2 / (p : ℝ) ^ 2 ∧
      (Fintype.card H : ℝ) * finiteImageMass w Y z ≤ 1 + 2 / (p : ℝ) ^ 2 := by
  let reduction : (I → ℤ) →+ (I → ZMod (p ^ A)) :=
    { toFun := fun v i => (v i : ZMod (p ^ A))
      map_zero' := by ext i; simp
      map_add' := by intro v w; ext i; simp }
  have hred : Function.Surjective reduction := by
    intro v
    choose lift hlift using (fun i => ZMod.intCast_surjective (v i))
    exact ⟨lift, funext hlift⟩
  have hann (x : H) : (p ^ A) • x = 0 := by
    obtain ⟨v, rfl⟩ := hq x
    rw [← map_nsmul]
    have hz : (p ^ A) • v = 0 := by
      ext i
      simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
    rw [hz, map_zero]
  have hdensity := finiteImage_uncharged_prime_density_rpow (q.comp reduction)
    (hq.comp hred) hp hann w Y hP hdecay z
  exact ⟨hdensity, by linarith [(abs_le.mp hdensity).2]⟩

end Erdos3

end

end OAI
