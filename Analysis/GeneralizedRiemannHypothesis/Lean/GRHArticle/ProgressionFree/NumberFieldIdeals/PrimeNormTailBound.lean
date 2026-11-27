import GRHArticle.ProgressionFree.NumberFieldIdeals.SquareNormTail
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# An explicit inverse-square tail for prime ideals

Group the prime ideals by their absolute norms. Every nonempty norm
fiber injects into the primes above a single rational prime. The
fundamental identity for ramification and inertia bounds its size
by the degree, including in the ramified case.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset

variable {K : Type*} [Field K] [NumberField K]

/-- Any finite family of distinct prime ideals of one absolute norm has at
most as many members as the degree of the number field. -/
theorem card_le_finrank_of_absNorm_eq {ι : Type*} (s : Finset ι)
    (P : ι → HeightOneSpectrum (𝓞 K)) (hP : Set.InjOn P s) {m : ℕ}
    (hm : ∀ i ∈ s, absNorm (P i).asIdeal = m) : s.card ≤ Module.finrank ℚ K := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  have hne : m ≠ 1 := fun h ↦ (P i).isMaximal.ne_top
    (absNorm_eq_one_iff.mp ((hm i hi).trans h))
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hne
  let b : Ideal ℤ := span {(p : ℤ)}
  have hp' := Nat.prime_iff_prime_int.mp hp
  have hb : b ≠ ⊥ := by simpa [b] using hp'.ne_zero
  haveI : b.IsMaximal := hp'.isMaximal_span_singleton
  apply le_trans _ (Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hb)
  apply Finset.card_le_card_of_injOn (fun j ↦ (P j).asIdeal)
  · intro j hj
    obtain ⟨Q, hQ, he, hdvd⟩ := exists_isMaximal_dvd_of_dvd_absNorm' hp (P j).asIdeal
      (by rwa [hm j hj])
    have hPQ := (P j).isMaximal.eq_of_le hQ.ne_top (dvd_iff_le.mp hdvd)
    exact (IsDedekindDomain.mem_primesOverFinset_iff hb _).mpr ⟨(P j).isPrime, ⟨by simpa [hPQ] using he.symm⟩⟩
  · exact fun i hi j hj he ↦ hP hi hj (HeightOneSpectrum.ext he)

/-- The contribution of prime ideals above norm cutoff `Y` to the
inverse-square series is at most the field degree divided by `Y`. -/
theorem primeIdeal_inv_sq_tail_le_finrank_div (Y : ℕ) (hY : 0 < Y) :
    (∑' p : {p : HeightOneSpectrum (𝓞 K) // Y < absNorm p.asIdeal},
      ((absNorm p.val.asIdeal : ℝ)^2)⁻¹) ≤ (Module.finrank ℚ K : ℝ) / Y := by
  classical
  let ν (p : {p : HeightOneSpectrum (𝓞 K) // Y < absNorm p.asIdeal}) := absNorm p.val.asIdeal
  let j (p : {p : HeightOneSpectrum (𝓞 K) // Y < absNorm p.asIdeal}) := ν p - (Y+1)
  have hj p : ν p = j p + Y + 1 := by
    have hp : Y < ν p := p.property
    dsimp [j]
    omega
  let F (k : ℕ) : ℝ := ((k : ℝ) + Y)⁻¹
  apply Real.tsum_le_of_sum_le (fun p ↦ by positivity)
  intro s
  let N := s.sup j + 1
  have hmap : ∀ p ∈ s, j p ∈ range N := fun p hp ↦
    mem_range.mpr (Nat.lt_succ_of_le (le_sup hp))
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ k ∈ range N, (Module.finrank ℚ K : ℝ) * (F k - F (k+1)) := by
      apply sum_le_sum
      intro k hk
      let T := s.filter (fun p ↦ j p = k)
      have hm p (hp : p ∈ T) : ν p = k+Y+1 := by rw [hj p, (mem_filter.mp hp).2]
      have hc := card_le_finrank_of_absNorm_eq T Subtype.val Subtype.val_injective.injOn hm
      have h₀ : (0 : ℝ) < (k : ℝ) + Y := by positivity
      have h₁ : (0 : ℝ) < (k : ℝ) + Y + 1 := by positivity
      have hweight : ((((k + Y + 1 : ℕ) : ℝ)^2)⁻¹) ≤ F k - F (k+1) := by
        simp only [Nat.cast_add, Nat.cast_one, F]
        rw [add_right_comm (k:ℝ) 1 (Y:ℝ)]
        field_simp
        nlinarith [sq_nonneg ((k:ℝ)+Y)]
      calc
        _ = ∑ p ∈ T, ((((k + Y + 1 : ℕ) : ℝ)^2)⁻¹) :=
          sum_congr rfl fun p hp ↦ by change (((ν p : ℝ)^2)⁻¹) = _; rw [hm p hp]
        _ = (T.card : ℝ) * ((((k + Y + 1 : ℕ) : ℝ)^2)⁻¹) := by simp
        _ ≤ (Module.finrank ℚ K : ℝ) * ((((k + Y + 1 : ℕ) : ℝ)^2)⁻¹) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg _)
    _ = (Module.finrank ℚ K : ℝ) * (F 0 - F N) := by rw [← mul_sum, sum_range_sub']
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa [F] using (sub_le_self (F 0) (show 0 ≤ F N by dsimp [F]; positivity))

end GRHArticle.ProgressionFree.NumberFieldIdeals
