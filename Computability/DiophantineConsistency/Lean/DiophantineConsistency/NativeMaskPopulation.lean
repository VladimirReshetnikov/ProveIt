import DiophantineConsistency.MaskPopulation

/-!
# Population saturation forces the two native mask tests

This local decoder treats the four binary blocks explicitly. The preceding
Pell source must supply the lower population bound, and the native coefficient
interface must supply the upper bound for its two repeated masks.
-/

namespace DiophantineConsistency.NativeMaskPopulation

open Jones1982

/-- An upper bound suffices even if the four summands have carries. -/
theorem four_block_population_le (u A B C D : ℕ) :
    σ 2 (A + 2 ^ u * B + (2 ^ u) ^ 2 * C + (2 ^ u) ^ 3 * D) ≤
      σ 2 A + σ 2 B + σ 2 C + σ 2 D := by
  have h1 := σ_two_add_le A (2 ^ u * B)
  have h2 := σ_two_add_le (A + 2 ^ u * B) ((2 ^ u) ^ 2 * C)
  have h3 := σ_two_add_le (A + 2 ^ u * B + (2 ^ u) ^ 2 * C) ((2 ^ u) ^ 3 * D)
  simp only [← pow_mul, lemma_2_4_σ] at h1 h2 h3 ⊢
  omega

/-- The half-binomial population lower bound leaves no room for either
masked overlap. The exact population equality follows as well. -/
theorem native_mask_saturation {u A F M H R : ℕ}
    (hA : A < 2 ^ u) (hF : F < 2 ^ u)
    (hR : R = A + M + 2 ^ u * (F + H) +
      (2 ^ u) ^ 2 * (2 ^ u - 1 - A) + (2 ^ u) ^ 3 * (2 ^ u - 1 - F))
    (hmask : σ 2 M + σ 2 H ≤ u + 2) (hlower : 3 * u + 2 ≤ σ 2 R) :
    A &&& M = 0 ∧ F &&& H = 0 ∧ σ 2 R = 3 * u + 2 := by
  have hpacked := four_block_population_le u (A + M) (F + H)
    (2 ^ u - 1 - A) (2 ^ u - 1 - F)
  rw [← hR] at hpacked
  have hCA := lemma_2_6 hA
  have hCF := lemma_2_6 hF
  have hAM := lemma_2_2 A M
  have hFH := lemma_2_2 F H
  have hzeroA : τ 2 A M = 0 := by omega
  have hzeroF : τ 2 F H = 0 := by omega
  exact ⟨(τ_two_eq_zero_iff A M).mp hzeroA,(τ_two_eq_zero_iff F H).mp hzeroF,by omega⟩

/-- Repetition of one radix digit. -/
def repeated (t N a : ℕ) : ℕ := Nat.ofDigits (2 ^ t) (List.replicate N a)

/-- The source multiplier J is the all-one radix word. -/
def repunit (t N : ℕ) : ℕ := repeated t N 1

theorem repeated_eq_mul_repunit (t N a : ℕ) : repeated t N a = a * repunit t N := by
  simp [repeated, repunit, Nat.mul_ofDigits]

theorem repeated_population (t N a : ℕ) (ha : a < 2 ^ t) :
    σ 2 (a * repunit t N) = N * σ 2 a := by
  rw [← repeated_eq_mul_repunit]
  have hpop := MaskPopulation.population_ofDigits t (List.replicate N a)
    (by intro x hx; have he : x = a := List.eq_of_mem_replicate hx; simpa only [he] using ha)
  simpa only [repeated,List.map_replicate,List.sum_replicate,nsmul_eq_mul,Nat.cast_id] using hpop

theorem repunit_mod_eight {t N : ℕ} (ht : 3 ≤ t) (hN : 0 < N) :
    repunit t N % 8 = 1 := by
  obtain ⟨n,rfl⟩ : ∃ n, N = n + 1 := ⟨N-1,by omega⟩
  have hpow : 2 ^ t % 8 = 0 := Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 ht)
  change (1 + 2 ^ t * repunit t n) % 8 = 1
  simp [Nat.add_mod, Nat.mul_mod, hpow]

theorem population_add_one_even {n : ℕ} (hn : n % 2 = 0) :
    σ 2 (n + 1) = σ 2 n + 1 := by
  rw [show n = 2 * (n / 2) by omega, σ_two_two_mul_add_one, σ_two_two_mul]

theorem population_sub_one_mod_eight {n : ℕ} (hn : n % 8 = 4) :
    σ 2 (n - 1) = σ 2 n + 1 := by
  have he : n = 8 * (n / 8) + 4 := by omega
  rw [he,show 8 * (n/8) + 4 - 1 = 8 * (n/8) + 3 by omega]
  rw [show 8 * (n/8) + 3 = 2 * (2 * (2 * (n/8)) + 1) + 1 by ring,
    show 8 * (n/8) + 4 = 2 * (2 * (2 * (n/8) + 1)) by ring]
  simp only [σ_two_two_mul_add_one,σ_two_two_mul]

/-- The two native repeated masks have exactly the claimed combined
population, including the low-origin increment and decrement. -/
theorem repeated_native_mask_population {t N MC MF : ℕ}
    (ht : 3 ≤ t) (hN : 0 < N) (hMC : MC < 2 ^ t) (hMF : MF < 2 ^ t)
    (hMCeven : MC % 2 = 0) (hMFfour : MF % 8 = 4)
    (hpopulation : σ 2 MC + σ 2 MF = t) :
    σ 2 (MC * repunit t N + 1) + σ 2 (MF * repunit t N - 1) = t * N + 2 := by
  have hJ8 := repunit_mod_eight ht hN
  have hMCJ : (MC * repunit t N) % 2 = 0 := by
    rw [Nat.mul_mod,hMCeven,zero_mul]
    norm_num
  have hMFJ : (MF * repunit t N) % 8 = 4 := by
    rw [Nat.mul_mod,hMFfour,hJ8]
  rw [population_add_one_even hMCJ,population_sub_one_mod_eight hMFJ,
    repeated_population t N MC hMC,repeated_population t N MF hMF]
  nlinarith

end DiophantineConsistency.NativeMaskPopulation
