import DiophantineConsistency.NativeHalfBinomial
import Diophantine.Paper1982.Carries

/-! # The population lower bound supplied by the native Pell source -/

namespace DiophantineConsistency.NativePopulationLower

open Jones1982 NativePellBootstrap NativePellPower NativeBinaryScale
  NativePellScaleBounds NativeHalfBinomial

/-- The actual common scale and half-binomial coefficient force the native
rank to have at least 3u+2 set bits when q=2^u. -/
theorem source_population_lower (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (hβ : 15 ≤ ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    {u : ℕ} (hqu : sourceQ ports x = 2 ^ u) :
    3 * u + 2 ≤ σ 2 (nativeRank x).toNat := by
  obtain ⟨r,w,hr,hR,hbin⟩ := source_half_binomial ports hports hβ x hx hs
  have h3u := source_binary_exponent_bound ports hports x hx hs hqu
  have hdivX : 2 ^ (3 * u + 1) ∣ x 21 := by
    rw [source_X_eq_two_pow_rank ports hports hβ x hx hs]
    exact pow_dvd_pow 2 (by omega)
  have hdivY : 2 ^ (3 * u) ∣ x 16 * x 9 := by
    have h := source_q_cube_dvd_Y ports hports.beta_pos.le x hs
    rw [hqu,← pow_mul,show u * 3 = 3 * u by omega] at h
    exact h
  have hdivtwoY : 2 ^ (3 * u + 1) ∣ 2 * (x 16 * x 9) := by
    rw [pow_succ]
    simpa only [mul_comm] using mul_dvd_mul hdivY (dvd_refl 2)
  have hdivwX : 2 ^ (3 * u + 1) ∣ w * x 21 := dvd_mul_of_dvd_right hdivX w
  have hdivchoose : 2 ^ (3 * u + 1) ∣ (2 * r).choose r := by
    have hd := Nat.dvd_sub hdivtwoY hdivwX
    have he : 2 * (x 16 * x 9) - w * x 21 = (2 * r).choose r := by omega
    rwa [he] at hd
  have hσr := (lemma_2_15 (3 * u + 1) r).mpr hdivchoose
  rw [hR,σ_two_two_mul_add_one]
  omega

end DiophantineConsistency.NativePopulationLower
