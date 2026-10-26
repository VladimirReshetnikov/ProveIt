import DiophantineConsistency.NativePellPower
import Mathlib.Data.Nat.GCD.Basic

/-!
# Recovery of the native binary block base

These lemmas bind the source's q to an actual power of its fixed binary radix.
The width d and beta=2^d−1 remain explicit, with no native-tableau claim.
-/

namespace DiophantineConsistency.NativeBinaryScale

open NativePellBootstrap NativePellPower

/-- The positive natural source base corresponding to its signed beta port. -/
def sourceQ (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) : ℕ :=
  1 + x 0 * (ports 0).toNat

theorem sourceQ_cast (ports : Fin 4 → ℤ) (hβ : 0 ≤ ports 0) (x : Fin 31 → ℕ) :
    (sourceQ ports x : ℤ) = 1 + (x 0 : ℤ) * ports 0 := by
  simp only [sourceQ,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Int.toNat_of_nonneg hβ]

/-- The exact q-divisibility of X comes directly from the source's second
lifting row. -/
theorem source_X_eq_q_mul (ports : Fin 4 → ℤ) (hβ : 0 ≤ ports 0)
    (x : Fin 31 → ℕ)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 21 = sourceQ ports x * x 10 := by
  have h2 := hs 2
  change (x 21 : ℤ) + (-1) * x 10 + (-ports 0) * ((x 0 : ℤ) * x 10) = 0 at h2
  have hz : (x 21 : ℤ) = (sourceQ ports x : ℤ) * x 10 := by
    rw [sourceQ_cast ports hβ x]
    linear_combination h2
  exact_mod_cast hz

/-- Every positive source zero has q a positive power of two. -/
theorem source_q_power_two (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (hβ : 15 ≤ ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ u, 0 < u ∧ u ≤ (nativeRank x).toNat ∧ sourceQ ports x = 2 ^ u := by
  have hX := source_X_eq_two_pow_rank ports hports hβ x hx hs
  have hqX := source_X_eq_q_mul ports hports.beta_pos.le x hs
  have hdiv : sourceQ ports x ∣ 2 ^ (nativeRank x).toNat := by
    rw [← hX]
    exact ⟨x 10,hqX⟩
  obtain ⟨u,hu,hqu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  refine ⟨u,?_,hu,hqu⟩
  have hβnat : 0 < (ports 0).toNat := by
    have he := Int.toNat_of_nonneg hports.beta_pos.le
    exact_mod_cast (show (0 : ℤ) < ((ports 0).toNat : ℤ) by rw [he]; exact hports.beta_pos)
  have hq : 1 < sourceQ ports x := by
    dsimp [sourceQ]
    nlinarith [Nat.mul_pos (hx 0) hβnat]
  by_contra h
  have hu0 : u = 0 := by omega
  rw [hu0,pow_zero] at hqu
  omega

/-- The order of two modulo 2^d−1 is exactly d. -/
theorem width_dvd_exponent {d u : ℕ} (hd : 0 < d)
    (hdiv : 2 ^ d - 1 ∣ 2 ^ u - 1) : d ∣ u := by
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  rw [Nat.pow_sub_one_mod_pow_sub_one] at hm
  apply Nat.dvd_of_mod_eq_zero
  by_contra hn
  have hsmall := (Nat.pow_le_one_iff hn).mp (Nat.sub_eq_zero_iff_le.mp hm)
  omega

/-- The source base is a power of the fixed radix, with a positive number
of native cells. -/
theorem source_q_power_radix (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (hβ : 15 ≤ ports 0) {d : ℕ} (hd : 0 < d)
    (hwidth : ports 0 = (2 : ℤ) ^ d - 1)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ N, 0 < N ∧ sourceQ ports x = (2 ^ d) ^ N ∧
      d * N ≤ (nativeRank x).toNat := by
  obtain ⟨u,hu,huR,hqu⟩ := source_q_power_two ports hports hβ x hx hs
  have hβnat : (ports 0).toNat = 2 ^ d - 1 := by
    apply Int.ofNat.inj
    change ((ports 0).toNat : ℤ) = ((2 ^ d - 1 : ℕ) : ℤ)
    rw [Int.toNat_of_nonneg hports.beta_pos.le,Nat.cast_sub (show 1 ≤ 2 ^ d from Nat.one_le_two_pow)]
    exact hwidth
  have hdiv : 2 ^ d - 1 ∣ 2 ^ u - 1 := by
    have hqu' : 2 ^ u = 1 + x 0 * (2 ^ d - 1) := by
      rw [← hqu,sourceQ,hβnat]
    refine ⟨x 0,?_⟩
    rw [hqu',Nat.add_sub_cancel_left]
    exact mul_comm _ _
  obtain ⟨N,hN⟩ := width_dvd_exponent hd hdiv
  refine ⟨N,?_,?_,?_⟩
  · by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0,mul_zero] at hN
    omega
  · rw [hqu,hN,pow_mul]
  · rw [← hN]
    exact huR

end DiophantineConsistency.NativeBinaryScale
