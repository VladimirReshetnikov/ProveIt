import DiophantineConsistency.NativeBinaryScale

/-!
# The symmetric scale recovered from the literal native source

After exponential recovery, q cubed divides both X and Y. These are the
normalization facts needed before a half-binomial ratio extraction.
-/

namespace DiophantineConsistency.NativePellScaleBounds

open NativePellBootstrap NativePellPower NativeBinaryScale

/-- The literal defining rows identify N=q³ over the naturals. -/
theorem source_N_eq_q_cube (ports : Fin 4 → ℤ) (hβ : 0 ≤ ports 0)
    (x : Fin 31 → ℕ)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 16 = sourceQ ports x ^ 3 := by
  have h0 := hs 0
  have h1 := hs 1
  change (x 24 : ℤ) + ((-2) * ports 0) * x 0 + (-(ports 0 ^ 2)) * ((x 0 : ℤ) ^ 2) = 0 at h0
  change (-1 : ℤ) + (-1) * x 24 + x 16 + (-ports 0) * x 0 +
    (-ports 0) * ((x 0 : ℤ) * x 24) = 0 at h1
  have hL : (x 24 : ℤ) = (sourceQ ports x : ℤ) ^ 2 - 1 := by
    rw [sourceQ_cast ports hβ x]
    linear_combination h0
  have hN : (x 16 : ℤ) = (sourceQ ports x : ℤ) * (1 + x 24) := by
    rw [sourceQ_cast ports hβ x]
    linear_combination h1
  rw [hL] at hN
  have hz : (x 16 : ℤ) = (sourceQ ports x : ℤ) ^ 3 := by
    rw [hN]
    ring
  exact_mod_cast hz

/-- A stronger lower bound for the inner native rank than its coarse
twenty-four bound, derived from its exact packing target. -/
theorem source_rank_gt_three_q (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    3 * sourceQ ports x < (nativeRank x).toNat := by
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hC : 0 < q - x 1 - x 2 :=
    source_transport_positive ports hports.beta_pos hports.K_nonneg x hx hs
  have hF : (0 : ℤ) < x 1 := by exact_mod_cast hx 1
  have hα : (0 : ℤ) < x 2 := by exact_mod_cast hx 2
  have hq3 : 3 ≤ q := by omega
  have hL8 : 8 ≤ q ^ 2 - 1 := by nlinarith
  have hG : q ≤ (q - 1) * (q - x 1) + x 2 := by
    nlinarith [mul_nonneg (show 0 ≤ q - 1 by omega) (show 0 ≤ q - x 1 - 1 by omega)]
  have hGL := mul_le_mul_of_nonneg_right hG (show 0 ≤ q ^ 2 - 1 by omega)
  have hmin : 3 * q < q * (q ^ 2 - 1) := by nlinarith
  have hmask : 0 ≤ (ports 2 + ports 3 * q) * x 0 :=
    mul_nonneg (add_nonneg hports.MC_nonneg (mul_nonneg hports.MF_nonneg (by omega)))
      (by positivity)
  have htarget := source_rank_eq_target ports x hs
  change nativeRank x = ((q - 1) * (q - x 1) + x 2) * (q ^ 2 - 1) +
    (ports 2 + ports 3 * q) * x 0 at htarget
  have hR : 3 * q < nativeRank x := by linarith
  have hcast : ((nativeRank x).toNat : ℤ) = nativeRank x :=
    Int.toNat_of_nonneg (by omega)
  have hqcast : (sourceQ ports x : ℤ) = q := sourceQ_cast ports hports.beta_pos.le x
  have hz : (3 : ℤ) * (sourceQ ports x : ℤ) < ((nativeRank x).toNat : ℤ) := by
    rw [hqcast,hcast]
    exact hR
  exact_mod_cast hz

/-- The source rank dominates three times the binary exponent of q. -/
theorem source_binary_exponent_bound (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    {u : ℕ} (hqu : sourceQ ports x = 2 ^ u) :
    3 * u < (nativeRank x).toNat := by
  have hR := source_rank_gt_three_q ports hports x hx hs
  have huq : u < sourceQ ports x := by rw [hqu]; exact Nat.lt_two_pow_self
  omega

/-- The recovered X admits the symmetric q³ scale, proved by exponent
divisibility rather than assumed in the ratio block. -/
theorem source_q_cube_dvd_X (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (hβ : 15 ≤ ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    sourceQ ports x ^ 3 ∣ x 21 := by
  obtain ⟨u,hu,huR,hqu⟩ := source_q_power_two ports hports hβ x hx hs
  have h3u := source_binary_exponent_bound ports hports x hx hs hqu
  rw [source_X_eq_two_pow_rank ports hports hβ x hx hs,hqu,← pow_mul]
  exact pow_dvd_pow 2 (by omega)

/-- The other common-scale divisibility is a direct defining-row identity. -/
theorem source_q_cube_dvd_Y (ports : Fin 4 → ℤ) (hβ : 0 ≤ ports 0)
    (x : Fin 31 → ℕ)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    sourceQ ports x ^ 3 ∣ x 16 * x 9 := by
  rw [source_N_eq_q_cube ports hβ x hs]
  exact dvd_mul_right _ _

end DiophantineConsistency.NativePellScaleBounds
