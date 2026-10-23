import DiophantineConsistency.NativeSourceMask

/-!
# The native arithmetic window extracted from the literal source

This file combines the exponential shift, old-z transport and both native
mask tests. The window still requires a separate tableau/computation decoder.
-/

namespace DiophantineConsistency.NativeSourceWindow

open Jones1982 NativePellBootstrap NativePellPower NativeBinaryScale
  NativePellScaleBounds NativeMaskPopulation NativeSourceMask

/-- The old positive transport coordinate is retained exactly as z−1 on
the right-hand side; no shifted-coordinate positivity is assumed. -/
theorem source_transport_identity (ports : Fin 4 → ℤ) (hp : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ((ports 1).toNat + x 10) * gap ports x =
      x 1 + (x 3 - 1) * (sourceQ ports x - 1) := by
  obtain ⟨hC,hCsum,hFq,hAq⟩ := source_gap_bounds ports hp x hx hs
  have hq := sourceQ_cast ports hp.beta_pos.le x
  have hα : (x 2 : ℤ) = (sourceQ ports x : ℤ) - x 1 - gap ports x := by
    have he : (gap ports x : ℤ) + x 1 + x 2 = sourceQ ports x := by exact_mod_cast hCsum
    omega
  have h14 := hs 14
  change ports 1 + (x 10 : ℤ) + (-ports 1) * x 2 + (-1) * ((x 2 : ℤ) * x 10) +
    (-1 - ports 1) * x 1 + (-1) * ((x 1 : ℤ) * x 10) +
    (ports 0 + ports 0 * ports 1) * x 0 + ports 0 * ((x 0 : ℤ) * x 10) +
    (-ports 0) * ((x 0 : ℤ) * x 3) = 0 at h14
  have htrans : (ports 1 + x 10) * (gap ports x : ℤ) =
      x 1 + ((x 3 : ℤ) - 1) * ((sourceQ ports x : ℤ) - 1) := by
    rw [hα] at h14
    linear_combination h14 + (ports 1 + x 10 + 1 - x 3) * hq
  have hz : ((((ports 1).toNat + x 10) * gap ports x : ℕ) : ℤ) =
      ((x 1 + (x 3 - 1) * (sourceQ ports x - 1) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (hx 3),Nat.cast_sub (by omega : 1 ≤ sourceQ ports x),
      Int.toNat_of_nonneg hp.K_nonneg]
    exact htrans
  exact_mod_cast hz

/-- The source's spatial coefficient is the actual binary shift determined
by the native rank and the binary window length. -/
theorem source_spatial_power (ports : Fin 4 → ℤ) (hp : PortBox ports)
    (hβ : 15 ≤ ports 0) (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    {u : ℕ} (hq : sourceQ ports x = 2 ^ u) :
    x 10 = 2 ^ ((nativeRank x).toNat - u) := by
  have hX := source_X_eq_two_pow_rank ports hp hβ x hx hs
  have hqX := source_X_eq_q_mul ports hp.beta_pos.le x hs
  have h3u := source_binary_exponent_bound ports hp x hx hs hq
  have huR : u ≤ (nativeRank x).toNat := by omega
  have hqe : 0 < sourceQ ports x := by rw [hq]; positivity
  apply Nat.eq_of_mul_eq_mul_left hqe
  calc sourceQ ports x * x 10 = x 21 := hqX.symm
    _ = 2 ^ (nativeRank x).toNat := hX
    _ = sourceQ ports x * 2 ^ ((nativeRank x).toNat - u) := by
      rw [hq,← pow_add,Nat.add_sub_of_le huR]

/-- All arithmetic data required by the native mask window follow from
the literal source and its stated coefficient interface. -/
theorem source_native_window (ports : Fin 4 → ℤ) {d MC MF : ℕ}
    (h : Interface ports d MC MF) (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ N, 0 < N ∧ sourceQ ports x = (2 ^ d) ^ N ∧ x 0 = repunit d N ∧
      0 < gap ports x ∧ gap ports x + x 1 + x 2 = sourceQ ports x ∧
      (gap ports x - 1) &&& (MC * x 0 + 1) = 0 ∧ x 1 &&& (MF * x 0 - 1) = 0 ∧
      σ 2 (nativeRank x).toNat = 3 * (d * N) + 2 ∧
      x 10 = 2 ^ ((nativeRank x).toNat - d * N) ∧
      ((ports 1).toNat + x 10) * gap ports x =
        x 1 + (x 3 - 1) * (sourceQ ports x - 1) := by
  obtain ⟨N,hN,hq,hJ,hMC,hMF,hσ⟩ := source_mask_tests ports h x hx hs
  obtain ⟨hC,hCsum,_,_⟩ := source_gap_bounds ports h.portBox x hx hs
  have hqu : sourceQ ports x = 2 ^ (d * N) := by rw [hq,pow_mul]
  refine ⟨N,hN,hq,hJ,hC,hCsum,hMC,hMF,hσ,?_,?_⟩
  · exact source_spatial_power ports h.portBox h.beta_ge_fifteen x hx hs hqu
  · exact source_transport_identity ports h.portBox x hx hs

end DiophantineConsistency.NativeSourceWindow
