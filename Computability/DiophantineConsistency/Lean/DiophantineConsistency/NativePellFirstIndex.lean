import DiophantineConsistency.NativePellBootstrap

/-!
# Exact first Pell index of the authoritative native source

This is an arithmetic consequence of the literal old-z source and its port box.
It derives the oddness of the native rank; parity is not a hypothesis.
-/

namespace DiophantineConsistency.NativePellFirstIndex

open Diophantine Pell NativePellBootstrap

/-- The first index congruence has no nonzero multiple of the window once
the main index is the native rank and is larger than the first index. -/
theorem first_index_exact {E Q k n R h : ℕ} (hQ : 0 < Q)
    (hEP : E ∣ 2 * Q) (hR : R + 1 < E) (hnR : n < R)
    (hk : k = 2 * yn (by omega : 1 < 2 * Q + 1) n)
    (hind : k = 1 + R + E * h) : 2 * n = R + 1 := by
  have hP : 1 < 2 * Q + 1 := by omega
  have hm : yn hP n ≡ n [MOD E] := by
    apply Nat.ModEq.of_dvd (show E ∣ 2 * Q + 1 - 1 by simpa using hEP)
    exact yn_modEq_a_sub_one hP n
  have hkmod : k ≡ 2 * n [MOD E] := by rw [hk]; exact hm.mul_left 2
  have hkR : k ≡ R + 1 [MOD E] := by
    show k % E = (R + 1) % E
    rw [hind,show 1 + R + E * h = R + 1 + h * E by ring,
      Nat.add_mul_mod_self_right]
  apply (hkmod.symm.trans hkR).eq_of_abs_lt
  rw [abs_lt]
  constructor <;> push_cast <;> omega

/-- Recover the first sequence index, including its exact relation to the
native rank, from the positive old-z source. -/
theorem source_first_index_exact (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ n, 0 < n ∧ 2 * n = (nativeRank x).toNat + 1 ∧
      x 11 = xn (by have := firstQ_pos x hx; omega :
        1 < 2 * firstQ x + 1) n ∧
      x 12 + x 13 = 2 * yn (by have := firstQ_pos x hx; omega :
        1 < 2 * firstQ x + 1) n := by
  obtain ⟨n,hn,hτ,hk⟩ := source_first_classification ports x hx hs
  obtain ⟨hD,hc⟩ := source_main_index_exact ports hports x hx hs
  have hR24 := source_native_rank_ge_twentyfour ports hports.beta_pos hports.K_nonneg
    hports.MC_nonneg hports.MF_nonneg x hx hs
  let R := (nativeRank x).toNat
  have hR : (R : ℤ) = nativeRank x := Int.toNat_of_nonneg (by omega)
  have hRpos : 0 < R := by
    exact_mod_cast (show (0 : ℤ) < (R : ℤ) by rw [hR]; omega)
  have hkc : x 12 + x 13 < x 19 := by
    have hce := (source_c_bounds ports x hx hs).1
    have hkY : x 12 + x 13 ≤ (x 12 + x 13) * (x 16 * x 9) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (hx 16) (hx 9))
    have hη := hx 12
    omega
  have hnR : n < R := main_index_gt_first (by omega)
    (by have := firstQ_pos x hx; omega)
    (by have h := (source_c_bounds ports x hx hs).2; omega) hRpos hn
    (source_base_separation ports hports.beta_pos x hx hs) hc hk hkc
  have hwindow := source_window_bound ports hports.beta_pos hports.K_nonneg
    hports.MC_lt_beta hports.MF_lt_twice_beta x hx hs
  have hRE : R + 1 < x 17 := by
    rw [← hR] at hwindow
    exact_mod_cast hwindow
  have hE := (source_first_registers ports x hx hs).1
  have hEP : x 17 ∣ 2 * firstQ x := by
    rw [hE]
    exact ⟨2 * (x 16 * x 9),by dsimp [firstQ]; ring⟩
  have h12 := hs 12
  change (-1 : ℤ) + x 26 + x 13 + x 12 + (-1) * ((x 8 : ℤ) * x 19) +
    (-1) * ((x 5 : ℤ) * x 17) = 0 at h12
  have hindZ : (x 12 : ℤ) + x 13 = 1 + R + x 17 * x 5 := by
    have hR' : (R : ℤ) = (x 19 : ℤ) * x 8 - x 26 := hR
    linear_combination h12 - hR'
  have hind : x 12 + x 13 = 1 + R + x 17 * x 5 := by exact_mod_cast hindZ
  exact ⟨n,hn,first_index_exact (firstQ_pos x hx) hEP hRE hnR hk hind,hτ,hk⟩

/-- Oddness is an output of first-index recovery. -/
theorem source_native_rank_odd (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    Odd (nativeRank x).toNat := by
  obtain ⟨n,hn,he,_,_⟩ := source_first_index_exact ports hports x hx hs
  refine ⟨n - 1,?_⟩
  omega

/-- The exact first pair in the usual odd-rank parameter `r`.
The source already forces `r≥12`, without a parity or size premise. -/
theorem source_first_pair (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ r, 12 ≤ r ∧ (nativeRank x).toNat = 2 * r + 1 ∧
      x 11 = xn (by have := firstQ_pos x hx; omega :
        1 < 2 * firstQ x + 1) (r + 1) ∧
      x 12 + x 13 = 2 * yn (by have := firstQ_pos x hx; omega :
        1 < 2 * firstQ x + 1) (r + 1) := by
  obtain ⟨n,hn,he,hτ,hk⟩ := source_first_index_exact ports hports x hx hs
  have hR24 := source_native_rank_ge_twentyfour ports hports.beta_pos hports.K_nonneg
    hports.MC_nonneg hports.MF_nonneg x hx hs
  have hcast : ((nativeRank x).toNat : ℤ) = nativeRank x := Int.toNat_of_nonneg (by omega)
  have hR24' : 24 ≤ (nativeRank x).toNat := by
    exact_mod_cast (show (24 : ℤ) ≤ ((nativeRank x).toNat : ℤ) by rw [hcast]; omega)
  refine ⟨n - 1,by omega,by omega,?_,?_⟩
  · simpa only [Nat.sub_add_cancel hn] using hτ
  · simpa only [Nat.sub_add_cancel hn] using hk

end DiophantineConsistency.NativePellFirstIndex
