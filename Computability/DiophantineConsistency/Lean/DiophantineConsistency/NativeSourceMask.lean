import DiophantineConsistency.NativePopulationLower
import DiophantineConsistency.NativeMaskPopulation

/-!
# The two native mask tests from the literal old-z source

The coefficient interface below states the exact radix, shift, low-bit and
population assumptions. No tableau or machine semantics is hidden in it.
-/

namespace DiophantineConsistency.NativeSourceMask

open Jones1982 NativePellBootstrap NativePellPower NativeBinaryScale
  NativePellScaleBounds NativePopulationLower NativeMaskPopulation
open scoped BigOperators

structure Interface (ports : Fin 4 → ℤ) (d MC MF : ℕ) : Prop where
  width : 4 ≤ d
  beta : ports 0 = (2 : ℤ) ^ d - 1
  K_nonneg : 0 ≤ ports 1
  MC_eq : ports 2 = MC
  MF_eq : ports 3 = MF + ports 0
  MC_lt : MC < 2 ^ d - 1
  MF_lt : MF < 2 ^ d - 1
  MC_even : MC % 2 = 0
  MF_four : MF % 8 = 4
  population : σ 2 MC + σ 2 MF = d

theorem Interface.beta_ge_fifteen {ports : Fin 4 → ℤ} {d MC MF : ℕ}
    (h : Interface ports d MC MF) : 15 ≤ ports 0 := by
  have hpow : (16 : ℕ) ≤ 2 ^ d := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) h.width
  have hz : (16 : ℤ) ≤ 2 ^ d := by exact_mod_cast hpow
  rw [h.beta]
  omega

theorem Interface.portBox {ports : Fin 4 → ℤ} {d MC MF : ℕ}
    (h : Interface ports d MC MF) : PortBox ports := by
  have hβ := h.beta_ge_fifteen
  have hMC : (MC : ℤ) < ports 0 := by
    have hm : MC + 2 ≤ 2 ^ d := by have := h.MC_lt; omega
    have hmZ : (MC : ℤ) + 2 ≤ (2 : ℤ) ^ d := by exact_mod_cast hm
    rw [h.beta]
    omega
  have hMF : (MF : ℤ) < ports 0 := by
    have hm : MF + 2 ≤ 2 ^ d := by have := h.MF_lt; omega
    have hmZ : (MF : ℤ) + 2 ≤ (2 : ℤ) ^ d := by exact_mod_cast hm
    rw [h.beta]
    omega
  refine ⟨by omega,h.K_nonneg,?_,?_,?_,?_⟩
  · rw [h.MC_eq]; positivity
  · rw [h.MF_eq]; positivity
  · rw [h.MC_eq]; exact hMC
  · rw [h.MF_eq]; omega

/-- The all-one digit word is exactly the geometric sum. -/
theorem repunit_eq_geom (d N : ℕ) : repunit d N = ∑ i ∈ Finset.range N, (2 ^ d) ^ i := by
  have he := Jones1982.ofDigits_map_range (2 ^ d) (fun _ => 1) N
  simpa [repunit,repeated] using he

/-- The source multiplier J is the actual N-cell repunit once q=B^N. -/
theorem source_J_eq_repunit (ports : Fin 4 → ℤ) {d : ℕ} (hd : 0 < d)
    (hβ : ports 0 = (2 : ℤ) ^ d - 1)
    (x : Fin 31 → ℕ) {N : ℕ} (hq : sourceQ ports x = (2 ^ d) ^ N) :
    x 0 = repunit d N := by
  have hpow : (2 : ℕ) ≤ 2 ^ d := by
    exact Nat.le_self_pow (by omega) 2
  have hβ0 : 0 ≤ ports 0 := by
    have hz : (2 : ℤ) ≤ 2 ^ d := by exact_mod_cast hpow
    rw [hβ]
    omega
  have hβnat : (ports 0).toNat = 2 ^ d - 1 := by
    apply Int.ofNat.inj
    change ((ports 0).toNat : ℤ) = ((2 ^ d - 1 : ℕ) : ℤ)
    rw [Int.toNat_of_nonneg hβ0,Nat.cast_sub (by omega : 1 ≤ 2 ^ d)]
    exact hβ
  have hq' : 1 + x 0 * (2 ^ d - 1) = (2 ^ d) ^ N := by
    simpa only [sourceQ,hβnat] using hq
  have he : x 0 + (2 ^ d) ^ N = 1 + x 0 * 2 ^ d := by
    rw [← hq']
    have hp : 2 ^ d = (2 ^ d - 1) + 1 := by omega
    nth_rw 2 [hp]
    ring
  rw [repunit_eq_geom]
  exact Jones1982.geom_of_eq hpow he

/-- The four-block identity is ordinary integer algebra; the beta-J
relation is used exactly once, including the shifted fourth source port. -/
theorem packing_four_block {q F C MC MF J beta : ℤ} (h : beta * J = q - 1) :
    ((q - 1) * (q - F) + (q - F - C)) * (q ^ 2 - 1) +
      (MC + q * (MF + beta)) * J =
    (C - 1) + (MC * J + 1) + q * (F + (MF * J - 1)) +
      q ^ 2 * (q - C) + q ^ 3 * (q - F - 1) := by
  linear_combination q * h

/-- The positive transport gap, interpreted as a natural after its source
positivity proof. -/
def gap (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) : ℕ := sourceQ ports x - x 1 - x 2

theorem source_gap_bounds (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    0 < gap ports x ∧ gap ports x + x 1 + x 2 = sourceQ ports x ∧
      x 1 < sourceQ ports x ∧ gap ports x - 1 < sourceQ ports x := by
  have hC := source_transport_positive ports hports.beta_pos hports.K_nonneg x hx hs
  rw [← sourceQ_cast ports hports.beta_pos.le x] at hC
  have hz : (x 1 : ℤ) + x 2 < sourceQ ports x := by omega
  have hn : x 1 + x 2 < sourceQ ports x := by exact_mod_cast hz
  dsimp [gap]
  have := hx 1
  have := hx 2
  omega

/-- The exact literal source rank has the four blocks used by population
saturation. The source fourth port is shifted exactly once. -/
theorem source_rank_four_blocks (ports : Fin 4 → ℤ) {d MC MF : ℕ}
    (h : Interface ports d MC MF) (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    (nativeRank x).toNat =
      (gap ports x - 1) + (MC * x 0 + 1) +
      sourceQ ports x * (x 1 + (MF * x 0 - 1)) +
      sourceQ ports x ^ 2 * (sourceQ ports x - 1 - (gap ports x - 1)) +
      sourceQ ports x ^ 3 * (sourceQ ports x - 1 - x 1) := by
  have hp := h.portBox
  obtain ⟨hC,hCsum,hFq,hAq⟩ := source_gap_bounds ports hp x hx hs
  have hMF : 0 < MF := by have := h.MF_four; omega
  have hMFJ : 1 ≤ MF * x 0 := Nat.mul_pos hMF (hx 0)
  have hqcast := sourceQ_cast ports hp.beta_pos.le x
  have hβJ : ports 0 * x 0 = (sourceQ ports x : ℤ) - 1 := by
    linear_combination -hqcast
  have hα : (x 2 : ℤ) = (sourceQ ports x : ℤ) - x 1 - gap ports x := by
    have hz : (gap ports x : ℤ) + x 1 + x 2 = sourceQ ports x := by exact_mod_cast hCsum
    omega
  have ht := source_rank_eq_target ports x hs
  dsimp [nativeTarget] at ht
  rw [← hqcast,h.MC_eq,h.MF_eq,hα] at ht
  have hfour := packing_four_block (q := (sourceQ ports x : ℤ)) (F := (x 1 : ℤ))
    (C := (gap ports x : ℤ)) (MC := (MC : ℤ)) (MF := (MF : ℤ))
    (J := (x 0 : ℤ)) hβJ
  have htarget : nativeRank x =
      ((gap ports x : ℤ) - 1) + (MC * x 0 + 1) +
      (sourceQ ports x : ℤ) * (x 1 + (MF * x 0 - 1)) +
      (sourceQ ports x : ℤ) ^ 2 * (sourceQ ports x - gap ports x) +
      (sourceQ ports x : ℤ) ^ 3 * (sourceQ ports x - x 1 - 1) := by
    rw [ht]
    linear_combination hfour
  have hR0 := source_native_rank_ge_twentyfour ports hp.beta_pos hp.K_nonneg
    hp.MC_nonneg hp.MF_nonneg x hx hs
  have hRcast : ((nativeRank x).toNat : ℤ) = nativeRank x := Int.toNat_of_nonneg (by omega)
  have hq1 : 1 ≤ sourceQ ports x := by omega
  have hAcast : ((gap ports x - 1 : ℕ) : ℤ) = (gap ports x : ℤ) - 1 :=
    Nat.cast_sub hC
  have hHcast : ((MF * x 0 - 1 : ℕ) : ℤ) = (MF : ℤ) * x 0 - 1 := by
    push_cast [Nat.cast_sub hMFJ]
    rfl
  have hCAcast : ((sourceQ ports x - 1 - (gap ports x - 1) : ℕ) : ℤ) =
      (sourceQ ports x : ℤ) - gap ports x := by
    rw [Nat.cast_sub (by omega : gap ports x - 1 ≤ sourceQ ports x - 1),
      Nat.cast_sub hq1,hAcast]
    ring
  have hCFcast : ((sourceQ ports x - 1 - x 1 : ℕ) : ℤ) =
      (sourceQ ports x : ℤ) - x 1 - 1 := by
    rw [Nat.cast_sub (by omega : x 1 ≤ sourceQ ports x - 1),Nat.cast_sub hq1]
    ring
  apply Int.ofNat.inj
  change ((nativeRank x).toNat : ℤ) =
    (((gap ports x - 1) + (MC * x 0 + 1) +
      sourceQ ports x * (x 1 + (MF * x 0 - 1)) +
      sourceQ ports x ^ 2 * (sourceQ ports x - 1 - (gap ports x - 1)) +
      sourceQ ports x ^ 3 * (sourceQ ports x - 1 - x 1) : ℕ) : ℤ)
  push_cast
  rw [hRcast,hAcast,hHcast,hCAcast,hCFcast]
  exact htarget

/-- The literal positive source enforces precisely the two native binary
mask tests for the displayed coefficient interface. -/
theorem source_mask_tests (ports : Fin 4 → ℤ) {d MC MF : ℕ}
    (h : Interface ports d MC MF) (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ N, 0 < N ∧ sourceQ ports x = (2 ^ d) ^ N ∧ x 0 = repunit d N ∧
      (gap ports x - 1) &&& (MC * x 0 + 1) = 0 ∧
      x 1 &&& (MF * x 0 - 1) = 0 ∧ σ 2 (nativeRank x).toNat = 3 * (d * N) + 2 := by
  have hp := h.portBox
  obtain ⟨N,hN,hq,hNR⟩ := source_q_power_radix ports hp h.beta_ge_fifteen
    (by have := h.width; omega) h.beta x hx hs
  have hJ := source_J_eq_repunit ports (by have := h.width; omega) h.beta x hq
  have hqu : sourceQ ports x = 2 ^ (d * N) := by rw [hq,pow_mul]
  obtain ⟨hC,hCsum,hFq,hAq⟩ := source_gap_bounds ports hp x hx hs
  have hpop := repeated_native_mask_population (by have := h.width; omega) hN
    (show MC < 2 ^ d by have := h.MC_lt; omega)
    (show MF < 2 ^ d by have := h.MF_lt; omega)
    h.MC_even h.MF_four h.population
  rw [← hJ] at hpop
  have hlower := source_population_lower ports hp h.beta_ge_fifteen x hx hs hqu
  have hfour := source_rank_four_blocks ports h x hx hs
  rw [hqu] at hfour hFq hAq
  obtain ⟨hmaskC,hmaskF,hσ⟩ := native_mask_saturation hAq hFq hfour (le_of_eq hpop) hlower
  exact ⟨N,hN,hq,hJ,hmaskC,hmaskF,hσ⟩

end DiophantineConsistency.NativeSourceMask
