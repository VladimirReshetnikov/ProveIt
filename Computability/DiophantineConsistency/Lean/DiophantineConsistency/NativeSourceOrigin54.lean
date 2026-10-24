import DiophantineConsistency.NativeWindowConvolution54
import DiophantineConsistency.NativeLowPort54

/-!
# The native source forces the complete origin digit

The compact54 low mask has residue `ρ−2`. Together with the already proved
source mask equation, this forces the entire origin radix digit of `C`
to be exactly one. Whole-port binding and sparse-digit reconstruction are
separate obligations, not premises asserting native correctness.
-/

namespace DiophantineConsistency.NativeSourceOrigin54

open Jones1982 NativeMaskPopulation NativeSourceMask NativeBinaryScale
  NativePellBootstrap NativeCyclicConvolution
open scoped BigOperators

local notation "ρ" => NativeStencil54.radix

theorem repunit_mod_radix {d N : ℕ} (hd : 89 ≤ d) (hN : 0 < N) :
    repunit d N % ρ = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hp : 2 ^ d % ρ = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact pow_dvd_pow 2 hd
  change (1 + 2 ^ d * repunit d n) % ρ = 1
  rw [Nat.add_mod, Nat.mul_mod, hp]
  norm_num [NativeStencil54.radix]

/-- No support decomposition is needed for this arithmetic consequence of
the literal mask residue. Every bit of the origin radix digit is fixed. -/
theorem source_origin_mod_radix (ports : Fin 4 → ℤ) {d MC MF : ℕ}
    (h : Interface ports d MC MF) (hd : 89 ≤ d) (hMC : MC % ρ = ρ - 2)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    gap ports x % ρ = 1 := by
  obtain ⟨N, hN, _, hJ, hmask, _, _⟩ := source_mask_tests ports h x hx hs
  have hJmod : x 0 % ρ = 1 := by rw [hJ]; exact repunit_mod_radix hd hN
  have hmaskmod : (MC * x 0 + 1) % ρ = ρ - 1 := by
    rw [Nat.add_mod, Nat.mul_mod, hMC, hJmod]
    norm_num [NativeStencil54.radix]
  have hlow := congrArg (fun z : ℕ => z % 2 ^ 89) hmask
  rw [Nat.and_mod_two_pow] at hlow
  change (gap ports x - 1) % ρ &&& (MC * x 0 + 1) % ρ = 0 at hlow
  rw [hmaskmod] at hlow
  have hpre : (gap ports x - 1) % ρ = 0 := by
    simpa only [NativeStencil54.radix, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod] using hlow
  have hC := (source_gap_bounds ports h.portBox x hx hs).1
  calc
    gap ports x % ρ = ((gap ports x - 1) + 1) % ρ := by
      rw [Nat.sub_add_cancel hC]
    _ = 1 := by rw [Nat.add_mod, hpre]; norm_num [NativeStencil54.radix]

/-- A radix-bounded digit array has its least digit equal to its word
modulo the radix, even when the cyclic word has only one digit. -/
theorem word_mod_radix {n : ℕ} [NeZero n] (c : ZMod n → ℕ) :
    word ρ c % ρ = c 0 % ρ := by
  rw [word_eq_ofDigits]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    rw [List.ofFn_succ, Nat.ofDigits_cons]
    simp only [Nat.add_mul_mod_self_left]
    rfl

/-- This is the forced Start-selector input for the frozen convolution
interface. The bound and word equality here are exactly that interface's
assignment premises; no tiling or phase assumption is added. -/
theorem source_origin_digit {n : ℕ} [NeZero n] (ports : Fin 4 → ℤ)
    {d MC MF : ℕ} (h : Interface ports d MC MF) (hd : 89 ≤ d)
    (hMC : MC % ρ = ρ - 2) (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3) (hC : word ρ c = gap ports x) :
    c 0 = 1 := by
  have ho := source_origin_mod_radix ports h hd hMC x hx hs
  rw [← hC, word_mod_radix] at ho
  have hb : c 0 < ρ := by have := hc 0; norm_num [NativeStencil54.radix]; omega
  rwa [Nat.mod_eq_of_lt hb] at ho

/-- The exact whole low-port recipe discharges the residue premise.
Binding a delivered numeral to this recipe remains a separate finite task. -/
theorem source_origin_of_lowPort (ports : Fin 4 → ℤ) {d MC MF : ℕ}
    (h : Interface ports d MC MF) (hd : 89 ≤ d) (hMC : MC = NativeLowPort54.lowPort)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    gap ports x % ρ = 1 := by
  apply source_origin_mod_radix ports h hd _ x hx hs
  rw [hMC]
  exact NativeLowPort54.lowPort_mod_radix

theorem source_origin_digit_of_lowPort {n : ℕ} [NeZero n] (ports : Fin 4 → ℤ)
    {d MC MF : ℕ} (h : Interface ports d MC MF) (hd : 89 ≤ d)
    (hMC : MC = NativeLowPort54.lowPort) (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3) (hC : word ρ c = gap ports x) :
    c 0 = 1 := by
  apply source_origin_digit ports h hd _ x hx hs c hc hC
  rw [hMC]
  exact NativeLowPort54.lowPort_mod_radix

end DiophantineConsistency.NativeSourceOrigin54
