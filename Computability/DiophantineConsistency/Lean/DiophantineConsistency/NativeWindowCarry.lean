import DiophantineConsistency.NativeSourceWindow
import DiophantineConsistency.NativeBooleanRotation
import DiophantineConsistency.NativeCyclicCarryWord

/-!
# Bounded carries from the actual native arithmetic window

The source transport and binary temporal shift give the raw convolution
congruence. A coefficient-mass budget then gives simultaneous bounded
cyclic carries and the exact F digit word, with its pointwise mask tests.
No no-carry estimate, temporal alignment, tile or machine premise occurs.
-/

namespace DiophantineConsistency.NativeWindowCarry

open NativePellBootstrap NativeBinaryScale NativeSourceMask NativeSourceWindow
  NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation

set_option Elab.async false

variable {n : ℕ} [NeZero n]

def temporalDigits (v : ℕ) (x : Fin 31 → ℕ) (c : ZMod n → ℕ) : ZMod n → ℕ :=
  binaryRotation v ((nativeRank x).toNat - v * n) c

/-- The two positive summands left beside F exclude the exceptional zero residue. -/
theorem source_F_lt_mersenne (p : Fin 4 → ℤ) (hp : PortBox p)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) :
    x 1 < sourceQ p x - 1 := by
  obtain ⟨hC, hsum, _, _⟩ := source_gap_bounds p hp x hx hs
  have hA := hx 2
  omega

/-- The temporal word is the source's actual binary shift, before phase recovery. -/
theorem source_temporal_word (v : ℕ) (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : Interface p d MC MF) (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0)
    (c : ZMod n → ℕ) (hC : word (2 ^ v) c = gap p x)
    (hq : sourceQ p x = (2 ^ v) ^ n) :
    word (2 ^ v) (temporalDigits v x c) ≡ x 10 * gap p x [MOD (2 ^ v) ^ n - 1] := by
  have hqu : sourceQ p x = 2 ^ (v * n) := by rw [hq, pow_mul]
  have hw := source_spatial_power p hi.portBox hi.beta_ge_fifteen x hx hs hqu
  have hr := word_binaryRotation v ((nativeRank x).toNat - v * n) c
  simpa only [temporalDigits, ← hC, hw] using hr

/-- The coefficient word need only be congruent to K: folding collisions and
exponents beyond the window are allowed. All local carry and mask facts follow. -/
theorem source_convolution_carries {v D : ℕ} (hv : 0 < v)
    (p : Fin 4 → ℤ) {d MC MF : ℕ} (hi : Interface p d MC MF)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0)
    (a c m : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (hm : ∀ i, m i < 2 ^ v)
    (hC : word (2 ^ v) c = gap p x) (hq : sourceQ p x = (2 ^ v) ^ n)
    (hK : word (2 ^ v) a ≡ (p 1).toNat [MOD (2 ^ v) ^ n - 1])
    (hM : word (2 ^ v) m = MF * x 0 - 1)
    (budget : mass a + 2 ^ (v - 1) + D < (D + 1) * 2 ^ v) :
    ∃ k digits : ZMod n → ℕ, (∀ i, k i ≤ D) ∧ (∀ i, digits i < 2 ^ v) ∧
      (∀ i, k i = (convolution a c i + temporalDigits v x c i + k (i - 1)) / 2 ^ v) ∧
      (∀ i, convolution a c i + temporalDigits v x c i + k (i - 1) =
        digits i + 2 ^ v * k i) ∧ word (2 ^ v) digits = x 1 ∧
      (∀ i, digits i &&& m i = 0) := by
  have hr : 1 < 2 ^ v := Nat.one_lt_two_pow hv.ne'
  have hcong : (p 1).toNat * gap p x + x 10 * gap p x ≡
      x 1 [MOD (2 ^ v) ^ n - 1] := by
    rw [← add_mul, source_transport_identity p hi.portBox x hx hs, hq,
      Nat.add_mul_modulus_modEq_iff]
  have htemporal := source_temporal_word v p hi x hx hs c hC hq
  have htransport : word (2 ^ v) a * word (2 ^ v) c +
      word (2 ^ v) (temporalDigits v x c) ≡ x 1 [MOD (2 ^ v) ^ n - 1] := by
    rw [hC]
    exact ((hK.mul_right (gap p x)).add htemporal).trans hcong
  have hbudget (i : ZMod n) :
      convolution a c i + temporalDigits v x c i + D < (D + 1) * 2 ^ v := by
    have hconv : convolution a c i ≤ mass a := by
      simpa only [mul_one] using convolution_le_mass a c hc i
    have hrot := rotation_le_half hv ((nativeRank x).toNat - v * n) c hc i
    change temporalDigits v x c i ≤ 2 ^ (v - 1) at hrot
    exact lt_of_le_of_lt
      (Nat.add_le_add_right (Nat.add_le_add hconv hrot) D) budget
  have hF : x 1 < (2 ^ v) ^ n - 1 := by
    rw [← hq]
    exact source_F_lt_mersenne p hi.portBox x hx hs
  obtain ⟨k, digits, hk, hd, hrec, hlocal, hword⟩ :=
    NativeCyclicCarryWord.exists_convolution_normalization hr a c
      (temporalDigits v x c) hbudget htransport (hx 1) hF
  refine ⟨k, digits, hk, hd, hrec, hlocal, hword, ?_⟩
  apply (mask_word_iff rfl digits m hd hm).mp
  obtain ⟨_, _, _, _, _, hmask, _⟩ := source_mask_tests p hi x hx hs
  rwa [hword, hM]

end DiophantineConsistency.NativeWindowCarry
