import DiophantineConsistency.NativeSourceWindow
import DiophantineConsistency.NativeStencil54
import DiophantineConsistency.NativeCyclicRotation

/-!
# From the proved native window to pointwise convolution mask tests

The remaining premises are explicit word/port bindings and digit bounds.
The temporal rotation, no-carry estimate, strict residue bound and transport
are proved here; no accepted-clause or machine-calibration premise is used.
-/

namespace DiophantineConsistency.NativeWindowConvolution54

open NativePellBootstrap NativePellPower NativeBinaryScale NativePellScaleBounds
  NativeSourceMask NativeSourceWindow NativeCyclicConvolution NativeCyclicRotation

/-- The positive gap and positive source slack rule out `F=q−1`.
This supplies the strict residue bound required by cyclic convolution. -/
theorem source_F_lt_mersenne (ports : Fin 4 → ℤ) (hp : PortBox ports)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    x 1 < sourceQ ports x - 1 := by
  obtain ⟨hC, hsum, _, _⟩ := source_gap_bounds ports hp x hx hs
  have hα := hx 2
  omega

/-- The normalized radix word for the source's binary temporal shift.
Its small partial-digit phase is retained, rather than assumed aligned. -/
def temporalDigits {n : ℕ} [NeZero n]
    (x : Fin 31 → ℕ) (c : ZMod n → ℕ) : ZMod n → ℕ :=
  binaryRotation 89 ((nativeRank x).toNat - 89 * n) c

theorem source_temporal_word {n : ℕ} [NeZero n] (ports : Fin 4 → ℤ)
    {d MC MF : ℕ} (h : Interface ports d MC MF)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (c : ZMod n → ℕ) (hC : word NativeStencil54.radix c = gap ports x)
    (hq : sourceQ ports x = NativeStencil54.radix ^ n) :
    word NativeStencil54.radix (temporalDigits x c) ≡
      x 10 * gap ports x [MOD NativeStencil54.radix ^ n - 1] := by
  have hqu : sourceQ ports x = 2 ^ (89 * n) := by
    rw [hq, NativeStencil54.radix, pow_mul]
  have hw := source_spatial_power ports h.portBox h.beta_ge_fifteen x hx hs hqu
  have hr := word_binaryRotation 89 ((nativeRank x).toNat - 89 * n) c
  simpa only [temporalDigits, NativeStencil54.radix, ← hC, hw] using hr

/-- The native source forces pointwise mask tests once the assignment
digits and the two fixed words have been bound to the literal recipes.
The coefficient mass and all temporal rotation phases are already covered. -/
theorem source_convolution_mask_digits {n : ℕ} [NeZero n] (ports : Fin 4 → ℤ)
    {d MC MF : ℕ} (h : Interface ports d MC MF)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (c m : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3) (hm : ∀ i, m i < NativeStencil54.radix)
    (hC : word NativeStencil54.radix c = gap ports x)
    (hq : sourceQ ports x = NativeStencil54.radix ^ n)
    (hK : (ports 1).toNat = NativeStencil54.rawWord NativeStencil54.radix)
    (hM : word NativeStencil54.radix m = MF * x 0 - 1) :
    ∀ k, (convolution NativeStencil54.folded c k + temporalDigits x c k) &&& m k = 0 := by
  obtain ⟨_, _, _, _, _, hmask, _⟩ := source_mask_tests ports h x hx hs
  have htrans := source_transport_identity ports h.portBox x hx hs
  have hcong : (ports 1).toNat * gap ports x + x 10 * gap ports x ≡
      x 1 [MOD NativeStencil54.radix ^ n - 1] := by
    rw [← add_mul, htrans, hq, Nat.add_mul_modulus_modEq_iff]
  have hrot := source_temporal_word ports h x hx hs c hC hq
  have htransport : NativeStencil54.rawWord NativeStencil54.radix *
      word NativeStencil54.radix c + word NativeStencil54.radix (temporalDigits x c) ≡
      x 1 [MOD NativeStencil54.radix ^ n - 1] := by
    rw [hC, ← hK]
    exact (hrot.add_left _).trans hcong
  have hF : x 1 < NativeStencil54.radix ^ n - 1 := by
    rw [← hq]
    exact source_F_lt_mersenne ports h.portBox x hx hs
  apply NativeStencil54.transport_mask_digits c (temporalDigits x c) m hc
    (fun k => binaryRotation_bound_89 _ c hc k) hm htransport hF
  rwa [hM]

end DiophantineConsistency.NativeWindowConvolution54
