import DiophantineConsistency.CurrentSparseDigits2011
import DiophantineConsistency.CurrentHighDigits2011
import DiophantineConsistency.CurrentWindowCarry2011

/-!
# The actual current polynomial supplies its entire arithmetic word window

There is no source-system, word, mask, window, or calibration premise.
A positive zero supplies a canonical parent, its positive natural source,
one coherent window length, and the literal Boolean and high-mask words.
The fixed kernel then gives bounded carries and the exact F digit word.
The actual original coordinates, rank and temporal shift remain visible.
-/

namespace DiophantineConsistency.CurrentPolynomialWindow2011

open CurrentKernel2011 CurrentWindowCarry2011 NativeCyclicConvolution

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The literal fourteen-coordinate polynomial at the complete four fixed ports. -/
noncomputable def polynomial : MvPolynomial (Fin 14) ℤ := Carrier65.polynomial ports

/-- All arithmetic data use the same restored source and the same cyclic window. -/
structure Facts (v : Fin 14 → ℤ) (N : ℕ) [NeZero (N * 2011)]
    (x : Fin 31 → ℕ) (c k digits : ZMod (N * 2011) → ℕ) : Prop where
  source_pos : ∀ j, 0 < x j
  source_rows : ∀ j, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) j = 0
  source_J : x 0 = (v 0).toNat
  source_F : x 1 = (v 1).toNat
  source_alpha : x 2 = (v 2).toNat
  source_z : x 3 = (v 3).toNat
  source_w : x 10 = (v 8).toNat
  source_q : NativeBinaryScale.sourceQ ports x = (Carrier65.core ports v).q.toNat
  source_C : NativeSourceMask.gap ports x = (Carrier65.core ports v).C.toNat
  source_rank : NativePellBootstrap.nativeRank x = (Carrier65.core ports v).rank
  q_window : (Carrier65.core ports v).q.toNat = radix ^ (N * 2011)
  J_window : (v 0).toNat = NativeMaskPopulation.repunit CurrentMasks2011.width N
  C_pos : 0 < (Carrier65.core ports v).C.toNat
  C_split : (Carrier65.core ports v).C.toNat + (v 1).toNat + (v 2).toNat =
    (Carrier65.core ports v).q.toNat
  F_bound : (v 1).toNat < radix ^ (N * 2011) - 1
  rank_population : Jones1982.σ 2 (Carrier65.core ports v).rank.toNat =
    3 * (47 * (N * 2011)) + 2
  temporal_power : (v 8).toNat =
    2 ^ ((Carrier65.core ports v).rank.toNat - 47 * (N * 2011))
  temporal_digits : NativeWindowCarry.temporalDigits 47 x c =
    NativeCyclicRotation.binaryRotation 47
      ((Carrier65.core ports v).rank.toNat - 47 * (N * 2011)) c
  transport : (K + (v 8).toNat) * (Carrier65.core ports v).C.toNat =
    (v 1).toNat + ((v 3).toNat - 1) * ((Carrier65.core ports v).q.toNat - 1)
  C_word : word radix c = (Carrier65.core ports v).C.toNat
  origin : c 0 = 1
  boolean : ∀ i, c i ≤ 1
  support : ∀ i, i.val % 2011 ∉ CurrentMasks2011.lowSupport → c i = 0
  carry_bound : ∀ i, k i ≤ 57
  digit_bound : ∀ i, digits i < radix
  carry_recurrence : ∀ i, k i = (convolution folded c i +
    NativeCyclicRotation.binaryRotation 47
      ((Carrier65.core ports v).rank.toNat - 47 * (N * 2011)) c i + k (i - 1)) / radix
  carry_equation : ∀ i, convolution folded c i +
    NativeCyclicRotation.binaryRotation 47
      ((Carrier65.core ports v).rank.toNat - 47 * (N * 2011)) c i + k (i - 1) =
      digits i + radix * k i
  F_word : word radix digits = (v 1).toNat
  mask_tests : ∀ i, digits i &&& CurrentHighDigits2011.maskDigits i = 0

/-- The positive window length provides the required finite cyclic type. -/
def Window (v : Fin 14 → ℤ) (N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  ∃ x : Fin 31 → ℕ, ∃ c k digits : ZMod (N * 2011) → ℕ, Facts v N x c k digits

/-- Every positive zero of the displayed polynomial supplies the complete
arithmetic window. Native occupation, phase and machine semantics are left
for subsequent work; they are not assumptions of this endpoint. -/
theorem polynomial_zero_window (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, Window v N hN := by
  have hK : (0 : ℤ) < (K : ℤ) := by exact_mod_cast K_pos
  have hp : Carrier65Witness.PortBounds ports :=
    CurrentCarrierArithmetic2011.portBounds (K : ℤ) hK
  have hb : 0 < ports 0 := by have := hp.beta_min; omega
  have hz' : Carrier65.value ports v = 0 := by
    simpa only [polynomial, Carrier65.eval_polynomial] using hz
  obtain ⟨h, _, hu, hcanon⟩ := Carrier66.positive_zero_restores_canonical ports hp v hv hz'
  let u := Carrier66.restore ports v h
  let x := Carrier66Source.sourceNat ports u
  have hx : ∀ j, 0 < x j := Carrier66Source.sourceNat_pos ports u hb hu hcanon
  have hs : ∀ j, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) j = 0 :=
    Carrier66Source.sourceNat_rows ports u hb hu hcanon
  have hJx : x 0 = (v 0).toNat := rfl
  have hFx : x 1 = (v 1).toNat := rfl
  have hAx : x 2 = (v 2).toNat := rfl
  have hzx : x 3 = (v 3).toNat := rfl
  have hwx : x 10 = (v 8).toNat := rfl
  have hqx : NativeBinaryScale.sourceQ ports x = (Carrier65.core ports v).q.toNat := by
    simpa only [u, Carrier66.core_restore] using Carrier66Source.sourceQ_eq ports u hb hu hcanon
  have hCx : NativeSourceMask.gap ports x = (Carrier65.core ports v).C.toNat := by
    simpa only [u, Carrier66.core_restore] using Carrier66Source.gap_eq ports u hb hu hcanon
  have hRx : NativePellBootstrap.nativeRank x = (Carrier65.core ports v).rank := by
    simpa only [u, Carrier66.core_restore] using Carrier66Source.nativeRank_eq ports u hb hu hcanon
  obtain ⟨N, hN, hq, hJ, hC, hsum, hlow, _, hpop, hpower, htrans⟩ :=
    NativeSourceWindow.source_native_window ports interface x hx hs
  have hwidth : CurrentMasks2011.width * N = 47 * (N * 2011) := by
    unfold CurrentMasks2011.width
    omega
  have hq' : NativeBinaryScale.sourceQ ports x = radix ^ (N * 2011) := by
    change NativeBinaryScale.sourceQ ports x = (2 ^ 47) ^ (N * 2011)
    rw [hq, CurrentMasks2011.width, ← pow_mul, ← pow_mul]
    congr 1
  have hClt : NativeSourceMask.gap ports x < radix ^ (N * 2011) := by
    have := hx 1
    omega
  have hlow' : (NativeSourceMask.gap ports x - 1) &&&
      (CurrentMasks2011.lowPort * NativeMaskPopulation.repunit CurrentMasks2011.width N + 1) = 0 := by
    rwa [hJ] at hlow
  have hreconstruct := CurrentSparseDigits2011.decode_low_mask hN hC hClt hlow'
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  obtain ⟨c, hcword, hc0, hc, hsupport⟩ := hreconstruct
  have hM : word radix (CurrentHighDigits2011.maskDigits (N := N)) =
      CurrentMasks2011.highPort * x 0 - 1 := by
    rw [CurrentHighDigits2011.high_mask_word, hJ]
  obtain ⟨k, digits, hk, hd, hrec, hadd, hword, hmask⟩ :=
    source_carries x hx hs c CurrentHighDigits2011.maskDigits hc
      CurrentHighDigits2011.maskDigits_lt hcword hq' hM
  have ht : NativeWindowCarry.temporalDigits 47 x c =
      NativeCyclicRotation.binaryRotation 47
        ((Carrier65.core ports v).rank.toNat - 47 * (N * 2011)) c := by
    unfold NativeWindowCarry.temporalDigits
    rw [hRx]
  have hFbound := NativeWindowCarry.source_F_lt_mersenne ports interface.portBox x hx hs
  have htrans' : (K + (v 8).toNat) * (Carrier65.core ports v).C.toNat =
      (v 1).toNat + ((v 3).toNat - 1) * ((Carrier65.core ports v).q.toNat - 1) := by
    change (K + x 10) * NativeSourceMask.gap ports x =
      x 1 + (x 3 - 1) * (NativeBinaryScale.sourceQ ports x - 1) at htrans
    simpa only [hqx, hCx, hwx, hFx, hzx] using htrans
  refine ⟨N, hN, x, c, k, digits, ?_⟩
  refine ⟨hx, hs, hJx, hFx, hAx, hzx, hwx, hqx, hCx, hRx, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ht, htrans', ?_, hc0, hc, hsupport, hk, hd, ?_, ?_, ?_, hmask⟩
  · exact hqx.symm.trans hq'
  · exact hJx.symm.trans hJ
  · rwa [hCx] at hC
  · simpa only [hCx, hFx, hAx, hqx] using hsum
  · simpa only [hFx, hq'] using hFbound
  · simpa only [hRx, hwidth] using hpop
  · simpa only [hwx, hRx, hwidth] using hpower
  · exact hcword.trans hCx
  · simpa only [ht] using hrec
  · simpa only [ht] using hadd
  · exact hword.trans hFx

end DiophantineConsistency.CurrentPolynomialWindow2011
