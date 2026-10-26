import DiophantineConsistency.CurrentWordHighMask2011
import DiophantineConsistency.CurrentWordScalarWitness2011
import DiophantineConsistency.WangTiles942PowerDimensions

/-!
# One coherent native packing from the actual marked language

Both masks, positive scalar fields, exact unit transport and the repunit
window use one source word and one normalization. The temporal multiplier
is still chosen from the tiling stride. Its required equality with the
printed-rank multiplier, and the remaining Pell witnesses, are not claimed.
-/

namespace DiophantineConsistency.CurrentNativePacking2011

open NativeCyclicConvolution CurrentMasks2011 CurrentWordConstruction2011
  CurrentWordCopies2011 CurrentWordClause2011 CurrentWordHighMask2011
  CurrentWordScalarWitness2011 WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

/-- The source J is the literal positive repunit of this same window. -/
theorem repunit_pos : 0 < NativeMaskPopulation.repunit width N := by
  rw [NativeSourceMask.repunit_eq_geom]
  have hi := Finset.single_le_sum (s := Finset.range N)
    (f := fun i => (2^width)^i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (NeZero.pos N))
  simp only [pow_zero] at hi
  omega

omit [NeZero N] in
theorem repunit_balance : beta*NativeMaskPopulation.repunit width N+1 = q N := by
  rw [NativeSourceMask.repunit_eq_geom,width,pow_mul]
  change (radix^2011-1)*(∑ i ∈ Finset.range N, (radix^2011)^i)+1 = radix^(N*2011)
  have hg := geom_sum_mul_add (radix^2011-1) N
  rw [Nat.sub_add_cancel (one_le_pow₀ (by decide : 1 ≤ radix))] at hg
  calc
    _ = (radix^2011)^N := by
      simpa only [Nat.mul_comm (radix^2011-1)] using hg
    _ = radix^(N*2011) := by rw [← pow_mul, Nat.mul_comm 2011 N]

/-- Every scalar and mask uses exactly the original source and digit word. -/
structure Facts (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ) : Prop where
  normalization : CurrentCarryConstruction2011.Facts
    (constructedWord a dummy s) (displacement s) k digits
  scalars : ScalarFacts (q N) (source a dummy (shiftedStartMarker a (s : ZMod N)))
    (normalized digits) (multiplier s)
    (alpha (q N) (source a dummy (shiftedStartMarker a (s : ZMod N))) (normalized digits))
    (quotientWitness (q N) ((CurrentKernel2011.K+multiplier s)*
      source a dummy (shiftedStartMarker a (s : ZMod N))))
  low_mask : (word radix (constructedWord a dummy s)-1) &&&
    (lowPort*NativeMaskPopulation.repunit width N+1) = 0
  high_mask : word radix digits &&&
    (highPort*NativeMaskPopulation.repunit width N-1) = 0
  digit_masks : ∀ i, digits i &&& CurrentHighDigits2011.maskDigits i = 0
  repunit_positive : 0 < NativeMaskPopulation.repunit width N
  repunit_equation : beta*NativeMaskPopulation.repunit width N+1 = q N

/-- The normalization is constructed; no scalar fields or mask successes
are supplied as hypotheses. The actual dummy choices remain independent. -/
theorem marked_constructs_packing (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a) :
    ∃ k digits : ZMod (N*2011) → ℕ, Facts a dummy s k digits := by
  obtain ⟨k,digits,hf,hm,hs,_,_⟩ := exists_high_mask_normalization a dummy hd s ha
  obtain ⟨hscalar,hlow⟩ := scalar_witness a dummy _ hd (shiftedStartMarker_boolean a _)
    ha.start_at_zero s k digits hf
  exact ⟨k,digits,hf,hscalar,hlow,hs,hm,repunit_pos,repunit_balance⟩

/-- A conditional halt gives packing at independently large power dimensions.
The full actual marked word and its unique Start are retained. -/
theorem halt_constructs_power_packing (p : ℕ) (hp : 1 < p) (T wBound hBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ∃ rw rh : ℕ, 0 < rw ∧ 0 < rh ∧ wBound < p^rw ∧ hBound < p^rh ∧
      p^rw*p^rh = p^(rw+rh) ∧
      letI : NeZero (p^rw*p^rh) := ⟨Nat.mul_ne_zero
        (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega))⟩
      ∃ a : ZMod (p^rw*p^rh) → Fin 942,
      ∃ k digits : ZMod ((p^rw*p^rh)*2011) → ℕ,
        MarkedWord (p^rw*p^rh) ((p^rw : ℕ) : ℤ) a ∧
        (∀ z, a z = 0 ↔ z = 0) ∧ Facts a (fun _ => 0) (p^rw) k digits := by
  obtain ⟨rw,rh,hrw,hrh,hwb,hhb,hpower,hword⟩ :=
    WangTiles942PowerDimensions.exists_power_marked_word p hp T wBound hBound hh
  letI : NeZero (p^rw*p^rh) := ⟨Nat.mul_ne_zero
    (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega))⟩
  obtain ⟨a,ha,hu⟩ := hword
  obtain ⟨k,digits,hpack⟩ := marked_constructs_packing a (fun _ => 0)
    (fun _ => by omega) (p^rw) ha
  exact ⟨rw,rh,hrw,hrh,hwb,hhb,hpower,a,k,digits,ha,hu,hpack⟩

end DiophantineConsistency.CurrentNativePacking2011
