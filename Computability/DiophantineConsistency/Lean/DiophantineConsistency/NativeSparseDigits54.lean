import DiophantineConsistency.NativeVariableMask
import DiophantineConsistency.NativeWindowConvolution54
import DiophantineConsistency.OnePageLowPort54

/-! # The literal compact54 low mask reconstructs sparse assignment digits

The source supplies the assignment word, origin and capacity bounds. The
remaining coefficient-interface assumptions are written explicitly; no
accepted-tableau or native-machine correctness premise is present.
-/

namespace DiophantineConsistency.NativeSparseDigits54

open NativeCyclicConvolution NativeRadixDigits NativeVariableMask NativeSourceMask
  NativePellBootstrap NativeStencil54 NativeMaskPopulation NativeBinaryScale
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The actual low-bit support, with forbidden selector1 omitted. -/
def support : Finset ℕ := NativeLowPort54.positions.toFinset

theorem positions_nodup : NativeLowPort54.positions.Nodup := by
  rw [NativeLowPort54.positions, ← OnePageTuple54.assignmentPositions_eq]
  exact OnePageTuple54.assignmentPositions_nodup.filter _

private theorem bounded_positions :
    OnePageTuple54.assignmentPositions.all (fun j => decide (j < cellLength)) = true := by decide

theorem support_lt {j : ℕ} (hj : j ∈ support) : j < cellLength := by
  have hm : j ∈ NativeLowPort54.positions := List.mem_toFinset.mp hj
  rw [NativeLowPort54.positions, ← OnePageTuple54.assignmentPositions_eq] at hm
  exact of_decide_eq_true ((List.all_eq_true.mp bounded_positions) j (List.mem_filter.mp hm).1)

theorem zero_mem_support : 0 ∈ support := by
  apply List.mem_toFinset.mpr
  rw [NativeLowPort54.positions_head]
  simp

theorem dummy_mem_support : 507 ∈ support := by
  apply List.mem_toFinset.mpr
  rw [NativeLowPort54.positions, ← OnePageTuple54.assignmentPositions_eq]
  decide

theorem selector_one_not_mem : 1 ∉ support := by
  simp [support, NativeLowPort54.positions]

/-- A one-bit slot except at dummy507, which has two bits. -/
def bits (j : ℕ) : ℕ := capacity support 507 j

theorem bits_le_two (j : ℕ) : bits j ≤ 2 := capacity_le_two _ _ _

theorem bits_zero : bits 0 = 1 := by
  simp [bits, capacity, zero_mem_support]

theorem bits_one : bits 1 = 0 := by
  simp [bits, capacity, selector_one_not_mem]

/-- The symbolic low port is exactly the cell word for these capacities. -/
theorem cellWord_eq_lowPort : cellWord radix cellLength support 507 = NativeLowPort54.lowPort := by
  have he := cellWord_complement (by decide : 4 ≤ radix) support
    (fun j hj => support_lt hj) dummy_mem_support
  rw [show (∑ j ∈ support, radix ^ j) =
      (NativeLowPort54.positions.map fun j => radix ^ j).sum from
    List.sum_toFinset _ positions_nodup] at he
  have hlow := NativeLowPort54.lowPort_exact
  dsimp [NativeLowPort54.removedWord] at hlow
  omega

variable {N : ℕ} [NeZero (N * cellLength)]

def periodicBits (k : ZMod (N * cellLength)) : ℕ := bits (k.val % cellLength)

theorem mask_word :
    word radix (originMask radix (periodicBits (N := N))) =
      NativeLowPort54.lowPort * repunit (89 * cellLength) N + 1 := by
  have hw := word_originMask (N := N) (by decide : 2 ≤ 89)
    (by decide : 0 < cellLength) support (by decide : 507 ≠ 0) zero_mem_support
  change word radix (originMask radix (periodicBits (N := N))) =
    cellWord radix cellLength support 507 *
      (∑ k : Fin N, (radix ^ cellLength) ^ k.val) + 1 at hw
  rw [cellWord_eq_lowPort, show (∑ k : Fin N, (radix ^ cellLength) ^ k.val) =
    repunit (89 * cellLength) N from periodic_factor 89 cellLength N] at hw
  exact hw

/-- For a fixed source window length, the actual low mask supplies all
assignment premises, including sparsity and the exceptional dummy bound. -/
theorem source_assignment (ports : Fin 4 → ℤ) {MF : ℕ}
    (h : Interface ports (89 * cellLength) NativeLowPort54.lowPort MF)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (hq : sourceQ ports x = (2 ^ (89 * cellLength)) ^ N) :
    ∃ c : ZMod (N * cellLength) → ℕ,
      word radix c = gap ports x ∧ c 0 = 1 ∧
      (∀ k, c k < 2 ^ periodicBits k) ∧ (∀ k, c k ≤ 3) := by
  have hq' : sourceQ ports x = radix ^ (N * cellLength) := by
    rw [hq, radix, ← pow_mul, ← pow_mul]
    congr 1
    ring
  obtain ⟨hC, hsum, _, _⟩ := source_gap_bounds ports h.portBox x hx hs
  have hJ := source_J_eq_repunit ports (by decide : 0 < 89 * cellLength) h.beta x hq
  have hmask : (gap ports x - 1) &&& word radix (originMask radix (periodicBits (N := N))) = 0 := by
    obtain ⟨_, _, _, _, hm, _, _⟩ := source_mask_tests ports h x hx hs
    rwa [mask_word, ← hJ]
  obtain ⟨c, hc, hc0, hbits⟩ := decode_originMask (by decide : 1 ≤ 89) hC
    (show gap ports x < (2 ^ 89) ^ (N * cellLength) by
      change gap ports x < radix ^ (N * cellLength)
      rw [← hq']
      have := hx 1
      omega)
    (periodicBits (N := N))
    (fun k => by have hb := bits_le_two (k.val % cellLength); change bits _ ≤ 89; omega)
    (by simp [periodicBits, bits_zero]) hmask
  refine ⟨c, hc, hc0, hbits, fun k => ?_⟩
  have hb : periodicBits k ≤ 2 := bits_le_two _
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) hb
  have hk := hbits k
  norm_num at hp
  omega

omit [NeZero (N * cellLength)] in
/-- The zero digits outside the literal support are a consequence, not a
separate sparse-assignment hypothesis. -/
theorem assignment_sparse (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) (k : ZMod (N * cellLength))
    (hk : k.val % cellLength ∉ support) : c k = 0 := by
  have hd : k.val % cellLength ≠ 507 := by
    intro he
    rw [he] at hk
    exact hk dummy_mem_support
  have hh := hc k
  simp only [periodicBits, bits, capacity, hd, hk, if_false, pow_zero] at hh
  omega

omit [NeZero (N * cellLength)] in
/-- Every supported position except the upper dummy is Boolean. -/
theorem assignment_boolean (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) (k : ZMod (N * cellLength))
    (hk : k.val % cellLength ≠ 507) : c k ≤ 1 := by
  have hb : periodicBits k ≤ 1 := by
    unfold periodicBits bits capacity
    simp only [hk, if_false]
    split_ifs <;> omega
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) hb
  have hh := hc k
  norm_num at hp
  omega

/-- This specialization supplies the convolution theorem's assignment
word and digit bounds from the actual source, rather than assuming them.
The fixed stencil and high-mask word bindings stay explicit. -/
theorem source_sparse_convolution (ports : Fin 4 → ℤ) {MF : ℕ}
    (h : Interface ports (89 * cellLength) NativeLowPort54.lowPort MF)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (hq : sourceQ ports x = (2 ^ (89 * cellLength)) ^ N)
    (hK : (ports 1).toNat = rawWord radix)
    (m : ZMod (N * cellLength) → ℕ) (hm : ∀ k, m k < radix)
    (hM : word radix m = MF * x 0 - 1) :
    ∃ c : ZMod (N * cellLength) → ℕ,
      word radix c = gap ports x ∧ c 0 = 1 ∧
      (∀ k, c k < 2 ^ periodicBits k) ∧ (∀ k, c k ≤ 3) ∧
      ∀ k, (convolution folded c k + NativeWindowConvolution54.temporalDigits x c k) &&& m k = 0 := by
  obtain ⟨c, hc, hc0, hbits, hb⟩ := source_assignment ports h x hx hs hq
  refine ⟨c, hc, hc0, hbits, hb, ?_⟩
  apply NativeWindowConvolution54.source_convolution_mask_digits ports h x hx hs c m hb hm hc _ hK hM
  rw [hq, radix, ← pow_mul, ← pow_mul]
  congr 1
  ring

/-- The nonzero cyclic length is justified by the source's positive
cell count. No word or digit property is included among its parameters. -/
def Reconstruction (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) (N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * cellLength) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  ∃ c : ZMod (N * cellLength) → ℕ,
    word radix c = gap ports x ∧ c 0 = 1 ∧
    (∀ k, c k < 2 ^ periodicBits k) ∧ (∀ k, c k ≤ 3)

/-- Neither the cyclic length nor the sparse assignment is supplied:
both are extracted from the positive source and the exact low-port recipe. -/
theorem source_assignment_exists (ports : Fin 4 → ℤ) {MF : ℕ}
    (h : Interface ports (89 * cellLength) NativeLowPort54.lowPort MF)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    ∃ N, ∃ hN : 0 < N, Reconstruction ports x N hN := by
  obtain ⟨N, hN, hq, _, _, _, _⟩ := source_mask_tests ports h x hx hs
  refine ⟨N, hN, ?_⟩
  letI : NeZero (N * cellLength) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  exact source_assignment ports h x hx hs hq

end DiophantineConsistency.NativeSparseDigits54
