import DiophantineConsistency.Source34.Source34Block
import DiophantineConsistency.Mixed121.Mixed121Column
import DiophantineConsistency.Source34.Source34Carry
import DiophantineConsistency.Mixed121.W121.TemporalOtherWindows
import DiophantineConsistency.Compact44.CompactBooleanZeroCarry
import DiophantineConsistency.Compact44.CompactPartialPackingTransport

/-! # Physical block digits are carry-free raw columns, at the source34 ports

`Mixed121Column` at the source34 tuple. For a packed word `C` with Boolean
digits, every band word and the aligned temporal word (exponent `121·e`) has
Boolean digits. The stencil mass `Σ + 1` is below `2^111`, so every cyclic
carry of the exact remainder `((K + 2^(121e))·C) mod (2^(121n) − 1)` vanishes
and each of its digits is the raw column (`aligned_stencil_zero_carry`), now
over the source34 band offsets and bare offsets (`Source34Rotation`,
`Source34Flatten`). For the constructed word this remainder is the packing's
transport word `Fw`, so each physical block digit is its raw column
(`marked_physical_column`).

Generic and used from `Mixed121Column`: `Idx`, `coeff`, `aligned_digit`,
`stencil_mass_room`, `stencil_zero_carry`, `perturb`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Source34Column
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticStandardCasts ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPackingBlocks
  ArithmeticPacking CompactHeterogeneousCarry
open CompactMarkedTransport CompactPartialPackingTransport CompactGenericAlignedMass
open Mixed121Kernel (rho)
open Source34Kernel Source34Rotation Source34Flatten Mixed121Temporal Source34Cell Source34Word
  Source34Block
open Mixed121Rotation (coefficient word cap add_congr_mod aligned_rotation_bounds)
open Mixed121Flatten (selectors copies aligned_mass_lt)
open Mixed121Word (subdigit)
open Mixed121Column (Idx coeff aligned_digit stencil_mass_room stencil_zero_carry perturb
  perturb_definable)
attribute [local irreducible] paramKernel rho Compact943Data.rows Source34Ports.lowNat
  Source34Ports.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Carry inputs for an arbitrary source word -/

/-- The exact-product end-around carry input, without a graph zero. -/
theorem symbolic_product_carry (n C T : V) (hn : 0<n) (hM : 0<Exp.exp (121*n)-1)
    (hC : C<Exp.exp (121*n)) (hcap : ∀ k<n, dig 121 C k≤3)
    (hT : T<Exp.exp (121*n)) :
    CarryInput 121 n ((((paramKernel rho:ℕ):V)*C+T) % (Exp.exp (121*n)-1)) 1
      (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) coeff (word 121 n C bandOffsets T) := by
  let M : V := Exp.exp (121*n)-1
  let K : V := ((paramKernel rho:ℕ):V)
  have hK : K = kernelBand 4393 + kernelBand 5495 + bareKernel := kernel_bands
  have hbase := combined_congr K n C 0 ((K*C)%M) hn hM hK (by simp [M])
  have hbase' : (rotatedBand 4393 n C + rotatedBand 5495 n C + bareRotated n C)%M=(K*C)%M := by
    simpa using hbase
  have hgraph := add_congr_mod M _ _ T T hM hbase' rfl
  have hTcap : ∀ k<n, dig 121 T k≤Exp.exp 121-1 := fun k _ =>
    le_tsub_of_add_le_right (lt_iff_succ_le.mp (dig_lt 121 T k))
  exact Source34Carry.carry_input n C T ((K*C+T)%M) hn hM hC hcap hT hTcap (mod_lt _ hM) hgraph

/-- The same for `(K + 2^e)·C`, with the temporal term rotated. -/
theorem temporal_product_carry (n e C : V) (hn : 0<n)
    (hM : 0<Exp.exp (121*n)-1) (hC : C<Exp.exp (121*n))
    (hcap : ∀ k<n, dig 121 C k≤3) :
    CarryInput 121 n (((((paramKernel rho:ℕ):V)+Exp.exp e)*C) % (Exp.exp (121*n)-1)) 1
      (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) coeff
      (word 121 n C bandOffsets (temporalWord n e C)) := by
  let M : V := Exp.exp (121*n)-1
  let K : V := ((paramKernel rho:ℕ):V)
  have hT := temporal_word_lt n e C hn hC
  have hc := symbolic_product_carry n C (temporalWord n e C) hn hM hC hcap hT
  have ht := temporal_mod n e C hn hM
  have heq : (K*C+temporalWord n e C)%M=((K+Exp.exp e)*C)%M := by
    rw [add_mul]
    exact add_congr_mod M _ _ _ _ hM rfl ht.symm
  rwa [heq] at hc

theorem word_temporal_boolean (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N e k : V) (hN : 0 < N) (hk : k < 8801*N) :
    dig 121 (temporalWord (8801*N) (121*e) (packedWord row dummy N)) k ≤ 1 := by
  have hn : 0 < (8801:V)*N := mul_pos (by norm_num) hN
  have hC : packedWord row dummy N < Exp.exp (121*(8801*N)) := by
    simpa only [mul_assoc] using packedWord_lt row dummy N
  rw [aligned_digit _ _ _ _ hn hk hC]
  exact word_cap row dummy N _ (cyc_lt hn _ _)

/-! ## Zero carry -/

/-- Boolean sources and an aligned temporal exponent give carry-free columns. -/
theorem aligned_stencil_zero_carry (n e C : V) (hn : 0 < n)
    (hM : 0 < Exp.exp (121*n)-1) (hC : C < Exp.exp (121*n))
    (hcap : ∀ k < n, dig 121 C k ≤ 1) :
    ∀ k < n,
      carry 121 n (coeff : Idx → V) (word 121 n C bandOffsets (temporalWord n (121*e) C)) k = 0 ∧
      dig 121 (((((paramKernel rho : ℕ) : V) + Exp.exp (121*e))*C) % (Exp.exp (121*n)-1)) k =
        raw 121 coeff (word 121 n C bandOffsets (temporalWord n (121*e) C)) k := by
  have hcap3 : ∀ k < n, dig 121 C k ≤ 3 := fun k hk => le_trans (hcap k hk) (by norm_num)
  have hc := temporal_product_carry n (121*e) C hn hM hC hcap3
  have hbool : ∀ i : Idx, ∀ k < n,
      dig 121 (word 121 n C bandOffsets (temporalWord n (121*e) C) i) k ≤ 1 := by
    intro i k hk
    cases i with
    | inl i =>
      exact (aligned_rotation_bounds 121 n C (bandOffsets i) 1 hn hC hcap).2 k hk
    | inr i =>
      change dig 121 (temporalWord n (121*e) C) k ≤ 1
      rw [aligned_digit C n e k hn hk hC]
      exact hcap _ (cyc_lt hn k (e%n))
  exact stencil_zero_carry hc hbool

theorem packed_word_zero_carry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N e : V) (hN : 0 < N) :
    ∀ k < 8801*N,
      carry 121 (8801*N) (coeff : Idx → V)
        (word 121 (8801*N) (packedWord row dummy N) bandOffsets
          (temporalWord (8801*N) (121*e) (packedWord row dummy N))) k = 0 ∧
      dig 121 (((((paramKernel rho : ℕ) : V) + Exp.exp (121*e)) * packedWord row dummy N) %
          (Exp.exp (121*(8801*N))-1)) k =
        raw 121 coeff (word 121 (8801*N) (packedWord row dummy N) bandOffsets
          (temporalWord (8801*N) (121*e) (packedWord row dummy N))) k := by
  have hn : 0 < (8801 : V)*N := mul_pos (by norm_num) hN
  have he : (1 : V) ≤ 121*((8801:V)*N) :=
    pos_iff_one_le.mp (mul_pos (by norm_num) hn)
  have htwo : (2 : V) ≤ Exp.exp (121*(8801*N)) := by
    simpa using exp_monotone_le.mpr he
  have hM : 0 < Exp.exp (121*(8801*N))-1 :=
    tsub_pos_of_lt (lt_of_lt_of_le (by norm_num) htwo)
  have hC : packedWord row dummy N < Exp.exp (121*(8801*N)) := by
    simpa only [mul_assoc] using packedWord_lt row dummy N
  exact aligned_stencil_zero_carry _ _ _ hn hM hC (word_cap row dummy N)

/-! ## Cell sums and the physical column -/

/-- Boolean pulses preserve the small-cell size for both block-size bounds. -/
theorem marked_cell_sums {N s : V} (row δ : V → V)
    (hw : CompactWord row N s) (hbool : ∀ j < N, δ j ≤ 1) :
    let X0 : V → V := fun j => packedCell (row j) 0
    (∀ j < N, X0 j + blk 1064921 (paramKernel rho : V) N s X0 j < Exp.exp 1064921) ∧
    (∀ j < N, perturb X0 δ j + blk 1064921 (paramKernel rho : V) N s (perturb X0 δ) j <
      Exp.exp 1064921) := by
  let X0 : V → V := fun j => packedCell (row j) 0
  have hbase : ∀ j < N, X0 j < Exp.exp (121*3297+1 : V) := by
    intro j hj
    have hs := packedCell_lt_support (row j) 0 (hw.tile_ne j hj) (by simp)
    exact lt_of_lt_of_le hs (exp_monotone_le.mpr (by norm_num))
  have hpulse : ∀ j < N, perturb X0 δ j < Exp.exp (121*3297+1 : V) := by
    intro j hj
    rcases le_one_iff_eq_zero_or_one.mp (hbool j hj) with hz | ho
    · simpa [perturb, hz] using hbase j hj
    · simpa [perturb, X0, ho] using cell_pulse_lt (row j) (hw.tile_ne j hj)
  exact ⟨cell_sum_of_small hw.pos hbase, cell_sum_of_small hw.pos hpulse⟩

/-- Each physical block digit equals the exact raw stencil column, and the
same column has zero cyclic carry, for every valid cell and local phase. -/
theorem marked_physical_column (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hN : 1 < N) (hs : s < N)
    (hbool : ∀ j, dummy j ≤ 1) :
    ∀ j < N, ∀ q < 8801,
      let C := packedWord row dummy N
      let W := word 121 (8801*N) C bandOffsets (temporalWord (8801*N) (121*(8801*s)) C)
      carry 121 (8801*N) (coeff : Idx → V) W (8801*j+q) = 0 ∧
      dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) q =
        raw 121 coeff W (8801*j+q) := by
  have hXeq : cellWord row dummy = perturb (fun j => packedCell (row j) 0) dummy := by
    funext j
    exact cellWord_boolean_pulse row dummy j (hbool j)
  have hhi : ∀ j < N, (paramKernel rho : V) * cellWord row dummy j <
      Exp.exp 1064921 * Exp.exp 1064921 := by
    intro j hj
    rw [hXeq]
    rcases le_one_iff_eq_zero_or_one.mp (hbool j) with hz | ho
    · simpa only [perturb, hz, mul_zero, add_zero] using
        (packed_cell_product_lt (row j) 0 (hw.tile_ne j hj) (by simp))
    · simpa only [perturb, ho, mul_one] using
        (packed_pulse_product_lt (row j) (hw.tile_ne j hj))
  have hcell : ∀ j < N, cellWord row dummy j +
      blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j < Exp.exp 1064921 := by
    rw [hXeq]
    exact (marked_cell_sums row dummy hw (fun j _ => hbool j)).2
  have horigin : 1 ≤ cellWord row dummy 0 := by
    change 1 ≤ normalizedCell (row 0) (dummy 0)
    unfold normalizedCell
    rw [hw.marker]
    exact packedCell_origin (dummy 0 % 2) (lt_two_iff_le_one.mp (mod_lt _ (by norm_num)))
  letI : 𝚺₁-Function₁ (cellWord row dummy) := word_definable row dummy
  have ht : TransportInput 1064921 (paramKernel rho : V) N s (cellWord row dummy) :=
    ⟨hN, hs, hhi, hcell, horigin⟩
  have hD : (121 : V) * 8801 = 1064921 := by norm_num
  have hCeq : Cw 1064921 N (cellWord row dummy) = packedWord row dummy N := by
    unfold Cw packedWord
    rw [← hD]
  have hremainder :
      (((((paramKernel rho : ℕ) : V) + Exp.exp (121*(8801*s))) * packedWord row dummy N) %
        (Exp.exp (121*(8801*N))-1)) = Fw 1064921 (paramKernel rho : V) N s (cellWord row dummy) := by
    have hr := transport_residue ht
    rw [hCeq] at hr
    simpa only [← mul_assoc, hD] using hr
  intro j hj q hq
  have hk : 8801*j+q < 8801*N := by
    calc
      8801*j+q < 8801*j+8801 := by
        simpa only [add_comm] using add_lt_add_left hq (8801*j)
      _ = 8801*(j+1) := by ring
      _ ≤ 8801*N := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hj) (by norm_num)
  have hc := packed_word_zero_carry row dummy N (8801*s) hw.pos (8801*j+q) hk
  have hd : dig 121 (Fw 1064921 (paramKernel rho : V) N s (cellWord row dummy)) (8801*j+q) =
      dig 121 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j) q := by
    have hb := blk_lt ht
    unfold Fw
    have hsub := subdigit
      (bsum 1064921 (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy)) N) j q hq
    rw [hD, dig_bsum hb hj] at hsub
    exact hsub.symm
  rw [hremainder, hd] at hc
  exact hc

#print axioms Source34Column.temporal_product_carry
#print axioms Source34Column.packed_word_zero_carry
#print axioms Source34Column.marked_physical_column
end Source34Column
