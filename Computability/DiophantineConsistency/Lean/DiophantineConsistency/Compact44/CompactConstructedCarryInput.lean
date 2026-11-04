import DiophantineConsistency.Compact44.CompactWordCellClient
import DiophantineConsistency.Compact44.CompactTwoBandCarry
import DiophantineConsistency.Compact44.SymbolicKBandDraft
import DiophantineConsistency.ArithmeticPackingBlocks

/-! Bounded word packing and exact-product carry input. The local cell
digits, their radix bounds and the temporal-word size are hypotheses; no
other-band contribution or incoming carry is assumed to vanish. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CompactConstructedCarryInput
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticPackingBlocks
  DiophantineConsistency.CompactHeterogeneousCarry
open CompactWordCellClient CompactMarkedTransport CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactPartialBandRotation CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
attribute [local irreducible] Compact943Data.rows rho paramKernel selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A base-`2^67` subdigit inside a base-`2^(67*8807)` block. -/
theorem subdigit (C j p : V) (hp : p<8807) :
    dig 67 (dig (67*8807) C j) p = dig 67 C (8807*j+p) := by
  calc
    _ = dig 67 ((C / Exp.exp ((67*8807)*j)) % Exp.exp (67*8807)) p := by rfl
    _ = dig 67 (C / Exp.exp ((67*8807)*j)) p := dig_mod 67 _ p 8807 hp
    _ = dig 67 C (8807*j+p) := by
      unfold dig
      rw [← Arithmetic.div_mul, ← exp_add]
      congr 1
      congr 1
      ring_nf

/-- The represented block sum has precisely the cell's subdigits. -/
theorem packed_digit (X : V → V) [𝚺₁-Function₁ X] (N j p : V)
    (hX : ∀ j<N, X j<Exp.exp (67*8807)) (hj : j<N) (hp : p<8807) :
    dig 67 (bsum (67*8807) X N) (8807*j+p) = dig 67 (X j) p := by
  rw [← subdigit, dig_bsum hX hj]
  exact hp

/-- Cell-wise digit cap transfers to the entire packed source word. -/
theorem packed_cap (X : V → V) [𝚺₁-Function₁ X] (N : V)
    (hX : ∀ j<N, X j<Exp.exp (67*8807))
    (hcap : ∀ j<N, ∀ p<8807, dig 67 (X j) p≤3) :
    ∀ k<8807*N, dig 67 (bsum (67*8807) X N) k≤3 := by
  intro k hk
  have hj : k/8807<N := div_lt_of_lt_mul (by simpa only [mul_comm] using hk)
  have hp : k%8807<8807 := mod_lt k (by norm_num)
  have he : 8807*(k/8807)+k%8807=k := div_add_mod k 8807
  rw [←he, packed_digit X N _ _ hX hj hp]
  exact hcap _ hj _ hp

/-- A concrete exact-product end-around carry input, without assuming a
graph zero or assuming the incoming carry vanishes. -/
theorem symbolic_product_carry (n C T : V) (hn : 0<n) (hM : 0<Exp.exp (67*n)-1)
    (hC : C<Exp.exp (67*n)) (hcap : ∀ k<n, dig 67 C k≤3)
    (hT : T<Exp.exp (67*n)) :
    CarryInput 67 n ((((paramKernel rho:ℕ):V)*C+T) % (Exp.exp (67*n)-1)) 1
      (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x:V)))
      (GenericBandCarryFamily.word n C (bandOffsets position) T) := by
  let M : V := Exp.exp (67*n)-1
  let K : V := ((paramKernel rho:ℕ):V)
  have hK : K = kernelBand position 4393 + kernelBand position 5495 + TwoBand.bareKernel :=
    SymbolicKBandDraft.symbolic_kernel_band_cast
  have hbase := TwoBand.combined_congr position K n C 0 ((K*C)%M) hn hM hK (by simp [M])
  have hbase' : (rotatedBand position 4393 n C + rotatedBand position 5495 n C +
      TwoBand.bareRotated n C)%M=(K*C)%M := by simpa using hbase
  have hgraph := TwoBand.add_congr_mod M _ _ T T hM hbase' rfl
  have hTcap : ∀ k<n, dig 67 T k≤Exp.exp 67-1 := fun k _ =>
    le_tsub_of_add_le_right (lt_iff_succ_le.mp (dig_lt 67 T k))
  exact CompactTwoBandCarry.carry_input position n C T ((K*C+T)%M) hn hM hC hcap hT hTcap
    (mod_lt _ hM) hgraph

/-- The two families required by the selected-band client follow from
cell-level selector and copy identities, rather than assumptions about the
whole packed word. -/
theorem packed_word_digits {b X : V → V} [𝚺₁-Function₁ X] {N s j : V}
    (_hword : CompactWord b N s) (hj : j<N)
    (hX : ∀ t<N, X t<Exp.exp (67*8807))
    (hsel : ∀ i : Fin 943, dig 67 (X j) (i.val:V)=wordSelector b i j)
    (hcopy : ∀ i : Fin 41, dig 67 (X j) (position i:V)=wordPayloadBit b i j) :
    (∀ i : Fin 943, dig 67 (bsum (67*8807) X N) (8807*j+(i.val:V))=wordSelector b i j) ∧
    (∀ i : Fin 41, dig 67 (bsum (67*8807) X N) (8807*j+(position i:V))=wordPayloadBit b i j) := by
  constructor
  · intro i
    rw [packed_digit X N j _ hX hj (by exact_mod_cast (show i.val<8807 by have := i.isLt; omega)), hsel]
  · intro i
    rw [packed_digit X N j _ hX hj (by exact_mod_cast (show position i<8807 by have := position_lt_target i; omega)), hcopy]

#print axioms CompactConstructedCarryInput.subdigit
#print axioms CompactConstructedCarryInput.packed_digit
#print axioms CompactConstructedCarryInput.packed_cap
#print axioms CompactConstructedCarryInput.symbolic_product_carry
#print axioms CompactConstructedCarryInput.packed_word_digits
end CompactConstructedCarryInput
