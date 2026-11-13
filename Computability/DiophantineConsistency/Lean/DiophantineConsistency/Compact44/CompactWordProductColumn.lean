import DiophantineConsistency.Compact44.CompactWordCellClient
import DiophantineConsistency.Compact44.RawColumnBands

/-! Conditional column bridge. `C` is not constructed here: the source
selector/copy digit identities, the length bounds and the end-around carry
input are explicit assumptions. Both foreign-band and other contributions
remain in the resulting formula. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CompactWordProductColumn
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
  DiophantineConsistency.CompactHeterogeneousCarry
open CompactWordCellClient CompactMarkedTransport CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactPartialBand CompactPartialBandRotation RawColumnBands
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactIndexedFlatten CompactTwoBandFlatten
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
attribute [local irreducible] Compact943Data.rows rho paramKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- At target `8807*j+T`, a reflected offset `T-e` reads digit
`8807*j+e`, without wrap, whenever the target lies inside the word. -/
theorem source_index (n j : V) (T e : ℕ) (hk : 8807*j+(T:V)<n) (he : e≤T) :
    cyc n (8807*j+(T:V)) (((T-e:ℕ)):V) = 8807*j+(e:V) := by
  have hs : (e:V)+(((T-e:ℕ)):V)=(T:V) := by exact_mod_cast Nat.add_sub_of_le he
  have hoffle : (((T-e:ℕ)):V)≤8807*j+(T:V) := by
    rw [←hs]
    have h : (((T-e:ℕ)):V)≤(e:V)+(((T-e:ℕ)):V) := le_add_of_nonneg_left (by simp)
    exact le_trans h (le_add_of_nonneg_left (by simp))
  have hoff : (((T-e:ℕ)):V)<n := lt_of_le_of_lt hoffle hk
  rw [cyc_of_le hk hoff hoffle]
  apply (eq_tsub_of_add_eq ?_).symm
  rw [←hs]
  ring

/-- The selected reflected band's actual rotated-column sum is the word
cell aggregate, for either target `T ≥ 4393`, provided the packed word has
the indicated selector and payload digits. -/
theorem selected_band {b : V → V} {N s j n C : V} (hword : CompactWord b N s)
    (hj : j<N) (T : ℕ) (hT : 4393≤T) (hn : 0<n)
    (hk : 8807*j+(T:V)<n) (hC : C<Exp.exp (67*n))
    (hsel : ∀ i : Fin 943, dig 67 C (8807*j+(i.val:V))=wordSelector b i j)
    (hcopy : ∀ i : Fin 41, dig 67 C (8807*j+(position i:V))=wordPayloadBit b i j) :
    columnBand position T n C (8807*j+(T:V)) = 1+Exp.exp 51 := by
  have hs (i : Fin 943) : selectorDigit n C (8807*j+(T:V)) T i = wordSelector b i j := by
    unfold selectorDigit
    rw [source_index n j T i.val hk (by have := i.isLt; omega), hsel]
  have hc (i : Fin 41) : copyDigit position n C (8807*j+(T:V)) T i = wordPayloadBit b i j := by
    unfold copyDigit
    rw [source_index n j T (position i) hk (by have := position_lt_target i; omega), hcopy]
  rw [band_column position T n C _ hn hk hC, ← CompactCoefficientDecoder.finite_decomposition]
  simp_rw [hs, hc]
  exact word_occupied hword hj

abbrev Idx := Aligned (Fin 943) (Fin 41) ⊕ Unit
def coefficient : Idx → V :=
  GenericBandCarryFamily.coefficient (fun i : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies i:V))
def words (n C T : V) : Idx → V := GenericBandCarryFamily.word n C (bandOffsets position) T

/-- At the first target, the selected occupied band is known; the opposite
band, bare rotations, temporal digit, and incoming carry are retained. The
output is the actual symbolic kernel product plus the explicit temporal word,
reduced modulo the cyclic modulus. `CarryInput` and the packed source-digit
identities remain assumptions. -/
theorem first_target_product_digit {b : V → V} {N s j n C T bound : V}
    (hword : CompactWord b N s) (hj : j<N) (hn : 0<n)
    (hk : 8807*j+4393<n) (hC : C<Exp.exp (67*n))
    (hsel : ∀ i : Fin 943, dig 67 C (8807*j+(i.val:V))=wordSelector b i j)
    (hcopy : ∀ i : Fin 41, dig 67 C (8807*j+(position i:V))=wordPayloadBit b i j)
    (hcarry : CarryInput 67 n ((((paramKernel rho:ℕ):V)*C+T) % (Exp.exp (67*n)-1))
      bound (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) coefficient (words n C T)) :
    dig 67 ((((paramKernel rho:ℕ):V)*C+T) % (Exp.exp (67*n)-1)) (8807*j+4393) =
      ((1+Exp.exp 51) + columnBand position 5495 n C (8807*j+4393) +
        bareColumn n C (8807*j+4393) + dig 67 T (8807*j+4393) +
        carry 67 n coefficient (words n C T) (cyc n (8807*j+4393) 1)) % Exp.exp 67 := by
  have hband := selected_band hword hj 4393 (by norm_num) hn hk hC hsel hcopy
  simp only [Nat.cast_ofNat] at hband
  have hr := RawColumnBands.flatten position n C T (8807*j+4393)
  change raw 67 coefficient (words n C T) _ = _ at hr
  rw [hband] at hr
  rw [(carry_column hcarry hk).2, hr]

/-- The analogous identity for the second target. No foreign contribution
or incoming carry is assumed zero. -/
theorem second_target_product_digit {b : V → V} {N s j n C T bound : V}
    (hword : CompactWord b N s) (hj : j<N) (hn : 0<n)
    (hk : 8807*j+5495<n) (hC : C<Exp.exp (67*n))
    (hsel : ∀ i : Fin 943, dig 67 C (8807*j+(i.val:V))=wordSelector b i j)
    (hcopy : ∀ i : Fin 41, dig 67 C (8807*j+(position i:V))=wordPayloadBit b i j)
    (hcarry : CarryInput 67 n ((((paramKernel rho:ℕ):V)*C+T) % (Exp.exp (67*n)-1))
      bound (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) coefficient (words n C T)) :
    dig 67 ((((paramKernel rho:ℕ):V)*C+T) % (Exp.exp (67*n)-1)) (8807*j+5495) =
      (columnBand position 4393 n C (8807*j+5495) + (1+Exp.exp 51) +
        bareColumn n C (8807*j+5495) + dig 67 T (8807*j+5495) +
        carry 67 n coefficient (words n C T) (cyc n (8807*j+5495) 1)) % Exp.exp 67 := by
  have hband := selected_band hword hj 5495 (by norm_num) hn hk hC hsel hcopy
  simp only [Nat.cast_ofNat] at hband
  have hr := RawColumnBands.flatten position n C T (8807*j+5495)
  change raw 67 coefficient (words n C T) _ = _ at hr
  rw [hband] at hr
  rw [(carry_column hcarry hk).2, hr]

#print axioms CompactWordProductColumn.source_index
#print axioms CompactWordProductColumn.selected_band
#print axioms CompactWordProductColumn.first_target_product_digit
#print axioms CompactWordProductColumn.second_target_product_digit
end CompactWordProductColumn
