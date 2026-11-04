import DiophantineConsistency.Compact44.CompactOriginBlockResidue
import DiophantineConsistency.Compact44.CompactHighOriginResidue
import DiophantineConsistency.Compact44.CompactCellPulseEquality
import DiophantineConsistency.Compact44.CompactWordLowFields

/-! Transfer ordinary all-index high-mask safety to the special origin. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHighOriginMarked
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactMarkedTransport CompactUniformPackedCell CompactPackedCell
open CompactCellPulseEquality CompactWordLowFields CompactOriginBlockResidue CompactHighOriginResidue
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For normalized cells, a single ordinary high-mask no-carry condition at
all indices entails the special decremented-mask origin and non-origin fields. -/
theorem normalized_high_fields {row dummy : V → V} {N s : V}
    (hw : CompactWord row N s) (hs : 0<s) (hsN : s<N)
    (hall : ∀ j<N, NoCarry
      (blk 590069 (paramKernel rho : V) N s (fun k => normalizedCell (row k) (dummy k)) j)
      (highNat : V)) :
    NoCarry (blk 590069 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (dummy k)) 0) ((highNat : V)-1) ∧
    ∀ j<N, 0<j → NoCarry (blk 590069 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (dummy k)) j) (highNat : V) := by
  constructor
  · exact symbolic_high_origin _ (marked_origin_block_mod_four hw hs hsN) (hall 0 hw.pos)
  · intro j hj _; exact hall j hj

/-- The same origin reduction for the zero-dummy base family. -/
theorem base_high_fields {row : V → V} {N s : V}
    (hw : CompactWord row N s) (hs : 0<s) (hsN : s<N)
    (hall : ∀ j<N, NoCarry (blk 590069 (paramKernel rho : V) N s (baseCell row) j) (highNat : V)) :
    NoCarry (blk 590069 (paramKernel rho : V) N s (baseCell row) 0) ((highNat : V)-1) ∧
    ∀ j<N, 0<j → NoCarry (blk 590069 (paramKernel rho : V) N s (baseCell row) j) (highNat : V) := by
  have he : (fun j => normalizedCell (row j) (0:V)) = baseCell row := by
    funext j
    simp [normalizedCell, baseCell]
  have hn : ∀ j<N, NoCarry (blk 590069 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (0:V)) j) (highNat : V) := by rw [he]; exact hall
  have h := normalized_high_fields hw hs hsN hn
  rwa [he] at h

/-- The same origin reduction for the explicit Boolean-pulsed family. -/
theorem pulsed_high_fields {row δ : V → V} {N s : V}
    (hw : CompactWord row N s) (hs : 0<s) (hsN : s<N) (hbool : ∀ j, δ j ≤ 1)
    (hall : ∀ j<N, NoCarry (blk 590069 (paramKernel rho : V) N s (pulsedCell row δ) j) (highNat : V)) :
    NoCarry (blk 590069 (paramKernel rho : V) N s (pulsedCell row δ) 0) ((highNat : V)-1) ∧
    ∀ j<N, 0<j → NoCarry (blk 590069 (paramKernel rho : V) N s (pulsedCell row δ) j) (highNat : V) := by
  have he : (fun j => normalizedCell (row j) (δ j)) = pulsedCell row δ := by
    funext j
    change normalizedCell (row j) (δ j) = packedCell (row j) 0 + Exp.exp (67*1063)*δ j
    rw [normalized_eq_pulse, mod_eq_self_of_lt (lt_two_iff_le_one.mpr (hbool j))]
  have hn : ∀ j<N, NoCarry (blk 590069 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (δ k)) j) (highNat : V) := by rw [he]; exact hall
  have h := normalized_high_fields hw hs hsN hn
  rwa [he] at h

#print axioms CompactHighOriginMarked.normalized_high_fields
#print axioms CompactHighOriginMarked.base_high_fields
#print axioms CompactHighOriginMarked.pulsed_high_fields
end CompactHighOriginMarked
