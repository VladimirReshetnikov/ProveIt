import CompactMarkedAllHigh
import CompactHighOriginMarked

/-! Exact base and Boolean-pulsed high-mask fields of compact packing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactMarkedHighFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactConstructedWord CompactUniformPackedCell CompactWordPulseEquality CompactWordLowFields
open CompactMarkedAllHigh CompactHighOriginMarked
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Both high-mask fields for the actual zero-dummy base cells and any
    globally Boolean pulsed cells. -/
theorem marked_high_fields (row δ : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ δ]
    {N s : V} (hw : CompactWord row N s) (hN : 1<N) (hs0 : 0<s) (hs : s<N)
    (hbool : ∀ j, δ j ≤ 1) :
    (NoCarry (blk 590069 (paramKernel rho : V) N s (baseCell row) 0) ((highNat:V)-1) ∧
      ∀ j<N, 0<j → NoCarry (blk 590069 (paramKernel rho : V) N s (baseCell row) j) (highNat:V)) ∧
    (NoCarry (blk 590069 (paramKernel rho : V) N s (pulsedCell row δ) 0) ((highNat:V)-1) ∧
      ∀ j<N, 0<j → NoCarry (blk 590069 (paramKernel rho : V) N s (pulsedCell row δ) j) (highNat:V)) := by
  let zero : V → V := fun _ => 0
  letI : 𝚺₁-Function₁ zero := by dsimp [zero]; definability
  have he0 : cellWord row zero = baseCell row := by
    funext j
    simp [cellWord, normalizedCell, baseCell, zero]
  have heδ : cellWord row δ = pulsedCell row δ := by
    funext j
    change cellWord row δ j = packedCell (row j) 0 + Exp.exp (67*1063)*δ j
    exact cellWord_boolean_pulse row δ j (hbool j)
  have hall0 := marked_all_high row zero hw hN hs (by intro j; simp [zero])
  have hallδ := marked_all_high row δ hw hN hs hbool
  rw [he0] at hall0
  rw [heδ] at hallδ
  exact ⟨base_high_fields hw hs0 hs hall0, pulsed_high_fields hw hs0 hs hbool hallδ⟩

#print axioms CompactMarkedHighFields.marked_high_fields
end CompactMarkedHighFields
