import DiophantineConsistency.CompactCoefficientDecoder
import DiophantineConsistency.CompactCopyBound
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLocalCoefficientDecoder
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Conditional local decoder over arbitrary selector/copy values. This does not identify a graph column. -/
theorem local_decode_iff (f : Fin 943 → V) (b : Fin 41 → V)
    (hf : ∀ i, f i ≤ 1) (hb : ∀ j, b j ≤ 1) :
    NoCarry ((∑ i, ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V)*f i) +
      (∑ j, ((2^(10+j.val):ℕ):V)*b j)) (Exp.exp 51-2) ↔
    ((∀ i, f i=0) ∧ (∑ j,(2:V)^j.val*b j)=0) ∨
      ∃ i, CompactSelectorSum.Selected f i ∧
        (∑ j,(2:V)^j.val*b j)=Compact943Decoder.tileValue (V:=V) i := by
  rw [CompactCoefficientDecoder.finite_decomposition]
  exact Compact943Decoder.decode_iff f (∑ j,(2:V)^j.val*b j) hf
    (CompactCopyBound.copy_bound b hb)

#print axioms CompactLocalCoefficientDecoder.local_decode_iff
end CompactLocalCoefficientDecoder
