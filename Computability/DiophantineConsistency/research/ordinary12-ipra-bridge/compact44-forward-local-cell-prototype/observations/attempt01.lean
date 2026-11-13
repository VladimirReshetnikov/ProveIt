import DiophantineConsistency.CompactCoefficientDecoder

/-!
Exploratory source, not yet compiled.  This isolates one finite arithmetic
step toward constructing a compact cell.  The hypotheses assert the three
finite sums needed for an occupied selected row; this file does not derive
them from a cyclic word or a physical cell, and does not establish a mask or
graph equation.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CompactForwardLocalCell
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Conditional occupied-case aggregate value, for the actual 943-row
selector coefficients and 41 copy coefficients. -/
theorem occupied_aggregate (f : Fin 943 → V) (b : Fin 41 → V) (i : Fin 943)
    (hcount : (∑ j, f j) = 1)
    (hselected : (∑ j, (Exp.exp 41 - Compact943Decoder.tileValue (V := V) j) * f j) =
      Exp.exp 41 - Compact943Decoder.tileValue (V := V) i)
    (hcopy : (∑ j, (2 : V)^j.val * b j) = Compact943Decoder.tileValue (V := V) i) :
    (∑ j, ((CompactCoefficientMass.selector (Compact943Data.row j) : ℕ) : V) * f j) +
      (∑ j, ((2^(10+j.val) : ℕ) : V) * b j) = 1 + Exp.exp 51 := by
  rw [CompactCoefficientDecoder.finite_decomposition, hcount, hselected, hcopy,
    tsub_add_cancel_of_le (Compact943Decoder.tileValue_bounds (V := V) i).2.le]
  have hexp : Exp.exp (10 : V) * Exp.exp 41 = Exp.exp 51 := by
    rw [← exp_add]
    congr 1 <;> norm_num
  rw [hexp]

#print axioms CompactForwardLocalCell.occupied_aggregate
end CompactForwardLocalCell
