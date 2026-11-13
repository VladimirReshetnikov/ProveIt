module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCommandHInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCommandStepGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Discrete-order separation, valid for nonstandard values too. -/
theorem four_mul_ne_four_mul_add_two (a b : V) : 4*a≠4*b+2 := by
  have h24 : (2 : V)<4 := calc
    (2 : V) < 2+1 := by simp
    _ ≤ (2+1)+1 := le_add_of_nonneg_right (by simp)
    _ = 4 := by rw [two_add_one_eq_three,three_add_one_eq_four]
  rcases le_or_gt a b with hab|hba
  · have hm := mul_le_mul_of_nonneg_left hab (show (0 : V)≤4 by simp)
    exact ne_of_lt (lt_of_le_of_lt hm (by simp))
  · have hm := mul_le_mul_of_nonneg_left (succ_le_iff_lt.mpr hba) (show (0 : V)≤4 by simp)
    have hh : 4*b+4≤4*a := by simpa only [mul_add,mul_one] using hm
    have hl : 4*b+2<4*b+4 := by simpa only [add_comm] using add_lt_add_left h24 (4*b)
    exact ne_of_gt (lt_of_lt_of_le hl hh)

theorem implication_ne_universal (a b c d : V) :
    ActualArithmeticGraph.eval implicationExpr a b 0 0 ≠
      ActualArithmeticGraph.eval universalExpr c d 0 0 := by
  simpa [implicationExpr,universalExpr,im,al,ActualArithmeticGraph.eval] using
    four_mul_ne_four_mul_add_two (pairValue a b) (pairValue c d)

theorem source_pair_eq_zero (a b : V) : pairValue a b=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro hh
    have h0 : pairValue (0 : V) 0=0 := by simp [pairValue]
    exact pairValue_injective (hh.trans h0.symm)
  · rintro ⟨rfl,rfl⟩
    simp [pairValue]

theorem implication_eq_zero (a b : V) :
    ActualArithmeticGraph.eval implicationExpr a b 0 0=0 ↔ a=0 ∧ b=0 := by
  simp [implicationExpr,im,ActualArithmeticGraph.eval,source_pair_eq_zero]

#print axioms four_mul_ne_four_mul_add_two
#print axioms implication_eq_zero
end M6.PA.ActualCommandStepGraph
