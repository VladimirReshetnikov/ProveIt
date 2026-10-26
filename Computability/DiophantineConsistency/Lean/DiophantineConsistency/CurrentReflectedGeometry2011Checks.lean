import DiophantineConsistency.CurrentReflectedGeometry2011

namespace DiophantineConsistency.CurrentReflectedGeometry2011Checks

open CurrentReflectedGeometry2011 CurrentKernel2011 CurrentMasks2011
open scoped BigOperators

set_option Elab.async false

-- Actual west/east weights and positions, rather than convenience labels.
example : position (.inr (.inl (0 : Fin 8))) = 978 ∧
    2 * weight (.inr (.inl (0 : Fin 8))) = 2048 ∧
    position (.inr (.inr (.inr (.inl (0 : Fin 8))))) = 969 ∧
    2 * weight (.inr (.inr (.inr (.inl (0 : Fin 8))))) = 2 ^ 28 := by decide

-- The first reflected term is the last west bit, at output20 and source0.
example : position (.inr (.inl (7 : Fin 8))) = 985 ∧
    source 20 (.inr (.inl (7 : Fin 8))) = 0 ∧
    2 * weight (.inr (.inl (7 : Fin 8))) = 2 ^ 18 := by decide

-- A selector SOURCE can receive a control coefficient; the proof splits
-- by source position, not by the constructor of the coefficient entry.
example : source 1004 (.inr (.inr (.inr (.inr (0 : Fin 9))))) = 941 ∧
    2 * weight (.inr (.inr (.inr (.inr (0 : Fin 9))))) = 2 ^ 36 := by decide

-- The arbitrary Boolean dummy977 is included in the control-source bound.
example : source 1003 (.inr (.inl (1 : Fin 8))) = 977 ∧
    2 * weight (.inr (.inl (1 : Fin 8))) = 4096 := by decide

example : 985 ∈ lowSupport ∧ 986 ∉ lowSupport ∧
    1004 ∈ lowSupport ∧ 1005 ∉ lowSupport := by
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_singleton]
  decide

-- Exact full control sum and the conditional reset margin at the worst phase.
example : (∑ e : Control, 2 * weight (.inr e)) = 35184372086784 := by
  exact doubled_control_mass

example : (2 * 2 ^ 45 - 2048) + 3 + 2 ^ 46 + 57 =
    CurrentMasks2011.radix - 1988 ∧
    (2 * 2 ^ 45 - 2048) + 3 + 2 ^ 46 + 57 < CurrentMasks2011.radix := by decide

#print axioms position_injective
#print axioms doubled_weight_lt
#print axioms doubled_control_mass
#print axioms CurrentReflectedGeometry2011.reflected_even
#print axioms reflected_source
#print axioms reflected_cell
#print axioms reflected_zero_before_twenty
#print axioms selector_source_sum_le
#print axioms reflected_lt
#print axioms low_raw_budget
#print axioms outgoing_carry_zero
#print axioms copy_marker_incoming_zero

end DiophantineConsistency.CurrentReflectedGeometry2011Checks
