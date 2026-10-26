import DiophantineConsistency.CurrentClause2011

namespace DiophantineConsistency.CurrentClause2011Checks

open CurrentClause2011 CurrentMasks2011

set_option Elab.async false

-- Spatial subtraction crosses a cell boundary even when it does not cross
-- the entire cyclic word. Only the residue, not the absolute index, is996.
example : ((0 : ZMod (2 * 2011)) + 1005 - 2020).val = 3007 ∧
    ((0 : ZMod (2 * 2011)) + 1005 - 2020).val % 2011 = 996 := by decide

-- Both unwanted clause inputs are excluded from the actual full support.
example : 987 ∉ lowSupport ∧ 996 ∉ lowSupport ∧ 1 ∈ lowSupport := by
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_singleton]
  omega

-- The later cell's full clause mask is unaffected by the global origin subtraction.
example : CurrentHighDigits2011.maskDigits (N := 2) (2011 + 1005) = 2 ^ 45 - 4 :=
  clause_mask 2011 (by decide)

#print axioms addition_residue
#print axioms subtraction_residue
#print axioms clause_mask
#print axioms clause_convolution
#print axioms selectorCount_eq_prefix
#print axioms clause_low_residue
#print axioms normalized_clause_residue
#print axioms normalized_clause_mask

end DiophantineConsistency.CurrentClause2011Checks
