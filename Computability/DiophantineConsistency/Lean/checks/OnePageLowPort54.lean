import DiophantineConsistency.OnePageLowPort54

open DiophantineConsistency

namespace OnePageLowPort54Checks

set_option maxRecDepth 10000

example : OnePageTuple54.assignmentPositions.length = 520 := by decide
example : OnePageTuple54.assignmentPositions.Nodup := OnePageTuple54.assignmentPositions_nodup
example : OnePageTuple54.lowPort NativeStencil54.radix = NativeLowPort54.lowPort :=
  OnePageTuple54.lowPort_eq

theorem exact_subtraction :
    OnePageTuple54.lowPort NativeStencil54.radix +
      NativeLowPort54.removedWord NativeStencil54.radix + 1 =
        NativeStencil54.radix ^ NativeStencil54.cellLength := by
  rw [OnePageTuple54.lowPort_eq]
  exact NativeLowPort54.lowPort_exact

theorem origin_residue :
    OnePageTuple54.lowPort NativeStencil54.radix % NativeStencil54.radix =
      NativeStencil54.radix - 2 := by
  rw [OnePageTuple54.lowPort_eq]
  exact NativeLowPort54.lowPort_mod_radix

#print axioms OnePageTuple54.assignmentPositions_eq
#print axioms OnePageTuple54.assignmentPositions_nodup
#print axioms OnePageTuple54.lowPort_eq
#print axioms exact_subtraction
#print axioms origin_residue

end OnePageLowPort54Checks
