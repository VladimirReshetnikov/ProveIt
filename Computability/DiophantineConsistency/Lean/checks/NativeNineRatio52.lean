import DiophantineConsistency.NativeNineRatio52

open DiophantineConsistency.NativeNineRatio52

private def boundary : NewVars := ⟨1, 1, 1, 0, 1, 0⟩

-- A zero new index is admitted and converts to a positive old index while
-- preserving the actual H register of the existing Jones interface.
example : 0 < boundary.toOldIndex 8 8 1 0 100 ∧
    (boundary.old 8 8 1 0 100 (boundary.toOldIndex 8 8 1 0 100)).H =
      boundary.Hnew 8 8 1 0 100 :=
  toOldIndex_correct boundary (by decide) (by decide) (by decide) (by decide) (by decide)

example : 0 < (boundary.base 8 8 1 0 100).B' ∧
    (boundary.base 8 8 1 0 100).B' < (boundary.base 8 8 1 0 100).C ∧
    0 < (boundary.base 8 8 1 0 100).F :=
  register_bounds boundary (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms NewVars.base
#print axioms NewVars.toOldIndex
#print axioms exists_conditions_iff
#print axioms ratio_sound_new
#print axioms ratio_complete_new
