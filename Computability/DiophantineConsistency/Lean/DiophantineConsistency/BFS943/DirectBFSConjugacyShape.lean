import DiophantineConsistency.BFS943.DirectBFSConjugacyBase

/-! Finite shapes and distinguished symbols for the BFS conjugacy candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSConjugacyShape
open DirectBFSConjugacyBase

theorem array_sizes : horizontal.size=250 ∧ horizontalInverse.size=250 ∧
    vertical.size=439 ∧ verticalInverse.size=439 ∧ rowMap.size=943 ∧ rowInverse.size=943 ∧
    original.size=943 ∧ direct.size=943 := by decide

theorem distinguished_rows : rowMap.getD 0 999=0 ∧ rowMap.getD 1 999=1 := by decide

theorem fixed_horizontal : (List.range 6).all (fun i => decide (horizontal.getD i 999=i))=true := by decide

theorem fixed_vertical : ([0,1,434,435,436,437,438] : List Nat).all
    (fun i => decide (vertical.getD i 999=i))=true := by decide

#print axioms DirectBFSConjugacyShape.array_sizes
#print axioms DirectBFSConjugacyShape.distinguished_rows
#print axioms DirectBFSConjugacyShape.fixed_horizontal
#print axioms DirectBFSConjugacyShape.fixed_vertical
end DirectBFSConjugacyShape
