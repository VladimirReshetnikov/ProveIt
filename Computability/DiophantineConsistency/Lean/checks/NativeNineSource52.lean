import DiophantineConsistency.NativeNineSource52

open DiophantineConsistency.NativeNineSource52

-- The source and the six positive registers are decoded from exactly nine
-- natural coordinates; phi, j and n retain their zero boundary.
example : (varsOfTuple (fun _ => 0)).h = 1 ∧
    (varsOfTuple (fun _ => 0)).phi = 0 ∧ (varsOfTuple (fun _ => 0)).j = 0 := by decide

#print axioms exists_naturalValue_zero_iff
#print axioms ratio_size_bounds
#print axioms source_of_zero
#print axioms zero_of_source
#print axioms hasZero_iff_source
#print axioms natural_zero_iff_source
#print axioms natural_zero_iff_source_published
