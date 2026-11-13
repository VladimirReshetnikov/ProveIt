import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: symbolic low-mask radix-digit runs; no file binding. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MCRadixRuns
open CurrentMasks2011

attribute [local irreducible] CurrentMasks2011.radix

def runs : List ℕ :=
  List.replicate 951 (radix - 2) ++ List.replicate 9 (radix - 1) ++
  List.replicate 26 (radix - 2) ++ List.replicate 18 (radix - 1) ++
  List.replicate 1 (radix - 2) ++ List.replicate 1006 (radix - 1)

theorem maskList_runs : LowMaskCoding.maskList radix 2 2011 lowSupport = runs := by
  apply List.ext_getElem
  · simp [LowMaskCoding.maskList, runs]
  · intro i hi hj
    simp only [LowMaskCoding.maskList, List.getElem_map, List.getElem_range,
      LowMaskCoding.maskDigit, CurrentMasks2011.lowSupport_def, Finset.mem_union,
      Finset.mem_range, Finset.mem_Ico, Finset.mem_singleton, runs,
      List.getElem_append, List.getElem_replicate, List.length_append, List.length_replicate]
    split_ifs <;> omega

theorem low_port_runs : lowPort = Nat.ofDigits radix runs := by
  have h := LowMaskCoding.ofDigits_maskList (B := radix) (b := 2) (len := 2011)
    (S := lowSupport) (by decide) (by unfold radix; decide) lowSupport_lt
  rw [maskList_runs] at h
  change LowMaskCoding.mask radix 2 2011 lowSupport = _
  exact h.symm

end DiophantineConsistency.Sign17MCRadixRuns
#print axioms DiophantineConsistency.Sign17MCRadixRuns.maskList_runs
#print axioms DiophantineConsistency.Sign17MCRadixRuns.low_port_runs
