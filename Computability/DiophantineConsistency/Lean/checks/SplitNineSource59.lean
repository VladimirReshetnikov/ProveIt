import DiophantineConsistency.SplitNineSource59

open DiophantineConsistency SplitNineSource59

-- The positive all-one source tuple is impossible even at arbitrary ports.
example (ports : Fin 4 → ℤ) :
    ¬∀ j, SplitCertificate59.sourceRows ports (fun _ => 1) j = 0 := by
  intro h
  have hh := h 9
  rw [SplitKernels59.source_one_not_zero] at hh
  norm_num at hh

-- The source geometry really attains the top weight used in cofinal coding.
example (ports : Fin 4 → ℤ) : (parameters ports).w 20 = 116 := rfl

#print axioms valid_of_kernelBounds
#print axioms valid_of_portBounds
#print axioms coefficients_zero_iff_source
#print axioms exists_natural_zero_iff_source
#print axioms exists_natural_zero_iff_source_portBounds
#print axioms exists_natural_zero_iff_source_compact54
#print axioms no_natural_zero_iff_source
