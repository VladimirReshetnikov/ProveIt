import DiophantineConsistency.NativeQuadraticPositions

open DiophantineConsistency
open SidonPositions SelectiveQuadraticCoding NativeQuadraticParent NativeQuadraticPositions

example : target 0 = 349 := rfl
example : target 21 = 7678 := rfl

-- The actual final constant guard attains the kernel's exponent bound.
example : target 21 - pairWeight SelectiveCertificate52.weights
    (⟨(0, 0), by decide⟩ : PairIndex 31) = 7516 := by decide
example : (⟨(0, 0), by decide⟩ : PairIndex 31) ∈ rowSupport 21 := by
  exact Finset.mem_image.mpr ⟨0, by decide, rfl⟩

example (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ) :
    (product ports x).coeff 7865 = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (product_degree_lt ports x)

#print axioms encoding_span
#print axioms product_degree_lt
#print axioms kernel_exponents_injective
#print axioms kernel_coefficient_bound
#print axioms tau_selected_rows_iff
#print axioms product_half_base_bound
#print axioms doubled_full_polynomial
#print axioms tau_selected_rows_iff_of_scale

#print axioms tau_source_rows_iff_of_scale

#print axioms kernel_degree_le
#print axioms kernel_coefficient_at
#print axioms kernel_top_coefficient
#print axioms kernel_natDegree
