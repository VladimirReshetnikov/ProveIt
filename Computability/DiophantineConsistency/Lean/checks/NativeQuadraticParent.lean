import DiophantineConsistency.NativeQuadraticParent

open DiophantineConsistency
open NativeQuadraticParent SelectiveQuadraticCoding

-- The shifted zero tuple violates the original fifth row for every port tuple.
example (ports : Fin 4 → ℤ) : shiftedRows ports (fun _ => 0) 21 = 1 := by
  rfl

example (ports : Fin 4 → ℤ) : ¬ ∀ k, shiftedRows ports (fun _ => 0) k = 0 := by
  intro h
  have hz : shiftedRows ports (fun _ => 0) 21 = 1 := rfl
  have := h 21
  rw [hz] at this
  norm_num at this

-- The interior padding is a genuine constant coordinate of weight81,
-- while the seventh source variable occupies exponent0.
example : padded (fun i : Fin 31 => (i.val : ℤ)) 0 = 1 := by decide
example : padded (fun i : Fin 31 => (i.val : ℤ)) 7 = 6 := by decide
example : SelectiveCertificate52.weights 0 = 81 := rfl
example : SelectiveCertificate52.weights 7 = 0 := rfl

-- The last selected coefficient is the constant guard, not a vacuous source.
example (ports : Fin 4 → ℤ) :
    (encoded SelectiveCertificate52.weights (padded (fun _ => 0)) ^ 2 *
      combined SelectiveCertificate52.weights rowSupport (rowCoefficient ports)
        (fun j => 349 * (j.val + 1))).coeff 7678 = 2 := by
  have h := coeff_source_rows ports (fun _ => (0 : ℤ)) 21
  norm_num [shiftedRows, sourceRows, rowOrder] at h
  exact h

#print axioms rowSupport_subset
#print axioms rowValue_eq_shiftedRows
#print axioms coeff_source_rows
