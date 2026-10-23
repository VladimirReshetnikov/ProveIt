import DiophantineConsistency.SplitNinePolynomial59

open DiophantineConsistency.SplitNinePolynomial59
open DiophantineConsistency.SplitKernelData59

set_option maxRecDepth 10000

example : sourceBase (3:ℤ) 2=49152 := by decide

/-- Zero base checks the constant position and excludes every positive position. -/
example : kernel0 (fun i => (i.val:ℤ)) 0=0 := by
  have hp : ∀ i, positions0 i≠0 := by decide
  unfold kernel0
  apply Finset.sum_eq_zero
  intro i _
  rw [zero_pow (hp i),mul_zero]

example : kernel1 (fun i => (i.val:ℤ)) 0=0 := by
  have hp : ∀ i, positions1 i≠0 := by decide
  unfold kernel1
  apply Finset.sum_eq_zero
  intro i _
  rw [zero_pow (hp i),mul_zero]

example : kernel2 (fun i => (i.val+2:ℤ)) 0=(-2) := by
  have hp : ∀ i : Fin 42, positions2 i.succ≠0 := by decide
  have hz : (∑ i : Fin 42, coefficients2 (fun j => (j.val+2:ℤ)) i.succ*
      (0:ℤ)^positions2 i.succ)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [zero_pow (hp i),mul_zero]
  rw [kernel2,Fin.sum_univ_succ,hz]
  rfl

example : successorShift (fun _ => (0:ℤ)) 7=0 := rfl
example : successorShift (fun _ => (0:ℤ)) 8=1 := rfl

private def boundary : DiophantineConsistency.FreeCarrierRatio.FreeVars := ⟨1,1,1,1,1,0⟩

example : witnessVector 2 3 boundary 4=![2,3,1,1,1,1,1,0,4] := rfl

example : ratioValue (8:ℤ) 8 1 0 100 1 1 1 1 1 0 1=
    boundary.finalValue 8 8 1 0 3200 100 1 :=
  ratioValue_nat boundary 8 8 1 0 3200 100 1

#print axioms kernel0
#print axioms map_coefficients0
#print axioms map_coefficients1
#print axioms map_coefficients2
#print axioms map_value
#print axioms ratioValue_nat
#print axioms sourceRank_nat
#print axioms value_eq_naturalValue
#print axioms polynomial
#print axioms eval_polynomial
#print axioms eval_polynomial_nat
#print axioms exists_natural_zero_iff_source
#print axioms exists_natural_zero_iff_source_compact54
#print axioms no_natural_zero_iff_source
