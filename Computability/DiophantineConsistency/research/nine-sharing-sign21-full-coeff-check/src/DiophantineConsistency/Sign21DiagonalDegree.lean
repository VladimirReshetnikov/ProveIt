import DiophantineConsistency.Sign21LeadingRow

/-! SOURCE-ONLY: diagonal specialization does not increase total degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21LeadingRow
open MvPolynomial

def diagonalVars (i : Fin 21) : MvPolynomial (Fin 1) ℤ :=
  if i = 5 ∨ i = 16 ∨ i = 20 then X 0 else 0

noncomputable def diagonal (p : MvPolynomial (Fin 21) ℤ) : MvPolynomial (Fin 1) ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C diagonalVars p

theorem diagonal_totalDegree_le (p : MvPolynomial (Fin 21) ℤ) :
    (diagonal p).totalDegree ≤ p.totalDegree := by
  classical
  unfold diagonal
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (fun i hi => ?_)) (MvPolynomial.le_totalDegree hd)
  change (diagonalVars i ^ d i).totalDegree ≤ d i
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  unfold diagonalVars
  split_ifs <;> simp
end DiophantineConsistency.Sign21LeadingRow
#print axioms DiophantineConsistency.Sign21LeadingRow.diagonal_totalDegree_le
