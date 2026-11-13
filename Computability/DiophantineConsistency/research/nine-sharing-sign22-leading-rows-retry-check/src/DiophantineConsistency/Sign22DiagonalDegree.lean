import DiophantineConsistency.Sign22LeadingRows

/-! SOURCE-ONLY: diagonal specialization does not increase total degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22LeadingRows
open MvPolynomial

def diagonalVars (i : Fin 22) : MvPolynomial (Fin 1) ℤ :=
  if i = 10 ∨ i = 11 ∨ i = 14 ∨ i = 15 then X 0 else 0

noncomputable def diagonal (p : MvPolynomial (Fin 22) ℤ) : MvPolynomial (Fin 1) ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C diagonalVars p

theorem diagonal_totalDegree_le (p : MvPolynomial (Fin 22) ℤ) :
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
end DiophantineConsistency.Sign22LeadingRows
#print axioms DiophantineConsistency.Sign22LeadingRows.diagonal_totalDegree_le
