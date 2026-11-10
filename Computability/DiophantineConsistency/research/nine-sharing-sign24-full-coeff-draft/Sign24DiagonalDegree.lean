import DiophantineConsistency.Sign24LeadingN0

/-! SOURCE-ONLY: diagonal specialization does not increase total degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24LeadingN0
open MvPolynomial

def diagonalVars (i : Fin 24) : MvPolynomial (Fin 1) ℤ :=
  if i = 15 ∨ i = 16 then X 0 else 0

noncomputable def diagonal (p : MvPolynomial (Fin 24) ℤ) : MvPolynomial (Fin 1) ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C diagonalVars p

theorem diagonal_totalDegree_le (p : MvPolynomial (Fin 24) ℤ) :
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
end DiophantineConsistency.Sign24LeadingN0
#print axioms DiophantineConsistency.Sign24LeadingN0.diagonal_totalDegree_le
