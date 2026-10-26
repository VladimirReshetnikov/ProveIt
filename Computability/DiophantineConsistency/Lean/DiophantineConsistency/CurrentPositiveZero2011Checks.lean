import DiophantineConsistency.CurrentPositiveZero2011

namespace DiophantineConsistency.CurrentPositiveZero2011Checks

open CurrentPositiveZero2011 CurrentPolynomialWindow2011 CurrentCarrierArithmetic2011
set_option Elab.async false

-- Closed implication: no tiling, mask, rank, Pell seed or source zero is supplied.
example (hc : ¬ DiophantineConsistency.ConZFC) : PositiveZero polynomial :=
  not_conZFC_positive_zero hc

-- The exact fixed polynomial and exact existing syntactic consistency predicate.
example : (¬ PositiveZero polynomial) ↔ DiophantineConsistency.ConZFC :=
  no_positive_zero_iff_conZFC

-- Pointwise reading of lack of solutions, retaining strictly positive integers.
example : (∀ v : Fin 14 → ℤ, (∀ j,0<v j) → MvPolynomial.eval v polynomial ≠ 0) ↔
    DiophantineConsistency.ConZFC := by
  constructor
  · intro h
    apply no_positive_zero_iff_conZFC.mp
    rintro ⟨v,hv,hzero⟩
    exact h v hv hzero
  · intro hc
    exact CurrentSoundness2011.conZFC_no_polynomial_zero hc

-- All three accepted operation/degree frontiers have the same equivalence.
example :
    ((¬ PositiveZero (polynomial69 (CurrentKernel2011.K : ℤ))) ↔ DiophantineConsistency.ConZFC) ∧
    ((¬ PositiveZero (polynomial70 (CurrentKernel2011.K : ℤ))) ↔ DiophantineConsistency.ConZFC) ∧
    ((¬ PositiveZero (polynomial71 (CurrentKernel2011.K : ℤ))) ↔ DiophantineConsistency.ConZFC) :=
  no_thirteen_positive_zero_iff_conZFC

-- One actual positive assignment serves all three forms, not unrelated points.
example (hc : ¬ DiophantineConsistency.ConZFC) :
    ∃ u : Fin 13 → ℤ, (∀ j,0<u j) ∧
      MvPolynomial.eval u (polynomial69 (CurrentKernel2011.K : ℤ))=0 ∧
      MvPolynomial.eval u (polynomial70 (CurrentKernel2011.K : ℤ))=0 ∧
      MvPolynomial.eval u (polynomial71 (CurrentKernel2011.K : ℤ))=0 :=
  not_conZFC_simultaneous_thirteen_zero hc

#print axioms packingData
#print axioms not_conZFC_positive_zero
#print axioms positive_zero_iff_not_conZFC
#print axioms no_positive_zero_iff_conZFC
#print axioms no_thirteen_positive_zero_iff_conZFC
#print axioms not_conZFC_simultaneous_thirteen_zero

end DiophantineConsistency.CurrentPositiveZero2011Checks
