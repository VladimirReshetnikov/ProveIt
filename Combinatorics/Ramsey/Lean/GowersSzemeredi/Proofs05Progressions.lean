import GowersSzemeredi.Proofs05IntegerRefinement

/-!
# Genuine integer-representative refinements in Gowers's Section 5

The numbered Lemmas 5.12 and 5.13 require ordinary progressions of integer
representatives, rather than merely injective modular parameterizations.
The explicit Dirichlet and quotient-run construction proves their printed
cell budgets over every nonzero modulus.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Lemma 5.12 with the genuine integer-representative conclusion. -/
theorem lemma_5_12_holds : lemma_5_12 :=
  lemma_5_12_integer_representatives_holds

/-- Lemma 5.13 with the genuine integer-representative conclusion. -/
theorem lemma_5_13_holds : lemma_5_13 :=
  lemma_5_13_integer_representatives_holds

end LeanProofs.GowersSzemeredi
