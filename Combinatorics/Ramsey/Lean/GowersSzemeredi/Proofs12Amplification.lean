import GowersSzemeredi.Proofs12Parallelograms
import GowersSzemeredi.Proofs12HigherArrangements

/-!
# Fourier-rich second differences yield many higher arrangements

This module proves Lemma 12.4 by composing Lemmas 12.2 and 12.3.  The
seventh power changes the exponents `16` and `48` to `112` and `336`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod

namespace LeanProofs.GowersSzemeredi

/-- **Lemma 12.4.** Large Fourier coefficients of second differences yield
many respected `8`-arrangements. -/
theorem lemma_12_4_holds : lemma_12_4 := by
  intro N _ beta gamma f B phi hbeta hgamma hf hcard hlarge
  have hpairs := lemma_12_2_holds N beta gamma f B phi hbeta hgamma hf
    hcard hlarge
  have harrangements := lemma_12_3_holds N
    (beta ^ 16 * gamma ^ 48) B phi hpairs
  calc
    beta ^ 112 * gamma ^ 336 * (N : Real) ^ 32 =
        (beta ^ 16 * gamma ^ 48) ^ 7 * (N : Real) ^ 32 := by ring
    _ ≤ (respectedArrangementCount 8 B phi : Real) := harrangements

end LeanProofs.GowersSzemeredi
