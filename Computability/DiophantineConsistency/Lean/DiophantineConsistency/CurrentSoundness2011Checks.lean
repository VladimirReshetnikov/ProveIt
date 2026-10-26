import DiophantineConsistency.CurrentSoundness2011

/-! Actual fixed ports, positive independent coordinates, the existing
syntactic consistency predicate, and all three thirteen-variable forms. -/

namespace DiophantineConsistency.CurrentSoundness2011Checks

open SetTheory SetTheory.BusyBeaver.ZFC LeanProofs.BoundedZFCConsistency
open CurrentPolynomialWindow2011 CurrentCarrierArithmetic2011 CurrentSoundness2011

set_option Elab.async false
set_option maxRecDepth 10000

example (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    KDenseBridge.BlankHalts DecimalMachine215.machine :=
  polynomial_zero_blank_halts v hv hz

example (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) : BProv ZFCax_s [] Form.fBot :=
  polynomial_zero_zfc_refutation v hv hz

-- The conclusion specializes to the maintained evaluator with its entire
-- actual port tuple, not an arbitrary K or an assumed native calibration.
example (hc : ConZFC) (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j) :
    Carrier65.value CurrentWindowCarry2011.ports v ≠ 0 := by
  simpa only [polynomial,Carrier65.eval_polynomial] using conZFC_no_polynomial_zero hc v hv

example (hc : ConZFC) : ¬ PositiveZero polynomial := conZFC_no_positive_zero hc

example (hc : ConZFC) :
    ¬ PositiveZero (polynomial69 (CurrentKernel2011.K : ℤ)) :=
  (conZFC_no_thirteen_positive_zero hc).1

example (hc : ConZFC) :
    ¬ PositiveZero (polynomial70 (CurrentKernel2011.K : ℤ)) :=
  (conZFC_no_thirteen_positive_zero hc).2.1

example (hc : ConZFC) :
    ¬ PositiveZero (polynomial71 (CurrentKernel2011.K : ℤ)) :=
  (conZFC_no_thirteen_positive_zero hc).2.2

-- Restoration plus the actual fourteen-variable endpoint gives a finite
-- refutation from a zero of any accepted thirteen-variable form.
theorem thirteen_zero_refutation (u : Fin 13 → ℤ) (hu : ∀ j, 0 < u j)
    (hz : MvPolynomial.eval u (polynomial69 (CurrentKernel2011.K : ℤ)) = 0 ∨
      MvPolynomial.eval u (polynomial70 (CurrentKernel2011.K : ℤ)) = 0 ∨
      MvPolynomial.eval u (polynomial71 (CurrentKernel2011.K : ℤ)) = 0) :
    BProv ZFCax_s [] Form.fBot := by
  obtain ⟨hv,hvzero⟩ := restores (CurrentKernel2011.K : ℤ) u hu hz
  exact polynomial_zero_zfc_refutation _ hv hvzero

#print axioms polynomial_zero_blank_halts
#print axioms polynomial_zero_zfc_refutation
#print axioms conZFC_no_polynomial_zero
#print axioms conZFC_no_positive_zero
#print axioms conZFC_no_thirteen_positive_zero
#print axioms thirteen_zero_refutation

end DiophantineConsistency.CurrentSoundness2011Checks
