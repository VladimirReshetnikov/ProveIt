import GowersSzemeredi.Proofs13UniformDensityParameters

/-! This module keeps `section13RecurrenceLengthThreshold`,
`section13InitialRecurrenceThreshold` and `section13DensityRecurrenceThreshold`;
the rest of the development, with its description, is in
`Proofs13UniformDensityRecurrenceSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

def section13RecurrenceLengthThreshold (alpha : Real) (q : Nat) : Real :=
  max (simultaneousPolynomialThreshold 2 q + 1 : Nat)
    (max (positivePowerThreshold 8 1 ((1 : Real) / (2 : Real) ^ (12 * q)))
      (positivePowerThreshold (160 + 2 * alpha ^ 32) (alpha ^ 32)
        ((1 : Real) / (2 : Real) ^ (12 * q))))

def section13InitialRecurrenceThreshold (delta : Real) (q : Nat) : Real :=
  positivePowerThreshold (section13RecurrenceLengthThreshold delta q + 2)
    (section13ThetaOne (section10Lambda (delta ^ 32 / 16)) / (64 * Real.pi))
    (section13ThetaOne (section10Lambda (delta ^ 32 / 16)) ^ 2 / (16 * (q : Real)))

/-- Explicit finite maximum over the permitted spectrum sizes. -/
def section13DensityRecurrenceThreshold (delta : Real) : Nat :=
  max 3 ((Finset.range (Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) + 1)).sup
    (fun q => Nat.ceil (section13InitialRecurrenceThreshold delta q)))

end LeanProofs.GowersSzemeredi
