import SpectralBlueprint

open IPRAStableObservables.Spectral

#check DiagonalCertificate
#check PositiveCertificate
#check RootCertificate
#check ProjectorCertificate
#check PivotImprovementTarget
#check DiagonalizationFuelTarget
#check SpectralComparisonTarget
#check SquareRootMixedBasisTarget
#check ThresholdProjectorComparisonTarget
#check PositiveGapToMarginTarget
#check UnprovedMatrixObligations

-- These print dependencies of definitions, NOT proofs of the target Props.
#print axioms diagonalize
#print axioms SpectralComparisonTarget
#print axioms SquareRootMixedBasisTarget

-- Finite execution example only; the universal correctness targets above
-- remain unproved. Its output can be compared to the Python reference.
def exampleMatrix : Mat 2 := fun i j => if i = j then 2 else 1
#eval let w := diagonalize exampleMatrix (1 / 2)
  (w.values 0, w.values 1,
   offdiagSq (conjugate exampleMatrix w.basis))
