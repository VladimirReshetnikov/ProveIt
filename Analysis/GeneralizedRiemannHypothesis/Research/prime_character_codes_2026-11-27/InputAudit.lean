/-!
  Input interface ONLY, for the pinned upstream grh/ package.
  Copy into its root and run `lake env lean InputAudit.lean` after building.
  This file does not formalize the new sampling or rigidity theorems.
  It has not been run in the environment that produced this research note.
-/
import Main

namespace PrimeCharacterCodesInput

theorem rh : RiemannHypothesis := riemannHypothesis

theorem dirichlet_grh : DirichletLZerosOnLine := LFunction_eq_zero_re

theorem right_half_plane : DirichletLNonvanishingRightOfHalf :=
  LFunction_ne_zero_of_half_lt_re

#print axioms rh
#print axioms dirichlet_grh
#print axioms right_half_plane

end PrimeCharacterCodesInput
