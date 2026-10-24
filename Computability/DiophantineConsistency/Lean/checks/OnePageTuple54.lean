import DiophantineConsistency.OnePageTuple54

open DiophantineConsistency

namespace OnePageTuple54Checks

set_option maxRecDepth 10000

example (i j : Fin 457) :
    OnePageTuple54.integerDelta i j = if i=j then 1 else 0 :=
  OnePageTuple54.integerDelta_eq i j

example (i : Fin 457) : OnePageTuple54.integerCoefficient i =
    (NativeLocalCoefficients54.selectorCoefficient
      (OnePageModes54.unsortedMode i).2 (OnePageModes54.unsortedMode i).1 : ℤ) :=
  OnePageTuple54.integerCoefficient_eq i

example (ρ : ℕ) : OnePageTuple54.stencilWord ρ = NativeStencil54.rawWord ρ :=
  OnePageTuple54.stencilWord_eq_rawWord ρ

#print axioms OnePageTuple54.integerDelta_eq
#print axioms OnePageTuple54.integerDelta_cast
#print axioms OnePageTuple54.integerCoefficient_eq
#print axioms OnePageTuple54.coefficient_eq
#print axioms OnePageTuple54.entries_split
#print axioms OnePageTuple54.selectorWord_eq
#print axioms OnePageTuple54.stencilWord_eq_rawWord

end OnePageTuple54Checks
