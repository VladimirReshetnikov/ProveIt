module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionExistsSyntax
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

theorem compositionBijectionFreeEq (a b : Nat) :
    (orderBijection (.bvar 0) (.fvar a) (.fvar b) : Formula 1).free =
      orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1)) := by
  compositionSyntax

#print axioms compositionBijectionFreeEq
end M6.PA.RelationalSource.PairGraph
