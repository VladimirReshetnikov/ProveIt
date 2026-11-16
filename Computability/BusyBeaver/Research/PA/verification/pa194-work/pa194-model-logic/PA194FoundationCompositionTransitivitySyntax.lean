import PA194FoundationCompositionExistsSyntax
set_option maxHeartbeats 8000000

namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Formula)

theorem compositionBijectionFreeEq (a b : Nat) :
    (orderBijection (.bvar 0) (.fvar a) (.fvar b) : Formula 1).free =
      orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1)) := by
  compositionSyntax

#print axioms compositionBijectionFreeEq
end M6.PA.RelationalSource.PairGraph
