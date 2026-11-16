module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRecurrence
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
set_option maxHeartbeats 600000
attribute [local irreducible] addResult addPrefix mulPrefix

def mulPreviousIntro {Γ : List Form} (g base x y w : Nat)
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar w)))
    (hs : ND.Proof Γ (addResult (.fvar w) (.fvar base) (.fvar y))) :
    ND.Proof Γ (mulPrevious (.fvar g) (.fvar base) (.fvar x) (.fvar y)) := by
  apply exsIntro _ (.fvar w)
  convert andIntro he hs using 1 ; mulPreviousSyntax

#print axioms mulPreviousIntro

end M6.PA.RelationalSource.PairGraph
