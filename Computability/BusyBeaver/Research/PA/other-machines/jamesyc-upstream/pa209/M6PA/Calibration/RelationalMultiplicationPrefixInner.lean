module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationZero
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] mulPrefix addPrefix addResult
set_option maxHeartbeats 600000

/-- Introduce only the actual graph witness; the raw zero remains a parameter. -/
def mulPrefixInnerIntro {Γ : List Form} (a b z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar a) (.fvar b) (.fvar z) (.fvar g))) :
    ND.Proof Γ (∃¹ (Ordinal.zero (.fvar z) ⋏
      mulPrefix (.fvar a) (.fvar b) (.fvar z) (.bvar 0))) := by
  apply exsIntro _ (.fvar g)
  convert andIntro hz hp using 1 <;> mulSyntax

#print axioms mulPrefixInnerIntro
end M6.PA.RelationalSource.PairGraph
