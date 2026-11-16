module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationPrefixInner
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] mulPrefix addPrefix addResult
set_option maxHeartbeats 600000

def mulPrefixExistsIntro {Γ : List Form} (a b z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar a) (.fvar b) (.fvar z) (.fvar g))) :
    ND.Proof Γ (mulPrefixExists (.fvar a) (.fvar b)) := by
  apply exsIntro _ (.fvar z)
  convert mulPrefixInnerIntro a b z g hz hp using 1 <;> mulSyntax

#print axioms mulPrefixExistsIntro
end M6.PA.RelationalSource.PairGraph
