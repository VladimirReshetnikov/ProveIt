module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionBijection
@[expose] public section

/-! Separate syntax identities keep existential composition assembly small. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

theorem compositionBijectionShiftEq (g a b : Nat) :
    (orderBijection (.fvar g) (.fvar a) (.fvar b) : Form).shift =
      orderBijection (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1)) := by
  compositionSyntax

theorem compositionIsoShiftEq (a c : Nat) :
    (orderIso (.fvar a) (.fvar c) : Form).shift =
      orderIso (.fvar (a+1)) (.fvar (c+1)) := by
  compositionSyntax

theorem compositionPrefixFreeEq (g h a : Nat) :
    (compositionPrefix (.fvar g) (.fvar h) (.fvar a) (.bvar 0) : Formula 1).free =
      compositionPrefix (.fvar (g+1)) (.fvar (h+1)) (.fvar (a+1)) (.fvar 0) := by
  compositionSyntax

def compositionIsoIntro {Γ : List Form} (g a c : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar c))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar c)) := by
  apply exsIntro _ (.fvar g)
  convert hg using 1 <;> compositionSyntax

#print axioms compositionIsoIntro
#print axioms compositionBijectionShiftEq
#print axioms compositionIsoShiftEq
#print axioms compositionPrefixFreeEq
end M6.PA.RelationalSource.PairGraph
