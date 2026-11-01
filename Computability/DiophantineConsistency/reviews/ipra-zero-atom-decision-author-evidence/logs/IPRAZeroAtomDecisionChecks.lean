import DiophantineConsistency.IPRAZeroAtomDecision
set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRAZeroAtomDecision
example (hz : nativeTheory ⊢! zeroDecSentence) (a b : Term language ℕ) :
    extended nativeTheory ⊢!
      (Semiformula.nrel Language.ORing.Rel.eq ![a,zero] ⋎
        Semiformula.rel Language.ORing.Rel.eq ![b,zero])ᴺ 🡒
      native (Semiformula.nrel Language.ORing.Rel.eq ![a,zero] ⋎
        Semiformula.rel Language.ORing.Rel.eq ![b,zero]) :=
  zeroOpenBackward hz _ (.disj (.negative a) (.positive b))
#print axioms decideZero
#print axioms zeroOpenBackward
