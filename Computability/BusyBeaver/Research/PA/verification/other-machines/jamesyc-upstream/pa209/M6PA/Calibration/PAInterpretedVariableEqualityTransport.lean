module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualitySymmetry
public import M6PA.Calibration.RelationalOrderIsoTransport
@[expose] public section

/-! Ordinary equality transports arbitrary ground relational endpoints. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] PairGraph.orderIso
set_option maxHeartbeats 800000

def interpretedIsoTransport {Γ : List Form} (E : FormulaEquality Γ) (a b c d : Term 0)
    (hab : ND.Proof Γ (ND.eq a b)) (hcd : ND.Proof Γ (ND.eq c d))
    (hi : ND.Proof Γ (PairGraph.orderIso a c)) : ND.Proof Γ (PairGraph.orderIso b d) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a]) (PairGraph.orderIso (.bvar 0) (Rew.bShift c))) := by
    convert hi using 1 <;> interpretedWitnessSyntax
  have mid := E.substituteOne (PairGraph.orderIso (.bvar 0) (Rew.bShift c)) a b hab hp
  have hm : ND.Proof Γ (PairGraph.orderIso b c) := by
    convert mid using 1 <;> interpretedWitnessSyntax
  have hq : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![c]) (PairGraph.orderIso (Rew.bShift b) (.bvar 0))) := by
    convert hm using 1 <;> interpretedWitnessSyntax
  have out := E.substituteOne (PairGraph.orderIso (Rew.bShift b) (.bvar 0)) c d hcd hq
  convert out using 1 <;> interpretedWitnessSyntax

def boundVariableEqualityIntro {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hi : ND.Proof Γ (Ordinal.domain (b i))) (hj : ND.Proof Γ (Ordinal.domain (b j)))
    (hiso : ND.Proof Γ (PairGraph.orderIso (b i) (b j))) :
    ND.Proof Γ (equal (.bvar i) (.bvar j) b f) := by
  apply equalityValueIntro _ _ b f (b i) (b j)
  · rw [value_bvar]; exact andIntro hi (E.reflexive (b i))
  · rw [value_bvar]; exact andIntro hj (E.reflexive (b j))
  · exact hiso

#print axioms interpretedIsoTransport
#print axioms boundVariableEqualityIntro
end M6.PA.ForwardRelational
