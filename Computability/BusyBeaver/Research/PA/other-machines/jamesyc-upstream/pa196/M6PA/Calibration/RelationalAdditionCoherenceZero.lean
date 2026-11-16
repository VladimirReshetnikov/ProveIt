module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceRules
public import M6PA.Calibration.RelationalAdditionZeroCoherence
@[expose] public section

/-! Universal zero case for the arbitrary-other-input addition coherence predicate. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def addCoherenceZeroPoint {Γ : List Form} (E : FormulaEquality Γ)
    (x y b c r s : Nat) (hz : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (addCoherencePoint (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) := by
  apply impIntro
  let p : Form := addCoherencePremise (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)
  have h : ND.Proof (p::Γ) p := assumption (by simp)
  have h1 := andRight (andRight (andRight h))
  exact additionZeroCoherence (E.weaken (fun q hq => List.mem_cons_of_mem p hq)) x y b c r s
    (up hz p) (andLeft h1) (andLeft (andRight h1))
    (andLeft (andRight (andRight h1))) (andRight (andRight (andRight h1)))

def addCoherenceZero {Γ : List Form} (E : FormulaEquality Γ) (x : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (addCoherence (.fvar x)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  have h0 := Ordinal.zeroShift x hz
  have h1 := Ordinal.zeroShift (x+1) h0
  have h2 := Ordinal.zeroShift (x+1+1) h1
  have h3 := Ordinal.zeroShift (x+1+1+1) h2
  have h4 := Ordinal.zeroShift (x+1+1+1+1) h3
  have out := addCoherenceZeroPoint E.shifted.shifted.shifted.shifted.shifted
    (x+1+1+1+1+1) 4 3 2 1 0 h4
  convert out using 1 <;> addCoherenceSyntax

#print axioms addCoherenceZeroPoint
#print axioms addCoherenceZero
end M6.PA.RelationalSource.PairGraph
