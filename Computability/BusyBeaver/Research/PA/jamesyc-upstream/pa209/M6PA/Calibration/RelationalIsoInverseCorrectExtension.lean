module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseRules
@[expose] public section

/-! Reversed-edge correctness after one actual graph adjunction. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorInverseCorrectAt {Γ : List Form} (E : FormulaEquality Γ) (g n s h v p j y x : Nat)
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar n) (.fvar h)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (ha : ND.Proof Γ (adjunction (.fvar h) (.fvar p) (.fvar j)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n)))
    (he : ND.Proof Γ (edge (.fvar j) (.fvar y) (.fvar x))) :
    ND.Proof Γ (mem (.fvar s) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.fvar y)) := by
  apply orElim (classifyEdge E.core E.transitive h p j v n y x ha hp he)
  · let d : Form := edge (.fvar h) (.fvar y) (.fvar x)
    have hh := inverseCorrectAt g n h y x (up hc d) (assumption (by simp [d]))
    exact andIntro (Ordinal.successorOld n s x (up hs d) (andLeft hh)) (andRight hh)
  · let d : Form := eq (.fvar y) (.fvar v) ⋏ eq (.fvar x) (.fvar n)
    have hd : ND.Proof (d :: Γ) d := assumption (by simp)
    have ee := E.weaken (fun q hq => List.mem_cons_of_mem d hq)
    have hn := mp (ND.orRight (Ordinal.eqRefl ee.core n)) (andRight (Ordinal.successorAt n s n (up hs d)))
    have hnx := ee.symmetryOf (andRight hd)
    have hvy := ee.symmetryOf (andLeft hd)
    exact andIntro (Ordinal.memElement ee.core s n x hnx hn)
      (inverseEdgeOutputTransport ee g x v y hvy (edgeInputTransport ee g n x v hnx (up hv d)))

def successorInverseCorrect {Γ : List Form} (E : FormulaEquality Γ) (g n s h v p j : Nat)
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar n) (.fvar h)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (ha : ND.Proof Γ (adjunction (.fvar h) (.fvar p) (.fvar j)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n))) :
    ND.Proof Γ (inverseCorrect (.fvar g) (.fvar s) (.fvar j)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (j+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have vv : ND.Proof (shifted (shifted Γ)) (edge (.fvar (g+1+1)) (.fvar (n+1+1)) (.fvar (v+1+1))) := by
    convert shiftProof (shiftProof hv) using 1 <;> inverseSyntax
  have out := successorInverseCorrectAt (E.shifted.shifted.weaken (fun q hq => List.mem_cons_of_mem d hq))
    (g+1+1) (n+1+1) (s+1+1) (h+1+1) (v+1+1) (p+1+1) (j+1+1) 1 0
    (up (inverseCorrectShift (g+1) (n+1) (h+1) (inverseCorrectShift g n h hc)) d)
    (up (Ordinal.successorShift (n+1) (s+1) (Ordinal.successorShift n s hs)) d) (up vv d)
    (up (adjunctionShift (h+1) (p+1) (j+1) (adjunctionShift h p j ha)) d)
    (up (kuratowskiShift (p+1) (v+1) (n+1) (kuratowskiShift p v n hp)) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

#print axioms successorInverseCorrectAt
#print axioms successorInverseCorrect
end M6.PA.RelationalSource.PairGraph
