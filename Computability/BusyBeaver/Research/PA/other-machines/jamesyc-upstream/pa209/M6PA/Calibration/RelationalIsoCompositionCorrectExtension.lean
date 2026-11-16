module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionRules
@[expose] public section

/-! Composition-edge correctness of the actual adjoined graph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorCompositionCorrectAt {Γ : List Form} (E : FormulaEquality Γ)
    (g h n s k y z p l x w : Nat)
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (ha : ND.Proof Γ (adjunction (.fvar k) (.fvar p) (.fvar l)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z)))
    (he : ND.Proof Γ (edge (.fvar l) (.fvar x) (.fvar w))) :
    ND.Proof Γ (mem (.fvar s) (.fvar x) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar w)) := by
  apply orElim (classifyEdge E.core E.transitive k p l n z x w ha hp he)
  · let d : Form := edge (.fvar k) (.fvar x) (.fvar w)
    have hh := compositionCorrectAt g h n k x w (up hc d) (assumption (by simp [d]))
    exact andIntro (Ordinal.successorOld n s x (up hs d) (andLeft hh)) (andRight hh)
  · let d : Form := eq (.fvar x) (.fvar n) ⋏ eq (.fvar w) (.fvar z)
    have hd : ND.Proof (d :: Γ) d := assumption (by simp)
    have ee := E.weaken (fun q hq => List.mem_cons_of_mem d hq)
    have hn := mp (ND.orRight (Ordinal.eqRefl ee.core n)) (andRight (Ordinal.successorAt n s n (up hs d)))
    have hnx := ee.symmetryOf (andLeft hd)
    have hzw := ee.symmetryOf (andRight hd)
    have hnz := compositionEdgeIntro g h n y z (up hg d) (up hh d)
    exact andIntro (Ordinal.memElement ee.core s n x hnx hn)
      (compositionEdgeOutputTransport ee g h x z w hzw (compositionEdgeInputTransport ee g h n z x hnx hnz))

def successorCompositionCorrect {Γ : List Form} (E : FormulaEquality Γ)
    (g h n s k y z p l : Nat)
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (ha : ND.Proof Γ (adjunction (.fvar k) (.fvar p) (.fvar l)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z))) :
    ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar s) (.fvar l)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (l+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have gg : ND.Proof (shifted (shifted Γ)) (edge (.fvar (g+1+1)) (.fvar (n+1+1)) (.fvar (y+1+1))) := by
    convert shiftProof (shiftProof hg) using 1 <;> compositionSyntax
  have hh' : ND.Proof (shifted (shifted Γ)) (edge (.fvar (h+1+1)) (.fvar (y+1+1)) (.fvar (z+1+1))) := by
    convert shiftProof (shiftProof hh) using 1 <;> compositionSyntax
  have out := successorCompositionCorrectAt (E.shifted.shifted.weaken (fun q hq => List.mem_cons_of_mem d hq))
    (g+1+1) (h+1+1) (n+1+1) (s+1+1) (k+1+1) (y+1+1) (z+1+1) (p+1+1) (l+1+1) 1 0
    (up (compositionCorrectShift (g+1) (h+1) (n+1) (k+1) (compositionCorrectShift g h n k hc)) d)
    (up (Ordinal.successorShift (n+1) (s+1) (Ordinal.successorShift n s hs)) d) (up gg d) (up hh' d)
    (up (adjunctionShift (k+1) (p+1) (l+1) (adjunctionShift k p l ha)) d)
    (up (kuratowskiShift (p+1) (n+1) (z+1) (kuratowskiShift p n z hp)) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

#print axioms successorCompositionCorrectAt
#print axioms successorCompositionCorrect
end M6.PA.RelationalSource.PairGraph
