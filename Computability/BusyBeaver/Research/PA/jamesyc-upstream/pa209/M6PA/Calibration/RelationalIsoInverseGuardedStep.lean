module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseExistsStep
public import M6PA.Calibration.RelationalOrderIsoRules
public import M6PA.Calibration.RelationalOrdinalInductionUniform
@[expose] public section

/-! The successor step retains the subset bound: only prefix coordinates
inside the original graph's domain need values. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inversePredecessorSubset {Γ : List Form} (n s a : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (ha : ND.Proof Γ (Ordinal.subset (.fvar s) (.fvar a))) :
    ND.Proof Γ (Ordinal.subset (.fvar n) (.fvar a)) := by
  apply allIntro
  let d : Form := mem (.fvar (n+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have hh := Ordinal.successorOld (n+1) (s+1) 0 (up (Ordinal.successorShift n s hs) d) hd
  have out := Ordinal.subsetAt (s+1) (a+1) 0 (up (Ordinal.subsetShift s a ha) d) hh
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def inverseGuardedStep {Γ : List Form} (E : FormulaEquality Γ) (g a n s : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (ht : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hi : ND.Proof Γ (Ordinal.subset (.fvar n) (.fvar a) 🡒 inversePrefixExists (.fvar g) (.fvar n))) :
    ND.Proof Γ (Ordinal.subset (.fvar s) (.fvar a) 🡒 inversePrefixExists (.fvar g) (.fvar s)) := by
  apply impIntro
  let d : Form := Ordinal.subset (.fvar s) (.fvar a)
  have hd : ND.Proof (d :: Γ) d := assumption (by simp)
  have ee := E.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hns := mp (ND.orRight (Ordinal.eqRefl ee.core n)) (andRight (Ordinal.successorAt n s n (up hs d)))
  have hna := Ordinal.subsetAt s a n hd hns
  have hv := orderLeftAt g a n (up ht d) hna
  have hp := mp (inversePredecessorSubset n s a (up hs d) hd) (up hi d)
  exact inverseExistsStep ee g n s (up hempty d) (up hadj d) (up hs d) hv hp

#print axioms inversePredecessorSubset
#print axioms inverseGuardedStep
end M6.PA.RelationalSource.PairGraph
