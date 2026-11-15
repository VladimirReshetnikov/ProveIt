import PA194CompositionClosedAt
set_option maxHeartbeats 8000000
namespace PA194CompositionContext
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194CompositionClosedTemplate

def compositionStatement (a b c : Nat) : Form :=
  (Ordinal.domain (.fvar a) ⋏ (orderIso (.fvar a) (.fvar b) ⋏ orderIso (.fvar b) (.fvar c))) 🡒
    orderIso (.fvar a) (.fvar c)

def compositionAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,closedCompositionSeparation]

def compositionProof (a b c : Nat) : ND.Proof compositionAxioms (compositionStatement a b c) := by
  apply impIntro
  let d : Form := Ordinal.domain (.fvar a) ⋏ (orderIso (.fvar a) (.fvar b) ⋏ orderIso (.fvar b) (.fvar c))
  let C := d :: compositionAxioms
  have hd : ND.Proof C d := assumption (by simp [C])
  have E : FormulaEquality C :=
    ⟨⟨assumption (by simp [C,compositionAxioms]),assumption (by simp [C,compositionAxioms]),
      assumption (by simp [C,compositionAxioms])⟩,assumption (by simp [C,compositionAxioms])⟩
  have hs : ND.Proof C closedCompositionSeparation := assumption (by simp [C,compositionAxioms])
  exact compositionIsoTransitivity E a b c (assumption (by simp [C,compositionAxioms]))
    (assumption (by simp [C,compositionAxioms])) (assumption (by simp [C,compositionAxioms]))
    (compositionClosedAt a hs) (andLeft (andRight hd)) (andRight (andRight hd)) (andLeft hd)

def compositionDerivation (a b c : Nat) : LO.FirstOrder.Derivation
    (compositionAxioms.map Semiformula.neg ++ [compositionStatement a b c]) :=
  (compositionProof a b c).contra (by simp)
#print axioms compositionProof
#print axioms compositionDerivation
end PA194CompositionContext
