module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoRelationRules
public import M6PA.Calibration.RelationalGraphFunctionalExtension
@[expose] public section

/-! Edge typing after exact extension by the two predecessor endpoints. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorTypedAt {Γ : List Form} (E : FormulaEquality Γ)
    (g h a b c d x y : Nat)
    (hg : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar c) (.fvar x) ⋏ mem (.fvar d) (.fvar y)) := by
  apply orElim (mp he (andLeft (exactAt g h a b x y hx)))
  · let premise : Form := edge (.fvar g) (.fvar x) (.fvar y)
    have old := orderTypedAt g a b x y (up hg premise) (assumption (by simp [premise]))
    exact andIntro (Ordinal.successorOld a c x (up hs premise) (andLeft old))
      (Ordinal.successorOld b d y (up ht premise) (andRight old))
  · let premise : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar y) (.fvar b)
    have hd : ND.Proof (premise::Γ) premise := assumption (by simp)
    let EE := E.weaken (fun q hq => List.mem_cons_of_mem premise hq)
    have hm := mp (ND.orRight (EE.reflexive (.fvar a)))
      (andRight (Ordinal.successorAt a c a (up hs premise)))
    have hn := mp (ND.orRight (EE.reflexive (.fvar b)))
      (andRight (Ordinal.successorAt b d b (up ht premise)))
    exact andIntro (Ordinal.memElement EE.core c a x (EE.symmetryOf (andLeft hd)) hm)
      (Ordinal.memElement EE.core d b y (EE.symmetryOf (andRight hd)) hn)

def successorGraphTyped {Γ : List Form} (E : FormulaEquality Γ)
    (g h a b c d : Nat)
    (hg : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphTyped (.fvar h) (.fvar c) (.fvar d)) := by
  apply allIntro
  apply allIntro
  let premise : Form := edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)
  let EE := E.shifted.shifted.weaken (fun q hq => List.mem_cons_of_mem premise hq)
  have out := successorTypedAt EE (g+1+1) (h+1+1) (a+1+1) (b+1+1) (c+1+1) (d+1+1) 1 0
    (up (orderTypedShift (g+1) (a+1) (b+1) (orderTypedShift g a b hg)) premise)
    (up (Ordinal.successorShift (a+1) (c+1) (Ordinal.successorShift a c hs)) premise)
    (up (Ordinal.successorShift (b+1) (d+1) (Ordinal.successorShift b d ht)) premise)
    (up (exactShift (g+1) (h+1) (a+1) (b+1) (exactShift g h a b hx)) premise)
    (assumption (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

#print axioms successorTypedAt
#print axioms successorGraphTyped
end M6.PA.RelationalSource.PairGraph
