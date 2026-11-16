import PA194FoundationAdditionTrace
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def pointAddRecurrence {Γ : List Form} (E : FormulaEquality Γ) (a b g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g))) :
    ND.Proof Γ (addRecurrence (.fvar g)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have pp := pointShift (a+1+1) (b+1+1) (g+1+1)
    (pointShift (a+1) (b+1) (g+1) (pointShift a b g hp))
  have zz := Ordinal.zeroShift (a+1+1) (Ordinal.zeroShift (a+1) (Ordinal.zeroShift a hz))
  have hi := andLeft (pointAt (a+1+1+1) (b+1+1+1) (g+1+1+1) 2 1 pp)
  have result : ND.Proof (shifted (shifted (shifted Γ)))
      (sourceImply (edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏
        Ordinal.successor (.fvar 0) (.fvar 2))
        (∃⁰ (edge (.fvar (g+1+1+1)) (.fvar 0) (.bvar 0) ⋏
          Ordinal.successor (.bvar 0) (.fvar 1)))) := by
    apply impIntro
    let q : Form := edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hh : ND.Proof (q :: shifted (shifted (shifted Γ))) q := assumption (by simp)
    let EE := E.shifted.shifted.shifted.weaken (fun r hr => List.mem_cons_of_mem q hr)
    have he := andLeft (mp (andLeft hh) (up hi q))
    have hz' := zeroTransport EE (a+1+1+1) 2 (EE.symmetryOf he) (up zz q)
    exact botElim (noSuccessorZero EE 0 2 hz' (andRight hh))
  convert result using 1 <;> (dsimp only [addRecurrence,Ordinal.successor] <;> traceSyntax)

def pointAddPrefix {Γ : List Form} (E : FormulaEquality Γ) (a b g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g))) :
    ND.Proof Γ (addPrefix (.fvar a) (.fvar b) (.fvar a) (.fvar g)) := by
  have he := mp (andIntro (E.reflexive (.fvar a)) (E.reflexive (.fvar b))) (andRight (pointAt a b g a b hp))
  exact andIntro (pointDomain E a b g hz hp)
    (andIntro (pointFunctional E a b g hp)
      (andIntro (pointRange E a b g hb hp) (andIntro he (pointAddRecurrence E a b g hz hp))))

#print axioms pointAddRecurrence
#print axioms pointAddPrefix
end M6.PA.RelationalSource.PairGraph

