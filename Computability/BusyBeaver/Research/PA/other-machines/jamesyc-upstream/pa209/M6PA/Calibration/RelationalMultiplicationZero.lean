module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationTrace
@[expose] public section

/-! The genuine zero-input multiplication trace: its recurrence is proved from the
impossibility of a predecessor for an actual empty ordinal. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def pointMulRecurrence {Γ : List Form} (E : FormulaEquality Γ) (a b g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar a) (.fvar g))) :
    ND.Proof Γ (mulRecurrence (.fvar g) (.fvar b)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have pp := pointShift (a+1+1) (a+1+1) (g+1+1)
    (pointShift (a+1) (a+1) (g+1) (pointShift a a g hp))
  have zz := Ordinal.zeroShift (a+1+1) (Ordinal.zeroShift (a+1) (Ordinal.zeroShift a hz))
  have hi := andLeft (pointAt (a+1+1+1) (a+1+1+1) (g+1+1+1) 2 1 pp)
  have result : ND.Proof (shifted (shifted (shifted Γ)))
      (sourceImply (edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏
        Ordinal.successor (.fvar 0) (.fvar 2))
        (∃¹ (edge (.fvar (g+1+1+1)) (.fvar 0) (.bvar 0) ⋏
          addResult (.bvar 0) (.fvar (b+1+1+1)) (.fvar 1)))) := by
    apply impIntro
    let q : Form := edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hh : ND.Proof (q :: shifted (shifted (shifted Γ))) q := assumption (by simp)
    let EE := E.shifted.shifted.shifted.weaken (fun r hr => List.mem_cons_of_mem q hr)
    have he := andLeft (mp (andLeft hh) (up hi q))
    have hz' := zeroTransport EE (a+1+1+1) 2 (EE.symmetryOf he) (up zz q)
    exact botElim (noSuccessorZero EE 0 2 hz' (andRight hh))
  convert result using 1 <;> mulSyntax

def pointMulPrefix {Γ : List Form} (E : FormulaEquality Γ) (a b g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar a) (.fvar g))) :
    ND.Proof Γ (mulPrefix (.fvar a) (.fvar b) (.fvar a) (.fvar g)) := by
  have he := mp (andIntro (E.reflexive (.fvar a)) (E.reflexive (.fvar a))) (andRight (pointAt a a g a a hp))
  exact andIntro (pointDomain E a a g hz hp)
    (andIntro (pointFunctional E a a g hp)
      (andIntro (pointRange E a a g (Ordinal.zeroDomain (.fvar a) hz) hp) (andIntro he (pointMulRecurrence E a b g hz hp))))

#print axioms pointMulRecurrence
#print axioms pointMulPrefix
end M6.PA.RelationalSource.PairGraph
