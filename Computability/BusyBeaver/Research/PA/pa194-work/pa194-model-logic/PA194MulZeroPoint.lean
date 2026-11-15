import PA194ForwardTyped
import PA194FoundationAdditionZeroExistence
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardMulZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}
attribute [local irreducible] addResult

def pointMulRecurrence (a base g : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar a) (.fvar g))) :
    ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base)) := by
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have pp := pointShift (a+1+1) (a+1+1) (g+1+1)
    (pointShift (a+1) (a+1) (g+1) (pointShift a a g hp))
  have zz := Ordinal.zeroShift (a+1+1) (Ordinal.zeroShift (a+1) (Ordinal.zeroShift a hz))
  have hi := ND.andLeft (pointAt (a+1+1+1) (a+1+1+1) (g+1+1+1) 2 1 pp)
  have result : ND.Proof (ND.shifted (ND.shifted (ND.shifted Γ)))
      (sourceImply (edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏
        Ordinal.successor (.fvar 0) (.fvar 2))
        (∃⁰ (edge (.fvar (g+1+1+1)) (.fvar 0) (.bvar 0) ⋏
          addResult (.bvar 0) (.fvar (base+1+1+1)) (.fvar 1)))) := by
    apply ND.impIntro
    let q : Form := edge (.fvar (g+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hh : ND.Proof (q :: ND.shifted (ND.shifted (ND.shifted Γ))) q := ND.assumption (by simp)
    let EE := E.shifted.shifted.shifted.weaken (fun r hr => List.mem_cons_of_mem q hr)
    have he := ND.andLeft (ND.mp (ND.andLeft hh) (ND.up hi q))
    have hz' := zeroTransport EE (a+1+1+1) 2 (EE.symmetryOf he) (ND.up zz q)
    exact ND.botElim (noSuccessorZero EE 0 2 hz' (ND.andRight hh))
  convert result using 1 <;>
    (simp only [mulRecurrence,Ordinal.successor,Semiformula.free,Rewriting.free,Semiformula.rewAux,addResult_rew] <;> traceSyntax)
  simp only [addResult_rew,Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app]
  rfl


def pointMulPrefix (a base g : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar a) (.fvar g))) :
    ND.Proof Γ (mulPrefix (.fvar a) (.fvar base) (.fvar a) (.fvar g)) := by
  have he := ND.mp (ND.andIntro (E.reflexive (.fvar a)) (E.reflexive (.fvar a)))
    (ND.andRight (pointAt a a g a a hp))
  exact ND.andIntro (pointDomain E a a g hz hp)
    (ND.andIntro (pointFunctional E a a g hp)
      (ND.andIntro (pointRange E a a g hd hp) (ND.andIntro he (pointMulRecurrence a base g E hz hp))))
#print axioms pointMulRecurrence
#print axioms pointMulPrefix
end PA194ForwardMulZero
