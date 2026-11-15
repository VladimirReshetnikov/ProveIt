import PA194SuccCongruenceValue
import PA194SuccInjectiveSyntax
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false
namespace PA194ForwardSuccCongruence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped PA194InverseEqual PA194SuccExtensionInputs PA194SuccInjective PA194TransitivitySyntax
variable {Γ : List Form}

def bound : Ordinal.Formula 2 := equalTerm (.bvar 0) (.bvar 1) 🡒 succEqualTerm (.bvar 0) (.bvar 1)
def mid : Ordinal.Formula 1 := ∀⁰ (Ordinal.domain (.bvar 0) 🡒 bound)
def target : Form := formula PA194PAeq.succCongruence
  (Fin.elim0 : Fin 0 → Ordinal.Term 0) (fun _ : Nat => (.fvar 0 : Ordinal.Term 0))

theorem target_eq : target = ∀⁰ (Ordinal.domain (.bvar 0) 🡒 mid) := rfl

def proof (I : Inputs Γ) : ND.Proof Γ target := by
  rw [target_eq]
  apply ND.allIntro
  let D : Form := Ordinal.domain (.fvar 0)
  let Δ := D :: ND.shifted Γ
  let I' := I.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
  have h : ND.Proof Δ mid.free := by
    change ND.Proof Δ (∀⁰ _)
    apply ND.allIntro
    let Ψ := D :: ND.shifted Δ
    let I'' := I'.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
    let A := equalAt 0 1
    let Ω := A :: Ψ
    let I3 := I''.weaken (fun _ hp => List.mem_cons_of_mem A hp)
    have ha : ND.Proof Ω A := ND.assumption (by simp [Ω])
    have hs := ND.impIntro (succCongruenceValue 0 1 I3 ha)
    have hd := ND.impIntro hs
    convert hd using 1
    simp [mid,bound,D,A,succEqualTerm_fvar,succEqualTerm_rew,equalTerm_rew,
      sourceImply,Semiformula.rewAux_neg,Semiformula.free,Rewriting.free,app_eq_rewAux,
      Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q]
    simp [← Semiformula.neg_eq,Semiformula.rewAux_neg,domain_rew,succEqualTerm_rew,
      succEqualTerm_fvar,equalTerm_rew,Rew.free,Rew.q]
    all_goals rfl
  have out := ND.impIntro h
  convert out using 1
  simp [mid,bound,D,sourceImply,Semiformula.free,Rewriting.free,app_eq_rewAux,
    Semiformula.rewAux,domain_rew,succEqualTerm_rew,equalTerm_rew,Rew.free,Rew.q]
#print axioms target_eq
#print axioms proof
end PA194ForwardSuccCongruence
