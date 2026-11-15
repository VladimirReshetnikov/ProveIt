import PA194SuccInjectiveSyntax
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false
namespace PA194ForwardSuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped PA194InverseEqual PA194CancelInputs PA194SuccInjective PA194TransitivitySyntax
variable {Γ : List Form}

def mid : Ordinal.Formula 1 := ∀⁰ (Ordinal.domain (.bvar 0) 🡒
  (succEqualTerm (.bvar 1) (.bvar 0) 🡒 equalTerm (.bvar 1) (.bvar 0)))

def target : Form := formula PA194PAeq.succInjective
  (Fin.elim0 : Fin 0 → Ordinal.Term 0) (fun _ : Nat => (.fvar 0 : Ordinal.Term 0))

def proof (I : Inputs Γ) : ND.Proof Γ target := by
  unfold target
  rw [PA194SuccInjective.target_eq]
  apply ND.allIntro
  let D : Form := Ordinal.domain (.fvar 0)
  let Δ := D :: ND.shifted Γ
  let I' := I.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
  have h : ND.Proof Δ mid.free := by
    change ND.Proof Δ (∀⁰ _)
    apply ND.allIntro
    let Ψ := D :: ND.shifted Δ
    let I'' := I'.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
    let A := succEqualAt 1 0
    let Ω := A :: Ψ
    let I3 := I''.weaken (fun _ hp => List.mem_cons_of_mem A hp)
    have ha : ND.Proof Ω A := ND.assumption (by simp [Ω])
    have hs := ND.impIntro (succInjectiveValue 1 0 I3 ha)
    have hd := ND.impIntro hs
    convert hd using 1
    simp [mid,D,A,succEqualTerm_fvar,succEqualTerm_rew,PA194TransitivitySyntax.equalTerm_rew,
      sourceImply,Semiformula.rewAux_neg,Semiformula.free,Rewriting.free,app_eq_rewAux,
      Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q]
    simp [← Semiformula.neg_eq,Semiformula.rewAux_neg,domain_rew,succEqualTerm_rew,
      succEqualTerm_fvar,PA194TransitivitySyntax.equalTerm_rew,Rew.free,Rew.q]
    all_goals rfl
  have out := ND.impIntro h
  convert out using 1
  simp [mid,PA194SuccInjective.bound,D,sourceImply,Semiformula.free,Rewriting.free,app_eq_rewAux,
    Semiformula.rewAux,domain_rew,succEqualTerm_rew,PA194TransitivitySyntax.equalTerm_rew,Rew.free,Rew.q]
#print axioms proof
end PA194ForwardSuccInjective
