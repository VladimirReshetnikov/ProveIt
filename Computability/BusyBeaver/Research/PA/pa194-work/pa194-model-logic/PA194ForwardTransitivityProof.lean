import PA194EqualTransitivity
import PA194TransitivitySyntax
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false
namespace PA194ForwardTransitivity
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped PA194InverseEqual PA194CompositionInputs PA194TransitivitySyntax
variable {Γ : List Form}

def mid1 : Ordinal.Formula 1 := ∀⁰ (Ordinal.domain (.bvar 0) 🡒 ∀⁰
  (Ordinal.domain (.bvar 0) 🡒 (equalTerm (.bvar 2) (.bvar 1) 🡒
    (equalTerm (.bvar 1) (.bvar 0) 🡒 equalTerm (.bvar 2) (.bvar 0)))))
def mid2 : Ordinal.Formula 1 := ∀⁰ (Ordinal.domain (.bvar 0) 🡒
  (equalTerm (.fvar 0) (.bvar 1) 🡒 (equalTerm (.bvar 1) (.bvar 0) 🡒 equalTerm (.fvar 0) (.bvar 0))))

theorem equalTerm_fvar (a b : Nat) : equalTerm (.fvar a) (.fvar b) = equalAt a b := rfl

def target : Form := formula PA194PAeq.transitivity
  (Fin.elim0 : Fin 0 → Ordinal.Term 0) (fun _ : Nat => (.fvar 0 : Ordinal.Term 0))

def proof (I : Inputs Γ) : ND.Proof Γ target := by
  unfold target
  rw [target_eq]
  apply ND.allIntro
  let D : Form := Ordinal.domain (.fvar 0)
  let Δ := D :: ND.shifted Γ
  let I' := I.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
  have h : ND.Proof Δ mid1.free := by
    change ND.Proof Δ (∀⁰ _)
    apply ND.allIntro
    let Ψ := D :: ND.shifted Δ
    let I'' := I'.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
    have h2 : ND.Proof Ψ mid2.free := by
      change ND.Proof Ψ (∀⁰ _)
      apply ND.allIntro
      let Θ := D :: ND.shifted Ψ
      let I3 := I''.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
      let A := equalAt 2 1
      let B := equalAt 1 0
      let Ω := B :: A :: Θ
      let I4 := I3.weaken (fun _ hp => List.mem_cons_of_mem B (List.mem_cons_of_mem A hp))
      have ha : ND.Proof Ω A := ND.assumption (by simp [Ω])
      have hb : ND.Proof Ω B := ND.assumption (by simp [Ω])
      have hc := equalTransitivity 2 1 0 I4 ha hb
      have hd := ND.impIntro (ND.impIntro (ND.impIntro hc))
      convert hd using 1
      simp [mid2,D,A,B,equalTerm_fvar,equalTerm_rew,sourceImply,Semiformula.rewAux_neg,Semiformula.free,Rewriting.free,app_eq_rewAux,
        Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q]
      simp [← Semiformula.neg_eq,Semiformula.rewAux_neg,domain_rew,equalTerm_rew,equalTerm_fvar,Rew.free,Rew.q]
      all_goals rfl
    have hd := ND.impIntro h2
    convert hd using 1
    simp [mid1,mid2,D,equalTerm_fvar,sourceImply,Semiformula.rewAux_neg,Semiformula.free,Rewriting.free,app_eq_rewAux,
      Semiformula.rewAux,domain_rew,equalTerm_rew,Rew.free,Rew.q]
    simp [← Semiformula.neg_eq,Semiformula.rewAux_neg,domain_rew,equalTerm_rew,equalTerm_fvar,Rew.free,Rew.q]
    all_goals rfl
  have out := ND.impIntro h
  convert out using 1
  simp [mid1,bound,D,equalTerm_fvar,sourceImply,Semiformula.rewAux_neg,Semiformula.free,Rewriting.free,app_eq_rewAux,
    Semiformula.rewAux,domain_rew,equalTerm_rew,Rew.free,Rew.q]
#print axioms proof
end PA194ForwardTransitivity
