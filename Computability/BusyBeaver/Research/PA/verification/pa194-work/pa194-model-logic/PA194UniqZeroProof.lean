import PA194UniqZeroSyntax
import PA194EqualZeroUnique
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194UniqZeroProof
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped PA194InverseEqual PA194EqualZero PA194UniqZeroQuote PA194UniqZeroSyntax
open PA194TransitivitySyntax (equalTerm equalTerm_rew)
variable {Γ : List Form}

def mid : Ordinal.Formula 1 := ∀⁰ (Ordinal.domain (.bvar 0) 🡒
  (equalZeroTerm (.bvar 1) 🡒 (equalZeroTerm (.bvar 0) 🡒 equalTerm (.bvar 1) (.bvar 0))))

theorem equalZeroTerm_fvar (a : Nat) : equalZeroTerm (.fvar a) = equalZeroAt a := rfl
theorem equalTerm_fvar (a b : Nat) : equalTerm (.fvar a) (.fvar b) = equalAt a b := rfl

def target : Form := formula uniqZero (Fin.elim0 : Fin 0 → Ordinal.Term 0)
  (fun _ : Nat => (.fvar 0 : Ordinal.Term 0))

def proof (E : FormulaEquality Γ) : ND.Proof Γ target := by
  unfold target
  rw [target_eq]
  apply ND.allIntro
  let D : Form := Ordinal.domain (.fvar 0)
  let Δ := D :: ND.shifted Γ
  let E' := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem D hp)
  have h : ND.Proof Δ mid.free := by
    change ND.Proof Δ (∀⁰ _)
    apply ND.allIntro
    let Ψ := D :: ND.shifted Δ
    let E'' := E'.shifted.weaken (fun _ hp => List.mem_cons_of_mem D hp)
    let A := equalZeroAt 1
    let B := equalZeroAt 0
    let Ω := B :: A :: Ψ
    let E3 := E''.weaken (fun _ hp => List.mem_cons_of_mem B (List.mem_cons_of_mem A hp))
    have ha : ND.Proof Ω A := ND.assumption (by simp [Ω])
    have hb : ND.Proof Ω B := ND.assumption (by simp [Ω])
    have hc := unique 1 0 E3 ha hb
    have hd := ND.impIntro (ND.impIntro (ND.impIntro hc))
    convert hd using 1
    simp [mid,bound,D,A,B,equalTerm_fvar,equalZeroTerm_fvar,equalTerm_rew,equalZeroTerm_rew,
      sourceImply,Semiformula.rewAux_neg,Semiformula.free,Rewriting.free,app_eq_rewAux,
      Semiformula.rewAux,domain_rew,zero_rew,orderIso_rew,eq,Rew.free,Rew.q]
    simp [← Semiformula.neg_eq,Semiformula.rewAux_neg,domain_rew,equalTerm_rew,equalZeroTerm_rew,
      equalTerm_fvar,equalZeroTerm_fvar,Rew.free,Rew.q]
    all_goals rfl
  have out := ND.impIntro h
  convert out using 1
  simp [mid,bound,D,equalTerm_fvar,equalZeroTerm_fvar,equalTerm_rew,equalZeroTerm_rew,
    sourceImply,Semiformula.rewAux_neg,Semiformula.free,Rewriting.free,app_eq_rewAux,
    Semiformula.rewAux,domain_rew,zero_rew,orderIso_rew,eq,Rew.free,Rew.q]
#print axioms proof
end PA194UniqZeroProof
