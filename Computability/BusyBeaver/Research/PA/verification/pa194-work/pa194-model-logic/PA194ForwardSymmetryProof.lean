import PA194InverseEqualSwap
import PA194ForwardTyped
import PA194PAeqTargetInventory
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false
namespace PA194ForwardSymmetry
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped PA194InverseEqual PA194InverseSymmetryInputs
variable {Γ : List Form}

def target : Form := formula PA194PAeq.symmetry
  (Fin.elim0 : Fin 0 → Ordinal.Term 0) (fun _ : Nat => (.fvar 0 : Ordinal.Term 0))

def proof (I : Inputs Γ) : ND.Proof Γ target := by
  unfold target
  change ND.Proof Γ (∀⁰ _)
  apply ND.allIntro
  let D : Form := Ordinal.domain (.fvar 0)
  let Δ := D :: ND.shifted Γ
  let I' := I.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
  let sub : SourceFormula 1 := .all (PA194PAeq.implies
    (PA194PAeq.eq (.bvar 1) (.bvar 0)) (PA194PAeq.eq (.bvar 0) (.bvar 1)))
  have h : ND.Proof Δ ((formula sub (bindEnv (Fin.elim0 : Fin 0 → Ordinal.Term 0))
      (shiftEnv (fun _ : Nat => (.fvar 0 : Ordinal.Term 0)))).free) := by
    change ND.Proof Δ (∀⁰ _)
    apply ND.allIntro
    let Ψ := D :: ND.shifted Δ
    let I'' := I'.shift.weaken (fun _ hp => List.mem_cons_of_mem D hp)
    let A := equalAt 1 0
    let Ω := A :: Ψ
    let I''' := I''.weaken (fun _ hp => List.mem_cons_of_mem A hp)
    have ha : ND.Proof Ω A := ND.assumption (by simp [Ω])
    have hs := ND.impIntro (equalSwap 1 0 I''' ha)
    have hd := ND.impIntro hs
    convert hd using 1 <;>
      (simp only [formula,PA194PAeq.symmetry,PA194PAeq.implies,PA194PAeq.eq,equal,value,
        bindEnv,shiftEnv,equalAt,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,
        orderIso_rew,eq,Rew.free,Rew.q,Rew.func] <;> try isoSyntax)
  have out := ND.impIntro h
  convert out using 1 <;>
    (simp only [formula,PA194PAeq.symmetry,PA194PAeq.implies,PA194PAeq.eq,equal,value,
      bindEnv,shiftEnv,equalAt,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,
      orderIso_rew,eq,Rew.free,Rew.q,Rew.func] <;> try isoSyntax)
#print axioms proof
end PA194ForwardSymmetry
