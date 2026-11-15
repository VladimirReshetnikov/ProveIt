import PA194AddZeroShift
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardAddZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def equalFromOutput (a b : Nat) (E : FormulaEquality Γ)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a))) (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar b) (.fvar b)))
    (hout : ND.Proof Γ (addOutput (.fvar a) (.fvar b))) : ND.Proof Γ (equalAt b) := by
  let Q : Ordinal.Formula 1 := Ordinal.domain (.bvar 0) ⋏ addResult (.fvar a) (.fvar b) (.bvar 0)
  have hq : ND.Proof Γ (∃⁰ Q) := by
    convert hout using 1 <;> simp [addOutput,Q]
  apply ND.exsElim hq
  let Δ := Q.free :: ND.shifted Γ
  have hbody : ND.Proof Δ (Ordinal.domain (.fvar 0) ⋏ addResult (.fvar (a+1)) (.fvar (b+1)) (.fvar 0)) := by
    have h := ND.assumption (Γ := Δ) (p := Q.free) (by simp [Δ])
    convert h using 1
    simp [Q,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,addResult_rew,Rew.free,Rew.q]
  have E' : FormulaEquality Δ := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have ha' := ND.up (Ordinal.domainShift a ha) Q.free
  have hz' := ND.up (Ordinal.zeroShift a hz) Q.free
  have hb' := ND.up (Ordinal.domainShift b hb) Q.free
  have hi' : ND.Proof Δ (orderIso (.fvar (b+1)) (.fvar (b+1))) := by
    have h := ND.up (ND.shiftProof hi) Q.free
    convert h using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [orderIso_rew,Rew.shift,Rew.map]
  change ND.Proof Δ (equalAt b).shift
  rw [equalAt_shift]
  exact equalFromWitnesses (a+1) (b+1) 0 E' ha' hz' hb' (ND.andLeft hbody) (ND.andRight hbody) hi'
#print axioms equalFromOutput
end PA194ForwardAddZero
