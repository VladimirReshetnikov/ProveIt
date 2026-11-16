import PA194MulPrefixStep
import PA194AdditionTotalGuardedSource
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero

theorem additionTarget_shift : PA194AdditionTotalGuardedSource.target.shift = PA194AdditionTotalGuardedSource.target := by
  have hz : PA194AdditionTotalGuardedSource.target.fvSup = 0 := by decide
  have hf : PA194AdditionTotalGuardedSource.target.freeVariables = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hlt := Semiformula.lt_fvSup_of_fvar? (φ := PA194AdditionTotalGuardedSource.target) (m := x) hx
    omega
  exact PA194ModelLogic.syntactic_noFree_shift_fixed 0 PA194AdditionTotalGuardedSource.target hf

attribute [local irreducible] addResult mulPrefix

def supplyFromA1 {Γ : List Form} (base : Nat)
    (ha : ND.Proof Γ PA194AdditionTotalGuardedSource.target)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar base))) :
    ND.Proof Γ (additionSupply base) := by
  apply ND.allIntro
  have out : ND.Proof (ND.shifted Γ) (Ordinal.domain (.fvar 0) 🡒 addOutput (.fvar 0) (.fvar (base+1))) := by
    apply ND.impIntro
    let q : Form := Ordinal.domain (.fvar 0)
    let C := q :: ND.shifted Γ
    have hc : ND.Proof C q := ND.assumption (by simp [C])
    have ha' : ND.Proof C PA194AdditionTotalGuardedSource.target := by
      have hs : ND.Proof (ND.shifted Γ) PA194AdditionTotalGuardedSource.target := by
        simpa only [additionTarget_shift] using ND.shiftProof ha
      exact ND.up hs q
    have hb' := ND.up (PairGraph.domainShift base hb) q
    have hi : ND.Proof C (Ordinal.domain (.fvar 0) 🡒 Ordinal.domain (.fvar (base+1)) 🡒
        addOutput (.fvar 0) (.fvar (base+1))) := by
      convert ND.allElim _ (.fvar (base+1)) (ND.allElim _ (.fvar 0) ha') using 1 <;>
        (simp [PA194AdditionTotalGuardedSource.target,addOutput,Semiformula.rewAux,Ordinal.domain_rew,addResult_rew,
          Rew.subst,Rew.q,Rew.func] <;> finishSourceSyntax)
    exact ND.mp hb' (ND.mp hc hi)
  convert out using 1 <;>
    (dsimp [additionSupply,addOutput] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.domain_rew,addResult_rew,
      Rew.free,Rew.q,Rew.func] <;> finishSourceSyntax)
#print axioms additionTarget_shift
#print axioms supplyFromA1
end PA194MulRecurrenceNew
