import PA194MulPrefixSep
import PA194MulInductionTotal
import PA194MulOutputFromExists
import PA194ForwardReflContext
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulTotalGuardedSource
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero PA194MulRecurrenceNew PA194MulPrefixSep
attribute [local irreducible] addResult mulPrefix mulResult

def target : Form := ∀⁰ ∀⁰ (domain (.bvar 1) 🡒 domain (.bvar 0) 🡒 mulOutput (.bvar 1) (.bvar 0))

def proof {Γ : List Form} (S : SetProofs Γ)
    (ha : ND.Proof Γ PA194AdditionTotalGuardedSource.target) (hsep : ND.Proof Γ PA194MulPrefixSep.closedSep) :
    ND.Proof Γ target := by
  unfold target
  apply ND.allIntro
  apply ND.allIntro
  let A : Form := domain (.fvar 1)
  let B : Form := domain (.fvar 0)
  let Δ := B :: A :: ND.shifted (ND.shifted Γ)
  have hA : ND.Proof Δ A := ND.assumption (by simp [Δ])
  have hB : ND.Proof Δ B := ND.assumption (by simp [Δ])
  have S' : SetProofs Δ := S.shift.shift.weaken (fun _ hp => by simp [Δ,hp])
  have ha' : ND.Proof Δ PA194AdditionTotalGuardedSource.target := by
    have h : ND.Proof (ND.shifted (ND.shifted Γ)) PA194AdditionTotalGuardedSource.target := by
      simpa only [additionTarget_shift] using ND.shiftProof (ND.shiftProof ha)
    exact ND.weaken h (fun _ hp => by simp [Δ,hp])
  have hs' : ND.Proof Δ PA194MulPrefixSep.closedSep := by
    have h : ND.Proof (ND.shifted (ND.shifted Γ)) PA194MulPrefixSep.closedSep := by
      simpa only [PA194MulPrefixSep.closedSep_shift] using ND.shiftProof (ND.shiftProof hsep)
    exact ND.weaken h (fun _ hp => by simp [Δ,hp])
  have ht := PA194MulRecurrenceNew.prefixTotal S'.equality 0 S'.empty S'.adjunction S'.intersection ha' hB (PA194MulPrefixSep.sepAtZero hs')
  have hi : ND.Proof Δ (domain (.fvar 1) 🡒 mulPrefixExists (.fvar 1) (.fvar 0)) := by
    convert ND.allElim _ (.fvar 1) ht using 1 <;>
      (simp [Ordinal.inductionConclusion,PA194MulRecurrenceNew.property,mulPrefixExists,Semiformula.rewAux,Ordinal.domain_rew,
        Ordinal.zero_rew,mulPrefix_rew,Rew.subst,Rew.q,Rew.func] <;> finishSourceSyntax)
  have hp := ND.mp hA hi
  have out := ND.impIntro (ND.impIntro (outputFromExists S'.equality 1 0 hp))
  convert out using 1 <;> (try dsimp [Δ,A,B,mulOutput]) <;>
    (simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,Rew.free,Rew.q,Rew.func] <;> finishSourceSyntax)

def axioms : List Form := PA194MulPrefixSep.closedSep :: PA194AdditionTotalGuardedSource.target :: identityAxioms

def contextProof : ND.Proof axioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [axioms,identityAxioms]),ND.assumption (by simp [axioms,identityAxioms]),
    ND.assumption (by simp [axioms,identityAxioms])⟩,ND.assumption (by simp [axioms,identityAxioms])⟩,
    ND.assumption (by simp [axioms,identityAxioms]),ND.assumption (by simp [axioms,identityAxioms]),
    ND.assumption (by simp [axioms,identityAxioms])⟩ (ND.assumption (by simp [axioms])) (ND.assumption (by simp [axioms]))

def contextDerivation : LO.FirstOrder.Derivation (axioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp [ND.Proof])
#print axioms proof
#print axioms contextDerivation
end PA194MulTotalGuardedSource
