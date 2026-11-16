import PA194AdditionPrefixSep
import PA194ForwardReflContext
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194AdditionTotalGuardedSource
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194AdditionPrefixSep

def target : Form := ∀⁰ ∀⁰ (domain (.bvar 1) 🡒 domain (.bvar 0) 🡒 addOutput (.bvar 1) (.bvar 0))

def proof {Γ : List Form} (S : SetProofs Γ) (hs : ND.Proof Γ closedSep) : ND.Proof Γ target := by
  unfold target
  apply ND.allIntro
  apply ND.allIntro
  let A : Form := domain (.fvar 1)
  let B : Form := domain (.fvar 0)
  let Δ := B :: A :: ND.shifted (ND.shifted Γ)
  have hA : ND.Proof Δ A := ND.assumption (by simp [Δ])
  have hB : ND.Proof Δ B := ND.assumption (by simp [Δ])
  have S' : SetProofs Δ := S.shift.shift.weaken (fun _ hp => by simp [Δ,hp])
  have hss : ND.Proof (ND.shifted (ND.shifted Γ)) closedSep := by
    simpa only [closedSep_shift] using ND.shiftProof (ND.shiftProof hs)
  have hs' : ND.Proof Δ closedSep := ND.weaken hss (fun _ hp => by simp [Δ,hp])
  have ht := prefixTotal S' 0 hB (sepAtZero hs')
  have hp := prefixTotalAt 0 1 ht hA
  have out := ND.impIntro (ND.impIntro (addOutputFromExists S'.equality 1 0 hp))
  convert out using 1 <;> (try dsimp [Δ,A,B]) <;> prefixSyntax

def axioms : List Form := closedSep :: identityAxioms

def contextProof : ND.Proof axioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [axioms,identityAxioms]),ND.assumption (by simp [axioms,identityAxioms]),
    ND.assumption (by simp [axioms,identityAxioms])⟩,ND.assumption (by simp [axioms,identityAxioms])⟩,
    ND.assumption (by simp [axioms,identityAxioms]),ND.assumption (by simp [axioms,identityAxioms]),
    ND.assumption (by simp [axioms,identityAxioms])⟩ (ND.assumption (by simp [axioms]))

def contextDerivation : LO.FirstOrder.Derivation (axioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp [ND.Proof])
#print axioms proof
#print axioms contextDerivation
end PA194AdditionTotalGuardedSource
