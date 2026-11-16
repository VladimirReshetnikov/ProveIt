import PA194SuccExtensionInputs
import PA194ForwardReflContext
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194SuccIsoGuardedSource
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194SuccExtensionInputs

def target : Form := ∀⁰ ∀⁰ ∀⁰ ∀⁰ (domain (.bvar 3) 🡒 domain (.bvar 2) 🡒 domain (.bvar 1) 🡒 domain (.bvar 0) 🡒
  successor (.bvar 3) (.bvar 2) 🡒 successor (.bvar 1) (.bvar 0) 🡒
    orderIso (.bvar 3) (.bvar 1) 🡒 orderIso (.bvar 2) (.bvar 0))

variable {Γ : List Form}
def proof (I : Inputs Γ) : ND.Proof Γ target := by
  unfold target
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  let A : Form := domain (.fvar 3)
  let B : Form := domain (.fvar 2)
  let C : Form := domain (.fvar 1)
  let D : Form := domain (.fvar 0)
  let E : Form := successor (.fvar 3) (.fvar 2)
  let F : Form := successor (.fvar 1) (.fvar 0)
  let G : Form := orderIso (.fvar 3) (.fvar 1)
  let Δ := G :: F :: E :: D :: C :: B :: A :: ND.shifted (ND.shifted (ND.shifted (ND.shifted Γ)))
  have hA : ND.Proof Δ A := ND.assumption (by simp [Δ])
  have hC : ND.Proof Δ C := ND.assumption (by simp [Δ])
  have hE : ND.Proof Δ E := ND.assumption (by simp [Δ])
  have hF : ND.Proof Δ F := ND.assumption (by simp [Δ])
  have hG : ND.Proof Δ G := ND.assumption (by simp [Δ])
  have I' : Inputs Δ := I.shift.shift.shift.shift.weaken (fun _ hp => by simp [Δ,hp])
  have hi := I'.extend 3 1 2 0 hA hC hE hF hG
  have out := ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro hi))))))
  convert out using 1 <;> (try dsimp [Δ,A,B,C,D,E,F,G]) <;> isoSyntax

def contextProof : ND.Proof identityAxioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [identityAxioms]),ND.assumption (by simp [identityAxioms]),
    ND.assumption (by simp [identityAxioms])⟩,ND.assumption (by simp [identityAxioms])⟩,
    ND.assumption (by simp [identityAxioms]),ND.assumption (by simp [identityAxioms]),
    ND.assumption (by simp [identityAxioms])⟩

def contextDerivation : LO.FirstOrder.Derivation (identityAxioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp [ND.Proof])
#print axioms proof
#print axioms contextDerivation
end PA194SuccIsoGuardedSource
