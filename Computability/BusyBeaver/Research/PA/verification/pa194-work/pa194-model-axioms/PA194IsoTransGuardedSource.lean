import PA194CompositionInputs
import PA194CompositionContext
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194IsoTransGuardedSource
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194CompositionInputs PA194CompositionContext

def target : Form := ∀⁰ ∀⁰ ∀⁰ (domain (.bvar 2) 🡒 domain (.bvar 1) 🡒 domain (.bvar 0) 🡒
  orderIso (.bvar 2) (.bvar 1) 🡒 orderIso (.bvar 1) (.bvar 0) 🡒 orderIso (.bvar 2) (.bvar 0))

variable {Γ : List Form}
def proof (I : Inputs Γ) : ND.Proof Γ target := by
  unfold target
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  let A : Form := domain (.fvar 2)
  let B : Form := domain (.fvar 1)
  let C : Form := domain (.fvar 0)
  let D : Form := orderIso (.fvar 2) (.fvar 1)
  let E : Form := orderIso (.fvar 1) (.fvar 0)
  let Δ := E :: D :: C :: B :: A :: ND.shifted (ND.shifted (ND.shifted Γ))
  have hA : ND.Proof Δ A := ND.assumption (by simp [Δ])
  have hD : ND.Proof Δ D := ND.assumption (by simp [Δ])
  have hE : ND.Proof Δ E := ND.assumption (by simp [Δ])
  have I' : Inputs Δ := I.shift.shift.shift.weaken (fun _ hp => by simp [Δ,hp])
  have hi := I'.compose 2 1 0 hA hD hE
  have out := ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro hi))))
  convert out using 1 <;> (try dsimp [Δ,A,B,C,D,E]) <;> isoSyntax

def contextProof : ND.Proof compositionAxioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [compositionAxioms]),ND.assumption (by simp [compositionAxioms]),
    ND.assumption (by simp [compositionAxioms])⟩,ND.assumption (by simp [compositionAxioms])⟩,
    ND.assumption (by simp [compositionAxioms]),ND.assumption (by simp [compositionAxioms]),
    ND.assumption (by simp [compositionAxioms]),ND.assumption (by simp [compositionAxioms])⟩

def contextDerivation : LO.FirstOrder.Derivation (compositionAxioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp [ND.Proof])
#print axioms proof
#print axioms contextDerivation
end PA194IsoTransGuardedSource
