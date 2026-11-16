import PA194InverseSymmetryInputs
import PA194InverseSymmetryContext
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194IsoSymmetryGuardedSource
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194InverseSymmetryInputs PA194InverseSymmetryContext

def target : Form := ∀⁰ ∀⁰ (domain (.bvar 1) 🡒 domain (.bvar 0) 🡒
  orderIso (.bvar 1) (.bvar 0) 🡒 orderIso (.bvar 0) (.bvar 1))

variable {Γ : List Form}
def proof (I : Inputs Γ) : ND.Proof Γ target := by
  unfold target
  apply ND.allIntro
  apply ND.allIntro
  let A : Form := domain (.fvar 1)
  let B : Form := domain (.fvar 0)
  let C : Form := orderIso (.fvar 1) (.fvar 0)
  let Δ := C :: B :: A :: ND.shifted (ND.shifted Γ)
  have hA : ND.Proof Δ A := ND.assumption (by simp [Δ])
  have hC : ND.Proof Δ C := ND.assumption (by simp [Δ])
  have I' : Inputs Δ := I.shift.shift.weaken (fun _ hp => by simp [Δ,hp])
  have hi := I'.inverse 1 0 hA hC
  have out := ND.impIntro (ND.impIntro (ND.impIntro hi))
  convert out using 1 <;> (try dsimp [Δ,A,B,C]) <;> isoSyntax

def contextProof : ND.Proof inverseSymmetryAxioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [inverseSymmetryAxioms]),ND.assumption (by simp [inverseSymmetryAxioms]),
    ND.assumption (by simp [inverseSymmetryAxioms])⟩,ND.assumption (by simp [inverseSymmetryAxioms])⟩,
    ND.assumption (by simp [inverseSymmetryAxioms]),ND.assumption (by simp [inverseSymmetryAxioms]),
    ND.assumption (by simp [inverseSymmetryAxioms]),ND.assumption (by simp [inverseSymmetryAxioms])⟩

def contextDerivation : LO.FirstOrder.Derivation (inverseSymmetryAxioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp [ND.Proof])
#print axioms proof
#print axioms contextDerivation
end PA194IsoSymmetryGuardedSource
