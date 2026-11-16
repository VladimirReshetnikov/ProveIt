import PA194EmptyOrderIso
import PA194ForwardReflContext
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194ZeroIsoGuardedSource
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

/-- The fixed source fact used by the naming interpretation. -/
def target : Form := ∀⁰ ∀⁰ (domain (.bvar 1) 🡒 zero (.bvar 1) 🡒
  domain (.bvar 0) 🡒 zero (.bvar 0) 🡒 orderIso (.bvar 1) (.bvar 0))

variable {Γ : List Form}
def proof (E : FormulaEquality Γ) : ND.Proof Γ target := by
  unfold target
  apply ND.allIntro
  apply ND.allIntro
  let A : Form := domain (.fvar 1)
  let B : Form := zero (.fvar 1)
  let C : Form := domain (.fvar 0)
  let D : Form := zero (.fvar 0)
  let Δ := D :: C :: B :: A :: ND.shifted (ND.shifted Γ)
  have hB : ND.Proof Δ B := ND.assumption (by simp [Δ])
  have hD : ND.Proof Δ D := ND.assumption (by simp [Δ])
  have E' : FormulaEquality Δ := E.shifted.shifted.weaken (fun _ hp => by simp [Δ,hp])
  have hi := emptyOrderIso E' 1 0 hB hD
  have out := ND.impIntro (ND.impIntro (ND.impIntro (ND.impIntro hi)))
  convert out using 1 <;> (try dsimp [Δ,A,B,C,D]) <;> isoSyntax

def contextProof : ND.Proof identityAxioms target :=
  proof ⟨⟨ND.assumption (by simp [identityAxioms]),ND.assumption (by simp [identityAxioms]),
    ND.assumption (by simp [identityAxioms])⟩,ND.assumption (by simp [identityAxioms])⟩

def contextDerivation : LO.FirstOrder.Derivation (identityAxioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp [ND.Proof])
#print axioms proof
#print axioms contextDerivation
end PA194ZeroIsoGuardedSource
