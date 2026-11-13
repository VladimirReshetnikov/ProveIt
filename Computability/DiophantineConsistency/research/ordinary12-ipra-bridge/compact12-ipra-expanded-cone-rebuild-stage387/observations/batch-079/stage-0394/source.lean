import DiophantineConsistency.IPRANativeDisjunctionWitness
/-! Package a uniformly stable finite-arity native body as an exact stability witness. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeWitnessFamily
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRANativeDisjunctionWitness
open DiophantineConsistency.IPRAFoundationZFCStabilityWitness DiophantineConsistency.IPRANativeFormula

def witnessFromFamily (ψ : Proposition language) (n : ℕ)
    (body : Semisentenceᵢ language n) (v : Fin n → Term language ℕ)
    (h : ∀ w : Fin n → Term language ℕ,
      extended nativeTheory ⊢! ∼∼(Rew.embSubsts w ▹ body) 🡒 (Rew.embSubsts w ▹ body))
    (hshape : (Rew.embSubsts v ▹ body) = native ψ) :
    StabilityWitness nativeTheory ψ := by
  let stableBody : Semisentenceᵢ language n := ∼∼body 🡒 body
  have hp : nativeTheory ⊢! ∀⁰* stableBody := by
    apply closeFamily n stableBody
    intro w
    simpa only [stableBody, LogicalConnective.HomClass.map_imply,
      LogicalConnective.HomClass.map_neg] using h w
  refine ⟨n,stableBody,v,hp,?_⟩
  simp only [stableBody, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_neg, hshape]
end DiophantineConsistency.IPRANativeWitnessFamily
