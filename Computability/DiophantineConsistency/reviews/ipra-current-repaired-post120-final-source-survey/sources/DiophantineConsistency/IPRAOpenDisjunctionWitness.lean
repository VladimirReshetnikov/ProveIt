import DiophantineConsistency.IPRANativeWitnessFamily
/-! Exact disjunction stability witnesses from explicit uniform open child proof families. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAOpenDisjunctionWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRANativeDisjunctionWitness
open DiophantineConsistency.IPRAFoundationZFCStabilityWitness DiophantineConsistency.IPRANativeFormula

def fromOpenFamilies (φ ψ : Proposition language) (n : ℕ)
    (a b : Semisentenceᵢ language n) (v : Fin n → Term language ℕ)
    (ha : ∀ w : Fin n → Term language ℕ, extended nativeTheory ⊢!
      (Rew.embSubsts w ▹ a) ⋎ ∼(Rew.embSubsts w ▹ a))
    (hb : ∀ w : Fin n → Term language ℕ, extended nativeTheory ⊢!
      ∼∼(Rew.embSubsts w ▹ b) 🡒 (Rew.embSubsts w ▹ b))
    (hshapeA : (Rew.embSubsts v ▹ a) = native φ)
    (hshapeB : (Rew.embSubsts v ▹ b) = native ψ) : StabilityWitness nativeTheory (φ ⋎ ψ) := by
  have ha' : nativeTheory ⊢! ∀⁰* (a ⋎ ∼a) := by
    apply closeFamily n (a ⋎ ∼a)
    intro w
    simpa only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg] using ha w
  have hb' : nativeTheory ⊢! ∀⁰* (∼∼b 🡒 b) := by
    apply closeFamily n (∼∼b 🡒 b)
    intro w
    simpa only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg] using hb w
  exact disjunctionWitness φ ψ n a b v ha' hb' hshapeA hshapeB

def fromOpenFamiliesRight (φ ψ : Proposition language) (n : ℕ)
    (a b : Semisentenceᵢ language n) (v : Fin n → Term language ℕ)
    (ha : ∀ w : Fin n → Term language ℕ, extended nativeTheory ⊢!
      ∼∼(Rew.embSubsts w ▹ a) 🡒 (Rew.embSubsts w ▹ a))
    (hb : ∀ w : Fin n → Term language ℕ, extended nativeTheory ⊢!
      (Rew.embSubsts w ▹ b) ⋎ ∼(Rew.embSubsts w ▹ b))
    (hshapeA : (Rew.embSubsts v ▹ a) = native φ)
    (hshapeB : (Rew.embSubsts v ▹ b) = native ψ) : StabilityWitness nativeTheory (φ ⋎ ψ) := by
  have ha' : nativeTheory ⊢! ∀⁰* (∼∼a 🡒 a) := by
    apply closeFamily n (∼∼a 🡒 a)
    intro w
    simpa only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg] using ha w
  have hb' : nativeTheory ⊢! ∀⁰* (b ⋎ ∼b) := by
    apply closeFamily n (b ⋎ ∼b)
    intro w
    simpa only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg] using hb w
  exact disjunctionWitnessRight φ ψ n a b v ha' hb' hshapeA hshapeB
end DiophantineConsistency.IPRAOpenDisjunctionWitness
