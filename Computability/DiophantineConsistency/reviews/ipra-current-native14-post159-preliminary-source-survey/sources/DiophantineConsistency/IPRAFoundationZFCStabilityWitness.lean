import DiophantineConsistency.IPRAFoundationZFCTheoryStability
import DiophantineConsistency.IPRATheoryInstantiation
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCStabilityWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.IPRAFoundationZFCWitnessBound DiophantineConsistency.IPRAFoundationZFCMappedNegation
open DiophantineConsistency.IPRAStableBackward DiophantineConsistency.IPRAStableBackwardReach
open DiophantineConsistency.IPRAFoundationZFCReachStability DiophantineConsistency.IPRAFoundationZFCTheoryStability
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

structure StabilityWitness (T : Theoryᵢ L Λ) (ψ : Proposition L) where
  arity : ℕ
  body : Semisentenceᵢ L arity
  arguments : Fin arity → Term L ℕ
  bodyProof : T ⊢! ∀⁰* body
  instanceShape : (Rew.embSubsts arguments ▹ body) = (∼∼native ψ 🡒 native ψ)

def stabilityFromWitness (ψ : Proposition L) (w : StabilityWitness T ψ) :
    extended T ⊢! ∼∼native ψ 🡒 native ψ := by
  have hp := instantiateTheory w.body w.bodyProof w.arguments
  rw [w.instanceShape] at hp
  exact hp

def zfcEquivFromWitnesses (f : ℒₒᵣ →ᵥ L)
    (hbound : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 (Semiformula.lMap f boundedRefutation)ᴺ)
    (witnesses : ∀ ψ, Reach (matrixOpen f) ψ → NeedsStability ψ → StabilityWitness T ψ) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f :=
  zfcEquivFromTheory f hbound (fun ψ hreach hneed => stabilityFromWitness ψ (witnesses ψ hreach hneed))
end DiophantineConsistency.IPRAFoundationZFCStabilityWitness
