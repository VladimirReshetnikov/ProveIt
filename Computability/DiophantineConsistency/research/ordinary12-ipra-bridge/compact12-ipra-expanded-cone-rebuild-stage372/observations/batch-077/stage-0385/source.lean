import DiophantineConsistency.IPRAFoundationZFCStabilityWitness
import DiophantineConsistency.IPRAStableBackwardFinite
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCFiniteStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRAFoundationZFCWitnessBound DiophantineConsistency.IPRAFoundationZFCMappedNegation
open DiophantineConsistency.IPRAStableBackward DiophantineConsistency.IPRAStableBackwardFinite
open DiophantineConsistency.IPRAFoundationZFCReachStability DiophantineConsistency.IPRAFoundationZFCStabilityWitness
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

def zfcEquivFromFinite (f : ℒₒᵣ →ᵥ L)
    (hbound : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 (Semiformula.lMap f boundedRefutation)ᴺ)
    (witnesses : ∀ ψ, ψ ∈ reachList (matrixOpen f) → NeedsStability ψ → StabilityWitness T ψ) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f :=
  zfcEquivFromWitnesses f hbound (fun ψ hr hn => witnesses ψ (reachMem hr) hn)
end DiophantineConsistency.IPRAFoundationZFCFiniteStability
