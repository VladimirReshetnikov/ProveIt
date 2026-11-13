import DiophantineConsistency.IPRAFoundationZFCMappedErasure
import DiophantineConsistency.IPRAExistentialComparison
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCMatrixComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.IPRAFoundationZFCWitnessBound DiophantineConsistency.IPRAFoundationZFCMappedErasure
open DiophantineConsistency.IPRAFoundationZFCMappedNegation DiophantineConsistency.IPRAExistentialComparison
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

def boundedComparison (f : ℒₒᵣ →ᵥ L)
    (h : T ⊢! ∀⁰ ((Semiformula.lMap f (bnd rho))ᴺ 🡒 native (Semiformula.lMap f (bnd rho)))) :
    T ⊢! (Semiformula.lMap f boundedRefutation)ᴺ 🡒 ∼∼native (Semiformula.lMap f boundedRefutation) := by
  have hc := theoryExistsCompare (T := T) (Semiformula.lMap f (bnd rho)) h
  exact hc

def mappedZFCWithMatrix (f : ℒₒᵣ →ᵥ L)
    (hbound : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 (Semiformula.lMap f boundedRefutation)ᴺ)
    (hmatrix : T ⊢! ∀⁰ ((Semiformula.lMap f (bnd rho))ᴺ 🡒 native (Semiformula.lMap f (bnd rho)))) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f :=
  mappedZFCNegationTwoPremises f hbound (boundedComparison f hmatrix)
end DiophantineConsistency.IPRAFoundationZFCMatrixComparison
