import DiophantineConsistency.IPRABoundedMappedErasure
import DiophantineConsistency.IPRAFoundationZFCWitnessBound
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCMappedErasure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat
open DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRAFoundationZFCWitnessBound
open DiophantineConsistency.IPRABoundedMappedErasure
open DiophantineConsistency.IPRANativeFormulaRew
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

/-- Native erasure for the literal mapped Foundation refutation bound. -/
def exactErasure (f : ℒₒᵣ →ᵥ L) :
    T ⊢! native (Semiformula.lMap f boundedRefutation) 🡒 native (Semiformula.lMap f rho) := by
  have h := existsErasure (Λ := Λ) f rho
  apply Theoryᵢ.ofHilbert
  simpa only [boundedRefutation, Semiformula.lMap_emb, native_rew, LogicalConnective.HomClass.map_imply] using h
/-- Only the translated-bound and bounded comparison premises remain. -/
def mappedZFCNegationTwoPremises (f : ℒₒᵣ →ᵥ L)
    (hbound : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 (Semiformula.lMap f boundedRefutation)ᴺ)
    (hcompare : T ⊢! (Semiformula.lMap f boundedRefutation)ᴺ 🡒
      ∼∼native (Semiformula.lMap f boundedRefutation)) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘
      ∼IPRAFoundationZFCMappedNegation.mappedNativeRefutation f :=
  mappedZFCNegationOfBound f hbound hcompare (exactErasure f)
end DiophantineConsistency.IPRAFoundationZFCMappedErasure
