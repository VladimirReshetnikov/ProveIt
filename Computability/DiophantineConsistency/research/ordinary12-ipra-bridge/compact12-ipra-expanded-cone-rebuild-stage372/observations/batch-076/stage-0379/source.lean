import DiophantineConsistency.IPRAFoundationZFCMappedNegation
import DiophantineConsistency.IPRARefutationWitnessBridge
import DiophantineConsistency.StrictSigmaOneInduction

/-! Conditional GG comparison using the exact bounded Foundation predicate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open FoundationZFCConsistencyNat FoundationHAConsistencyNormalization
open IPRANativeFormula IPRARefutationWitnessBridge StrictSigmaOneInduction
open IPRAFoundationZFCMappedNegation
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

/-- Exact single-bound sentence obtained from the actual Foundation rho. -/
noncomputable def boundedRefutation : ArithmeticSentence := ∃⁰ (bnd rho)

/-- The bound-parameter matrix is syntactically Δ₀ in Foundation's hierarchy. -/
theorem boundedMatrix_isDeltaZero : Hierarchy 𝚺 0 (bnd rho) :=
  hierarchy_bnd rho_sigma_one (by decide) (by intro _; rfl)

/-- The mapped exact consistency image follows from three explicit theory
proofs concerning the actual `∃ b, bnd rho` sentence. -/
def mappedZFCNegationOfBound (f : ℒₒᵣ →ᵥ L)
    (hbound : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 (Semiformula.lMap f boundedRefutation)ᴺ)
    (hcompare : T ⊢! (Semiformula.lMap f boundedRefutation)ᴺ 🡒
      ∼∼native (Semiformula.lMap f boundedRefutation))
    (herase : T ⊢! native (Semiformula.lMap f boundedRefutation) 🡒
      native (Semiformula.lMap f rho)) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f := by
  rw [source_eq_neg_rho, LogicalConnective.HomClass.map_neg]
  exact negationOfWitness (Semiformula.lMap f rho) (Semiformula.lMap f boundedRefutation)
    hbound hcompare herase
end DiophantineConsistency.IPRAFoundationZFCWitnessBound
