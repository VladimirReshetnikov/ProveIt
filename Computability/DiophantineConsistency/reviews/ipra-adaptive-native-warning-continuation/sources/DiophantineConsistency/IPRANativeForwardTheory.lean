import DiophantineConsistency.IPRANativeForward

/-! Native-to-GG direction under any intuitionistic theory. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeForwardTheory
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open IPRANativeFormula IPRANativeFormulaRew IPRANativeForward
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

/-- This logical direction requires no arithmetic premises from T. -/
def theoryNativeForward (φ : Sentence L) : T ⊢! native φ 🡒 φᴺ := by
  apply Theoryᵢ.ofHilbert
  have h := nativeForward (Λ := Λ) (Rewriting.emb φ)
  simpa only [native_rew, Semiformula.emb_doubleNegation,
    LogicalConnective.HomClass.map_imply] using h
end DiophantineConsistency.IPRANativeForwardTheory
