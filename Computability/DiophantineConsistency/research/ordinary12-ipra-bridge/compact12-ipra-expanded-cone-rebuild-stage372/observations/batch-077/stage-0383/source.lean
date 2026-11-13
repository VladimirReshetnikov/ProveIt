import DiophantineConsistency.IPRAFoundationZFCReachStability
import DiophantineConsistency.IPRATheoryHilbertBridge
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCTheoryStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.StrictSigmaOneInduction DiophantineConsistency.IPRAFoundationZFCWitnessBound
open DiophantineConsistency.IPRAFoundationZFCMappedNegation DiophantineConsistency.IPRAFoundationZFCMatrixComparison
open DiophantineConsistency.IPRAStableBackward DiophantineConsistency.IPRAStableBackwardReach
open DiophantineConsistency.IPRAFoundationZFCReachStability DiophantineConsistency.IPRATheoryHilbertBridge
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

def matrixCompareFromTheory (f : ℒₒᵣ →ᵥ L)
    (stable : ∀ ψ, Reach (matrixOpen f) ψ → NeedsStability ψ → extended T ⊢! ∼∼native ψ 🡒 native ψ) :
    T ⊢! ∀⁰ ((Semiformula.lMap f (bnd rho))ᴺ 🡒 native (Semiformula.lMap f (bnd rho))) := by
  have ho := nativeBackwardReach (Λ := extended T) (matrixOpen f) stable
  have hg : extended T ⊢! ∀⁰ ((Rewriting.emb (Semiformula.lMap f (bnd rho)))ᴺ 🡒
      native (Rewriting.emb (Semiformula.lMap f (bnd rho)))) := by
    apply HilbertProofᵢ.gen
    change extended T ⊢! free ((Rewriting.emb (Semiformula.lMap f (bnd rho)))ᴺ) 🡒 free (native (Rewriting.emb (Semiformula.lMap f (bnd rho))))
    simpa only [matrixOpen, native_rew, Semiformula.rew_doubleNegation,
      LogicalConnective.HomClass.map_imply] using ho
  apply extendedToTheory T
  simpa only [Rewriting.app_all, Rew.q_emb, Semiformula.emb_doubleNegation,
    native_rew, LogicalConnective.HomClass.map_imply] using hg

def zfcEquivFromTheory (f : ℒₒᵣ →ᵥ L)
    (hbound : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 (Semiformula.lMap f boundedRefutation)ᴺ)
    (stable : ∀ ψ, Reach (matrixOpen f) ψ → NeedsStability ψ → extended T ⊢! ∼∼native ψ 🡒 native ψ) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f :=
  mappedZFCWithMatrix f hbound (matrixCompareFromTheory f stable)
end DiophantineConsistency.IPRAFoundationZFCTheoryStability
