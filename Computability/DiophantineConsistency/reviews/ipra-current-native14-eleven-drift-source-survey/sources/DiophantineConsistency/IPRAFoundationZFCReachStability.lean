import DiophantineConsistency.IPRAFoundationZFCMatrixComparison
import DiophantineConsistency.IPRAStableBackwardReach
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCReachStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.StrictSigmaOneInduction DiophantineConsistency.IPRAFoundationZFCWitnessBound
open DiophantineConsistency.IPRAFoundationZFCMappedNegation DiophantineConsistency.IPRAFoundationZFCMatrixComparison
open DiophantineConsistency.IPRAStableBackward DiophantineConsistency.IPRAStableBackwardReach
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

def matrixOpen (f : ℒₒᵣ →ᵥ L) : Proposition L := free (Rewriting.emb (Semiformula.lMap f (bnd rho)))

def matrixCompare (f : ℒₒᵣ →ᵥ L)
    (stable : ∀ ψ, Reach (matrixOpen f) ψ → NeedsStability ψ → Λ ⊢! ∼∼native ψ 🡒 native ψ) :
    T ⊢! ∀⁰ ((Semiformula.lMap f (bnd rho))ᴺ 🡒 native (Semiformula.lMap f (bnd rho))) := by
  have ho := nativeBackwardReach (Λ := Λ) (matrixOpen f) stable
  have hg : Λ ⊢! ∀⁰ ((Rewriting.emb (Semiformula.lMap f (bnd rho)))ᴺ 🡒
      native (Rewriting.emb (Semiformula.lMap f (bnd rho)))) := by
    apply HilbertProofᵢ.gen
    change Λ ⊢! free ((Rewriting.emb (Semiformula.lMap f (bnd rho)))ᴺ) 🡒 free (native (Rewriting.emb (Semiformula.lMap f (bnd rho))))
    simpa only [matrixOpen, native_rew, Semiformula.rew_doubleNegation,
      LogicalConnective.HomClass.map_imply] using ho
  apply Theoryᵢ.ofHilbert
  simpa only [Rewriting.app_all, Rew.q_emb, Semiformula.emb_doubleNegation,
    native_rew, LogicalConnective.HomClass.map_imply] using hg

def zfcEquiv (f : ℒₒᵣ →ᵥ L)
    (hbound : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 (Semiformula.lMap f boundedRefutation)ᴺ)
    (stable : ∀ ψ, Reach (matrixOpen f) ψ → NeedsStability ψ → Λ ⊢! ∼∼native ψ 🡒 native ψ) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f :=
  mappedZFCWithMatrix f hbound (matrixCompare f stable)
end DiophantineConsistency.IPRAFoundationZFCReachStability
