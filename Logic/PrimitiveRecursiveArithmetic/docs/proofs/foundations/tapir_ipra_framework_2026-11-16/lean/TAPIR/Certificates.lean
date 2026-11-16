import IPRADerivations.Foundations.TAPIR.Kernel
import IPRADerivations.Foundations.BoundedReflection

/-!
# Certificate escape macros

This file records exact targets for proof-local sealing, invariant observers,
and publicly named bounded witnesses.  The first and third declarations should
compile by direct reuse of existing checked rules.  Observer packages remain a
blueprint because their public relation is domain-specific.
-/

namespace LeanProofs.IPRA.TAPIR

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedReflection
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Proof-local certificates are eliminated by ordinary existential
elimination.  No bounded search is involved. -/
def sealCertificate {θ : Fm PTm (n + 1)} {ψ : Fm PTm n}
    (hex : Plan Γ (Fm.ex θ))
    (body : Plan (θ :: Γ.map Fm.shift) ψ.shift) : Plan Γ ψ :=
  Plan.seal hex body

/-- Re-export the checked bounded-choice theorem as the named-certificate
endpoint used by TAPIR. -/
theorem namedWitness (f : PTm 2) {N x : PTm n}
    (h : Γ ⊢[PRAAx]
      Fm.ex (lt (var 0) (Syn.shift N) ⋏
        neg (inst2 f (var 0) (Syn.shift x) ≐ zero))) :
    Γ ⊢[PRAAx]
      lt (wit f N x) N ⋏ neg (inst2 f (wit f N x) x ≐ zero) :=
  bounded_choice f h

/-- A theorem-specific observer package.  `obs` may be a term, tuple code, or
any finite public datum.  The two fields are intentionally object derivations. -/
structure ExactObserver (cert : Fm PTm (n + 1)) (obs : PTm (n + 1)) where
  public : Fm PTm n
  derives : cert :: ([] : List (Fm PTm n)).map Fm.shift ⊢[PRAAx] public.shift
  invariant : cert :: cert.shift :: ([] : List (Fm PTm (n + 1))).map Fm.shift ⊢[PRAAx]
    obs ≐ Syn.shift obs

/-- Target theorem: a valid local certificate plus an observer derivation can
be sealed.  The exact binder bookkeeping should be specialized to the chosen
observer representation. -/
theorem sealExactObserver
    {cert : Fm PTm (n + 1)} {public : Fm PTm n}
    (hex : Γ ⊢[PRAAx] Fm.ex cert)
    (hpub : cert :: Γ.map Fm.shift ⊢[PRAAx] public.shift) :
    Γ ⊢[PRAAx] public := by
  exact Prf.exE hex hpub

/-- Blueprint for a stable observer.  `close` is a domain-specific relation
such as rational distance at most an error term. -/
structure StableObserver (cert : Fm PTm (n + 1)) where
  obs : PTm (n + 1)
  close : PTm (n + 1) → PTm (n + 1) → Fm PTm (n + 1)
  compatible : cert :: cert.shift :: ([] : List (Fm PTm (n + 1))).map Fm.shift ⊢[PRAAx]
    close obs (Syn.shift obs)

end LeanProofs.IPRA.TAPIR
