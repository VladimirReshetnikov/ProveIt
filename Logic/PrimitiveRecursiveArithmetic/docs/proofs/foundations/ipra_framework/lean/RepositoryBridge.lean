import ConciseIPRA.NativeBiInterpretation

/-!
Repository integration adapter; build inside the pinned ProveIt workspace.
Do not import ObjectKernel in this build: it is a standalone copy of the same
upstream kernel declarations.  To use ObjectBridge inside ProveIt, replace
its first import by `import ConciseIPRA.PR`.

This adapter was inspected against the pinned source but not compiled here
against the whole repository dependency closure.
-/

namespace LeanProofs.ConciseIPRA.FrameworkRepositoryBridge

open scoped Fm

theorem toNative {n : Nat} {Γ : List (Fm PTm n)} {φ : Fm PTm n}
    (h : Γ ⊢[PRAAx] φ) : NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.mp h

theorem fromNative {n : Nat} {Γ : List (NFm n)} {φ : NFm n}
    (h : NPrf Γ φ) : Γ.map NFm.toPRA ⊢[PRAAx] φ.toPRA :=
  native_iff_pra.mp h

end LeanProofs.ConciseIPRA.FrameworkRepositoryBridge
