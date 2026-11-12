import ConciseIPRA.OneContext
import ConciseIPRA.NativeBiInterpretation

/-!
Transfer of the existing native/iPRA interpretations along exact
identity-language consequence equivalence. Written against ProveIt commit
a4e5e96c456303cf231eab2aeeb3291d8889833f; not compiled in the delivery
environment. No new term or formula interpretation is introduced.
-/

namespace LeanProofs.ConciseIPRA

open scoped Fm

variable {n : ℕ}

theorem oneContext_iff_pra {Γ : List (NFm n)} {A : NFm n} :
    OPrf Γ A ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  oprf_iff_nprf.trans native_iff_pra

theorem pra_iff_oneContext {Γ : List (Fm PTm n)} {φ : Fm PTm n} :
    (Γ ⊢[PRAAx] φ) ↔ OPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ) :=
  pra_iff_native.trans oprf_iff_nprf.symm

theorem oneContext_roundTrip (A : NFm n) :
    OPrf [NFm.ofPRA A.toPRA] A ∧ OPrf [A] (NFm.ofPRA A.toPRA) :=
  ⟨OPrf.ofNative (native_roundTrip A).1,
   OPrf.ofNative (native_roundTrip A).2⟩

theorem pra_oneContext_roundTrip (φ : Fm PTm n) (Γ : List (Fm PTm n)) :
    Γ ⊢[PRAAx] Fm.iff φ (NFm.ofPRA φ).toPRA :=
  pra_native_roundTrip φ Γ

theorem oneContext_inconsistent_iff :
    OPrf ([] : List (NFm 0)) NFm.bot ↔ ([] ⊢[PRAAx] (Fm.bot : Fm PTm 0)) :=
  oprf_iff_nprf.trans native_inconsistent_iff

end LeanProofs.ConciseIPRA
