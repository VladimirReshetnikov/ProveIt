import ConciseIPRA.NativeBiInterpretation

/-!
STATUS: not compiled in this delivery environment. This generic transfer
uses the actual API inspected at ProveIt commit
f1b0582aada7262b10924ea1ba12e2e490d2934b. It supplies no Pell proof by itself.
Run it inside the pinned ProveIt workspace after building ConciseIPRA.
-/

namespace PellIPRATransfer

open LeanProofs.ConciseIPRA
open scoped Fm

theorem toNative {φ : Fm PTm 0}
    (h : ([] : List (Fm PTm 0)) ⊢[PRAAx] φ) :
    NPrf [] (NFm.ofPRA φ) := by
  simpa using (pra_iff_native).mp h

end PellIPRATransfer
