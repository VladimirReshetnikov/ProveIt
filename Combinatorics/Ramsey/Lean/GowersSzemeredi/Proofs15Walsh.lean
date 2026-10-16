import GowersSzemeredi.Proofs15WalshGeneral

/-!
# Proven companion for Gowers (2001), Lemma 15.1
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- **Lemma 15.1 (Walsh basis).** Constancy of all polynomial moments
forces the coefficient function to be a scalar multiple of parity. The
ternary hypothesis is not needed (`signedWalsh_multiple_of_invariant`). -/
theorem lemma_15_1_holds : lemma_15_1 :=
  fun _ _ _ hprime hodd h eta hh _ hinvariant =>
    signedWalsh_multiple_of_invariant hprime hodd h eta hh hinvariant

end LeanProofs.GowersSzemeredi
