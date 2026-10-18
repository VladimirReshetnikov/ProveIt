import GowersSzemeredi.ComponentTradeoff

/-! Declarations of `ComponentTradeoff` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The original square-root trade-off, with the proof's inherited setup explicit. -/
def lemma_10_5_original_sqrt : Prop :=
  forall (N : Nat) [NeZero N] (X : Type*) [Fintype X] [DecidableEq X]
      (D : MultifunctionDomain N X) (phi : X -> ZMod N)
      (B : Finset (ZMod N)) (alpha rho : Real) (M : Nat) (sigma eta : Real)
      (x : X),
    Section10Setup D phi B alpha M sigma eta ->
    sigma <= eta * alpha ^ 2 -> IsSection10Anchor D phi B alpha M N eta x ->
    0 < rho -> rho <= alpha / 192 -> rho <= alpha ^ 2 / 32 ->
    sigma <= eta * rho ^ 4 * alpha / 384 ->
      exists W : Finset X,
        IsSection10RegularComponentAt D phi B x alpha eta rho M N (1 / 2) W

end LeanProofs.GowersSzemeredi
