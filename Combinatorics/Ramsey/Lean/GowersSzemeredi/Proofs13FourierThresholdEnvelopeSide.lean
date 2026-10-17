import GowersSzemeredi.Proofs13FourierThresholdEnvelope
import GowersSzemeredi.Proofs13FejerExplicitExponentSide

/-! Declarations of `Proofs13FourierThresholdEnvelope` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The proper common-step bilinear Fourier square with improved size and
density exists whenever N exceeds the displayed double exponential. -/
theorem theorem_13_12_fejer_double_exponential (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime]
    (hN : Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) ≤ N)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
      (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))) ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ :=
  theorem_13_12_fejer_explicit_threshold alpha hα hαone N
    ((section13FourierThreshold_le_double_exp hα hαone).trans hN) f hf hnot

end LeanProofs.GowersSzemeredi
