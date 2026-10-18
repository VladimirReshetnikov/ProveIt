import GowersSzemeredi.Proofs16CommonBase

/-! Declarations of `Proofs16CommonBase` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- **Gowers, Lemma 16.7.** -/
theorem lemma_16_7_holds : lemma_16_7 := by
  unfold lemma_16_7
  intro N k _ theta gamma B phi H1 Y phiPrime
  dsimp only
  intro hH hX hY hselection
  let theta1 := section16ThetaOne theta gamma k
  have htheta1 : 0 ≤ theta1 := by
    dsimp only [theta1, section16ThetaOne]
    exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩).pow_nonneg _
  exact lemma_16_7_with theta1 (section16Zeta theta gamma k) htheta1
    B phi H1 Y phiPrime hH hX hY hselection

end LeanProofs.GowersSzemeredi
