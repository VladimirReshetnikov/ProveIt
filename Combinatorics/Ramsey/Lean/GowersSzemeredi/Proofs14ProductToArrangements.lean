import GowersSzemeredi.Proofs14HigherArrangements

/-!
# From the product property to respected eight-arrangements

This module proves Lemma 14.8 by combining Corollary 14.6 with Lemma 14.7.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

theorem lemma_14_8_holds : lemma_14_8 := by
  intro N k _ beta gamma B phi hk hbeta hgamma hgamma_one hcard hproduct
  -- Lemma 14.7 applied to the bound of Corollary 14.6
  refine le_of_eq_of_le ?_ (lemma_14_7_holds N k _ B phi (by positivity)
    (corollary_14_6_holds N k beta gamma B phi hk hbeta hgamma hgamma_one hcard hproduct))
  rw [mul_pow, ← pow_mul, ← pow_mul, show 4 ^ (k + 1) * 7 = 7 * 4 ^ (k + 1) by ring,
    show 3 * k * 4 ^ (k + 1) * 7 = 21 * k * 4 ^ (k + 1) by ring]

end LeanProofs.GowersSzemeredi
