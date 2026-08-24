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
  let theta :=
    beta ^ (4 ^ (k + 1)) * gamma ^ (3 * k * 4 ^ (k + 1))
  have htheta : 0 < theta := by
    dsimp only [theta]
    exact mul_pos (pow_pos hbeta _) (pow_pos hgamma _)
  have hpairs :
      theta * (N : Real) ^ (5 * k + 3) ≤
        respectedGeneralArrangementCount 2 B phi := by
    dsimp only [theta]
    exact corollary_14_6_holds N k beta gamma B phi hk hbeta hgamma
      hgamma_one hcard hproduct
  have height := lemma_14_7_holds N k theta B phi htheta hpairs
  have hbetaExponent :
      7 * 4 ^ (k + 1) = 4 ^ (k + 1) * 7 := by omega
  have hgammaExponent :
      21 * k * 4 ^ (k + 1) = (3 * k * 4 ^ (k + 1)) * 7 := by ring
  calc
    beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1)) *
        (N : Real) ^ (17 * k + 15) =
      theta ^ 7 * (N : Real) ^ (17 * k + 15) := by
        dsimp only [theta]
        rw [mul_pow, ← pow_mul, ← pow_mul, hbetaExponent, hgammaExponent]
    _ ≤ (respectedGeneralArrangementCount 8 B phi : Real) := height

end LeanProofs.GowersSzemeredi
