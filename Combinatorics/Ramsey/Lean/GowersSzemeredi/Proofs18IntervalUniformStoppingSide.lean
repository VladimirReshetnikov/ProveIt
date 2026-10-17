import GowersSzemeredi.Proofs18IntervalUniformStopping
import GowersSzemeredi.Proofs18RelativeProgressionExistence

/-! Declarations of `Proofs18IntervalUniformStopping` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- Starts and nonnegative steps below L/4 produce four-term progressions
entirely inside the interval. Both parameters are recovered from the pair. -/
theorem finiteInterval_fourTermCount_floor {N L : Nat} [NeZero N] (hL : L ≤ N) :
    (L / 4) ^ 2 ≤ fourTermCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) := by
  exact finiteInterval_progressionCount_floor (k := 4) hL (by norm_num)

theorem finiteInterval_fourTermCount_lower {N L : Nat} [NeZero N]
    (hL : L ≤ N) (hLfour : 4 ≤ L) :
    (L : Real) ^ 2 / 64 ≤
      (fourTermCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) : Real) := by
  simpa only [progressionCount, fourTermCount, Nat.cast_ofNat, show (4 : Real) * 4 ^ 2 = 64 by norm_num] using
    (finiteInterval_progressionCount_lower (k := 4) hL (by norm_num) hLfour)

/-- Explicit relative-uniform stopping: when the modulus is at most eight
times the interval length, a small enough uniformity error guarantees a
nonconstant ordinary four-term progression. -/
theorem interval_relative_uniform_hasNatAP_four {N L : Nat} [NeZero N] [Fact N.Prime]
    (hL : 2 * L < N) (hLfour : 4 ≤ L) (hNL : N ≤ 8 * L)
    (B : Finset (Fin L)) (delta alpha : Real)
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hsmall : 4 * alpha ^ (1 / 8 : Real) ≤ delta ^ 4 / 8192)
    (hlarge : 8192 < delta ^ 4 * N)
    (hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B delta)) alpha 2) :
    HasNatAP (B.image Fin.val) 4 := by
  have hLN : L ≤ N := by omega
  let S := finiteIntervalImage N (Finset.univ : Finset (Fin L))
  have hcount : (N : Real) ^ 2 / 4096 ≤ (fourTermCount S : Real) := by
    have hnlr : (N : Real) ≤ 8 * L := by exact_mod_cast hNL
    have hs : (N : Real) ^ 2 ≤ (8 * (L : Real)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hnlr
    have hc := finiteInterval_fourTermCount_lower hLN hLfour
    dsimp [S]
    nlinarith
  apply finiteIntervalImage_hasNatAP B hL
  apply relative_uniform_hasModAP_four (by omega) (finiteIntervalImage N B) S delta alpha
    (finiteIntervalImage_subset B) hδ hδone hα
    (by simpa only [S, relativeBalanced_finiteIntervalImage hLN] using hu)
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have he := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (N : Real))
  have hl := mul_lt_mul_of_pos_right hlarge hNpos
  have hc := mul_le_mul_of_nonneg_left hcount (pow_nonneg hδ 4)
  nlinarith

end LeanProofs.GowersSzemeredi
