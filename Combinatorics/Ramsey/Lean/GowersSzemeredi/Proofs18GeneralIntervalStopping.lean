import GowersSzemeredi.Proofs18GeneralProgressionExistence
import GowersSzemeredi.Proofs18IntervalUniformStopping

/-! Relative-uniform stopping on integer intervals at every progression
length. The explicit constants specialize to the existing four-term bound.

`intervalUniformityParameter_le_one` is in
`Proofs18GeneralIntervalStoppingSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- At arbitrary length k, sufficiently small relative-uniformity error
forces an ordinary progression in the original interval. -/
theorem interval_relative_uniform_hasNatAP {N L k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (hL : 2 * L < N) (hkL : k ≤ L) (hNL : N ≤ 8 * L)
    (B : Finset (Fin L)) (delta alpha : Real)
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hsmall : k * alpha ^ (1 / (2 : Real) ^ (k - 1)) ≤ delta ^ k / (512 * (k : Real) ^ 2))
    (hlarge : 512 * (k : Real) ^ 2 < delta ^ k * N)
    (hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B delta)) alpha (k - 2)) :
    HasNatAP (B.image Fin.val) k := by
  have hLN : L ≤ N := by omega
  let S := finiteIntervalImage N (Finset.univ : Finset (Fin L))
  have hcount : (N : Real) ^ 2 / (256 * (k : Real) ^ 2) ≤ (progressionCount S k : Real) := by
    have hnlr : (N : Real) ≤ 8 * L := by exact_mod_cast hNL
    have hs := (sq_le_sq₀ (by positivity : (0 : Real) ≤ N) (by positivity : (0 : Real) ≤ 8 * L)).mpr hnlr
    have hc := finiteInterval_progressionCount_lower hLN (by omega : 0 < k) hkL
    have hc' := (div_le_iff₀ (by positivity : (0 : Real) < 4 * (k : Real) ^ 2)).mp hc
    apply (div_le_iff₀ (by positivity : (0 : Real) < 256 * (k : Real) ^ 2)).mpr
    change (N : Real) ^ 2 ≤ (progressionCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) k : Real) * _
    nlinarith
  apply finiteIntervalImage_hasNatAP B hL
  apply relative_uniform_hasModAP hk (by omega) (finiteIntervalImage N B) S delta alpha
    (finiteIntervalImage_subset B) hδ hδone hα
    (by simpa only [S, relativeBalanced_finiteIntervalImage hLN] using hu)
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hden : (0 : Real) < 512 * (k : Real) ^ 2 := by positivity
  have he := mul_le_mul_of_nonneg_right ((le_div_iff₀ hden).mp hsmall) (sq_nonneg (N : Real))
  have hl := mul_lt_mul_of_pos_right hlarge hNpos
  have hc := mul_le_mul_of_nonneg_left
    ((div_le_iff₀ (by positivity : (0 : Real) < 256 * (k : Real) ^ 2)).mp hcount)
    (pow_nonneg hδ k)
  apply (mul_lt_mul_iff_left₀ hden).mp
  nlinarith

/-- An explicit uniformity parameter meeting the general interval count
budget. At k=4 this is the existing quadratic stopping parameter. -/
def intervalUniformityParameter (delta : Real) (k : Nat) : Real :=
  (delta ^ k / (512 * (k : Real) ^ 3)) ^ ((2 : Nat) ^ (k - 1))

theorem intervalUniformityParameter_pos {delta : Real} {k : Nat}
    (hδ : 0 < delta) (hk : 0 < k) : 0 < intervalUniformityParameter delta k := by
  unfold intervalUniformityParameter
  positivity

theorem intervalUniformityParameter_count_error {delta : Real} {k : Nat}
    (hδ : 0 ≤ delta) (hk : 0 < k) :
    k * intervalUniformityParameter delta k ^ (1 / (2 : Real) ^ (k - 1)) =
      delta ^ k / (512 * (k : Real) ^ 2) := by
  have hroot : intervalUniformityParameter delta k ^ (1 / (2 : Real) ^ (k - 1)) =
      delta ^ k / (512 * (k : Real) ^ 3) := by
    simpa only [intervalUniformityParameter, one_div, Nat.cast_pow, Nat.cast_ofNat] using
      (Real.pow_rpow_inv_natCast (show 0 ≤ delta ^ k / (512 * (k : Real) ^ 3) by positivity)
        (by positivity : (2 : Nat) ^ (k - 1) ≠ 0))
  rw [hroot]
  field_simp

end LeanProofs.GowersSzemeredi
