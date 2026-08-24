import GowersSzemeredi.Proofs03Minkowski
import GowersSzemeredi.Proofs03Cubes

/-!
# Uniform sets have few additive cubes

This module proves Lemma 3.10 from Gowers's paper.  The proof records the
exact unnormalised Gowers norm of an indicator, a balanced function, and a
constant, then applies the dimension-free form of Minkowski's inequality.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma gowersNorm_pow {N d : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    (gowersNorm d f) ^ ((2 : Nat) ^ d) =
      ‖∑ x : Point N d, ∑ s : ZMod N, cubeDifference f x s‖ := by
  unfold gowersNorm
  simpa [one_div] using
    (Real.rpow_inv_natCast_pow (norm_nonneg _)
      (by positivity : (2 : Nat) ^ d ≠ 0))

private lemma sum_cubeDifference_const {N d : Nat} [NeZero N]
    (c : Real) :
    (∑ x : Point N d, ∑ s : ZMod N,
        cubeDifference (fun _ => (c : Complex)) x s) =
      ((c ^ ((2 : Nat) ^ d) * (N : Real) ^ (d + 1) : Real) : Complex) := by
  rw [← constant_cubeForm_eq_sum_cubeDifference]
  have hparity (e : Fin d → Bool) :
      parityConj e (c : Complex) = (c : Complex) := by
    unfold parityConj
    split <;> simp
  unfold cubeForm
  simp_rw [hparity]
  simp only [prod_const, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, sum_const, card_univ, nsmul_eq_mul,
    ZMod.card, Point, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  rw [pow_succ]
  push_cast
  ring

private lemma gowersNorm_indicator_pow {N d : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (gowersNorm d (indicator A)) ^ ((2 : Nat) ^ d) =
      (cubeCount (d := d) A : Real) := by
  rw [gowersNorm_pow, sum_cubeDifference_indicator_eq_cubeCount]
  simp

private lemma gowersNorm_const_pow {N d : Nat} [NeZero N]
    (c : Real) (hc : 0 ≤ c) :
    (gowersNorm d (fun _ : ZMod N => (c : Complex))) ^ ((2 : Nat) ^ d) =
      c ^ ((2 : Nat) ^ d) * (N : Real) ^ (d + 1) := by
  rw [gowersNorm_pow, sum_cubeDifference_const]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (pow_nonneg hc _) (by positivity)

private lemma gowersNorm_succ_pow {N n : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    (gowersNorm (n + 1) f) ^ ((2 : Nat) ^ (n + 1)) =
      ∑ a : Point N n,
        ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 := by
  rw [gowersNorm_pow, sum_cube_succ_eq_sum_norm_sq]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma cubeCount_zero' {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : cubeCount (d := 0) A = A.card := by
  have h := congrArg Complex.re
    (sum_cubeDifference_indicator_eq_cubeCount (d := 0) A)
  simpa [cubeDifference, iteratedDifference] using h.symm

/-- **Gowers, Lemma 3.10.** A set uniform in degree `d - 1` has at most
the stated number of `d`-dimensional additive cubes. -/
theorem lemma_3_10_holds : lemma_3_10 := by
  intro N d _ A alpha delta hcard hUniform
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hdeltaMul : 0 ≤ delta * (N : Real) := by
    rw [← hcard]
    exact Nat.cast_nonneg _
  have hdelta : 0 ≤ delta :=
    nonneg_of_mul_nonneg_left hdeltaMul hN
  have hUniform' := hUniform
  unfold UniformSetOfDegree UniformOfDegree at hUniform'
  have halphaMul : 0 ≤ alpha * (N : Real) ^ (d - 1 + 2) := by
    exact (Finset.sum_nonneg fun (a : Point N (d - 1)) _ => sq_nonneg
      ‖∑ s : ZMod N, cubeDifference (balanced A) a s‖).trans hUniform'
  have halpha : 0 ≤ alpha :=
    nonneg_of_mul_nonneg_left halphaMul (pow_pos hN _)
  cases d with
  | zero =>
      rw [cubeCount_zero']
      norm_num [Real.rpow_one]
      calc
        (A.card : Real) = delta * N := hcard
        _ ≤ (delta + alpha) * N := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right halpha) hN.le
  | succ n =>
      have hUniformSucc : UniformSetOfDegree A alpha n := by
        simpa using hUniform
      unfold UniformSetOfDegree UniformOfDegree at hUniformSucc
      let m : Nat := (2 : Nat) ^ (n + 1)
      let rootAlpha : Real := alpha ^ ((m : Real)⁻¹)
      let scale : Real :=
        (N : Real) ^ (((n + 2 : Nat) : Real) / (m : Real))
      have hm : m ≠ 0 := by
        simp [m]
      have hmReal : (m : Real) ≠ 0 := by exact_mod_cast hm
      have hrootAlpha : 0 ≤ rootAlpha :=
        Real.rpow_nonneg halpha _
      have hscale : 0 ≤ scale :=
        Real.rpow_nonneg hN.le _
      have hrootAlphaPow : rootAlpha ^ m = alpha := by
        dsimp [rootAlpha]
        exact Real.rpow_inv_natCast_pow halpha hm
      have hscalePow : scale ^ m = (N : Real) ^ (n + 2) := by
        dsimp [scale]
        calc
          ((N : Real) ^ (((n + 2 : Nat) : Real) / (m : Real))) ^ m =
              (N : Real) ^
                ((((n + 2 : Nat) : Real) / (m : Real)) * (m : Real)) :=
            (Real.rpow_mul_natCast hN.le _ m).symm
          _ = (N : Real) ^ (((n + 2 : Nat) : Real)) := by
            congr 1
            field_simp
          _ = (N : Real) ^ (n + 2) := Real.rpow_natCast _ _
      have hdensity : density A = delta := by
        unfold density
        apply (div_eq_iff hN.ne').2
        simpa [mul_comm] using hcard
      have hindicator :
          indicator A = balanced A +
            (fun _ : ZMod N => (delta : Complex)) := by
        funext x
        simp [balanced, hdensity]
      have hbalancedPow :
          (gowersNorm (n + 1) (balanced A)) ^ m =
            ∑ a : Point N n,
              ‖∑ s : ZMod N, cubeDifference (balanced A) a s‖ ^ 2 := by
        simpa [m] using gowersNorm_succ_pow (n := n) (balanced A)
      have hbalanced :
          gowersNorm (n + 1) (balanced A) ≤ rootAlpha * scale := by
        apply le_of_pow_le_pow_left₀ hm (mul_nonneg hrootAlpha hscale)
        calc
          (gowersNorm (n + 1) (balanced A)) ^ m =
              ∑ a : Point N n,
                ‖∑ s : ZMod N, cubeDifference (balanced A) a s‖ ^ 2 :=
            hbalancedPow
          _ ≤ alpha * (N : Real) ^ (n + 2) := by
            exact hUniformSucc
          _ = (rootAlpha * scale) ^ m := by
            rw [mul_pow, hrootAlphaPow, hscalePow]
      have hconstant :
          gowersNorm (n + 1)
              (fun _ : ZMod N => (delta : Complex)) ≤ delta * scale := by
        apply le_of_pow_le_pow_left₀ hm (mul_nonneg hdelta hscale)
        calc
          (gowersNorm (n + 1)
              (fun _ : ZMod N => (delta : Complex))) ^ m =
              delta ^ m * (N : Real) ^ (n + 2) := by
            simpa [m] using
              gowersNorm_const_pow (N := N) (d := n + 1) delta hdelta
          _ ≤ (delta * scale) ^ m := by
            rw [mul_pow, hscalePow]
      have hindicatorNorm :
          gowersNorm (n + 1) (indicator A) ≤
            (delta + rootAlpha) * scale := by
        calc
          gowersNorm (n + 1) (indicator A) =
              gowersNorm (n + 1)
                (balanced A + fun _ : ZMod N => (delta : Complex)) := by
            rw [hindicator]
          _ ≤ gowersNorm (n + 1) (balanced A) +
              gowersNorm (n + 1)
                (fun _ : ZMod N => (delta : Complex)) :=
            gowersNorm_add_le _ _
          _ ≤ rootAlpha * scale + delta * scale :=
            add_le_add hbalanced hconstant
          _ = (delta + rootAlpha) * scale := by ring
      calc
        (cubeCount (d := n + 1) A : Real) =
            (gowersNorm (n + 1) (indicator A)) ^ m := by
          simpa [m] using
            (gowersNorm_indicator_pow (N := N) (d := n + 1) A).symm
        _ ≤ ((delta + rootAlpha) * scale) ^ m :=
          pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _)
            hindicatorNorm m
        _ = (delta + rootAlpha) ^ m * (N : Real) ^ (n + 2) := by
          rw [mul_pow, hscalePow]
        _ =
            (delta + alpha ^ ((1 : Real) / (2 : Real) ^ (n + 1))) ^
                ((2 : Nat) ^ (n + 1)) *
              (N : Real) ^ (n + 2) := by
          simp only [m, rootAlpha, one_div, Nat.cast_pow, Nat.cast_ofNat]

end LeanProofs.GowersSzemeredi
