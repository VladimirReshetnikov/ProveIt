import FabiusFunction.Differential
import FabiusFunction.DyadicClosedForm
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The signed global Fabius extension

This module proves that the Thue–Morse translate series defining
`extendedFabius` is locally finite.  It then derives the global differential
equation and the closed formulas for all iterated derivatives of both the
signed extension and Rvachev's compactly supported function.  A cell-coordinate
form of the locally finite series records its exact values at every even and
odd nonnegative integer knot.
-/

open scoped BigOperators ContDiff
open Finset Set

namespace Fabius

set_option autoImplicit false

private lemma extendedSummand_eq_zero_of_lt_two_mul
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} {n : ℕ}
    (hx : x < 2 * (n : ℝ)) :
    (-1 : ℝ) ^ binaryWeight n * rvachevUp F (x - 2 * (n : ℝ) - 1) = 0 := by
  rw [rvachevUp_eq_zero_of_le_neg_one F hF (by linarith)]
  ring

/-- At each point, only finitely many translates in the signed extension are nonzero. -/
lemma extendedFabius_summable (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ binaryWeight n *
      rvachevUp F (x - 2 * (n : ℝ) - 1)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  apply summable_of_ne_finset_zero (s := range N)
  intro n hn
  have hnN : N ≤ n := by simpa using hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hn0 : (0 : ℝ) ≤ n := by positivity
  apply extendedSummand_eq_zero_of_lt_two_mul F hF
  nlinarith

/-- On each interval `[2b, 2b+2]`, the global series has just one nonzero translate. -/
theorem extendedFabius_eq_single_translate (F : BoundedFabius)
    (hF : IsFabius F) (b : ℕ) {x : ℝ}
    (hlo : 2 * (b : ℝ) ≤ x) (hhi : x ≤ 2 * (b : ℝ) + 2) :
    extendedFabius F x =
      (-1 : ℝ) ^ binaryWeight b * rvachevUp F (x - 2 * (b : ℝ) - 1) := by
  unfold extendedFabius
  rw [tsum_eq_single b]
  intro m hmb
  rcases lt_or_gt_of_ne hmb with hmlt | hmlt
  · have hmle : m + 1 ≤ b := by omega
    have hmleR : (m : ℝ) + 1 ≤ b := by exact_mod_cast hmle
    rw [rvachevUp_eq_zero_of_one_le F hF (by nlinarith)]
    ring
  · have hmle : b + 1 ≤ m := by omega
    have hmleR : (b : ℝ) + 1 ≤ m := by exact_mod_cast hmle
    rw [rvachevUp_eq_zero_of_le_neg_one F hF (by nlinarith)]
    ring

/-- Cell-coordinate form of `extendedFabius_eq_single_translate`.  On the
`b`-th length-two cell, writing the argument as `2b + t` with `0 ≤ t ≤ 2`
removes all ambient offsets from the surviving Rvachev translate. -/
theorem extendedFabius_two_mul_add (F : BoundedFabius) (hF : IsFabius F)
    (b : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    extendedFabius F (2 * (b : ℝ) + t) =
      (-1 : ℝ) ^ binaryWeight b * rvachevUp F (t - 1) := by
  have h := extendedFabius_eq_single_translate F hF b
    (x := 2 * (b : ℝ) + t) (by linarith [ht.1]) (by linarith [ht.2])
  convert h using 1
  ring_nf

/-- The signed extension vanishes at every nonnegative even integer knot. -/
theorem extendedFabius_two_mul_nat (F : BoundedFabius) (hF : IsFabius F)
    (b : ℕ) : extendedFabius F (2 * (b : ℝ)) = 0 := by
  simpa [rvachevUp_neg_one F hF] using
    extendedFabius_two_mul_add F hF b 0 (by constructor <;> norm_num)

/-- At the midpoint of the `b`-th cell, the signed extension is exactly the
corresponding Thue--Morse sign. -/
theorem extendedFabius_two_mul_nat_add_one
    (F : BoundedFabius) (hF : IsFabius F) (b : ℕ) :
    extendedFabius F (2 * (b : ℝ) + 1) = (-1 : ℝ) ^ binaryWeight b := by
  simpa [rvachevUp_zero F hF] using
    extendedFabius_two_mul_add F hF b 1 (by constructor <;> norm_num)

/-- The signed extension vanishes on nonpositive arguments. -/
theorem extendedFabius_eq_zero_of_nonpos (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ≤ 0) : extendedFabius F x = 0 := by
  unfold extendedFabius
  rw [tsum_eq_single 0]
  · norm_num [binaryWeight, rvachevUp]
    rw [if_pos (hx.trans (by norm_num))]
    exact hF.zero_of_nonpos _ hx
  · intro n hn
    have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnposReal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have harg : x - 2 * (n : ℝ) - 1 ≤ 0 := by linarith
    have hinside : x - 2 * (n : ℝ) - 1 + 1 ≤ 0 := by linarith
    rw [rvachevUp, if_pos harg, hF.zero_of_nonpos _ hinside]
    simp

/-- The bounded and signed versions agree on the unit interval. -/
theorem extendedFabius_eq_fabiusReal (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extendedFabius F x = fabiusReal F x := by
  unfold extendedFabius
  rw [tsum_eq_single 0]
  · norm_num [binaryWeight, rvachevUp, hx.2]
  · intro n hn
    have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnposReal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have harg : x - 2 * (n : ℝ) - 1 ≤ 0 := by
      linarith [hx.2]
    have hinside : x - 2 * (n : ℝ) - 1 + 1 ≤ 0 := by
      linarith [hx.2]
    rw [rvachevUp, if_pos harg, hF.zero_of_nonpos _ hinside]
    simp

/-- The signed extension vanishes at the origin. -/
@[simp] theorem extendedFabius_zero (F : BoundedFabius) (hF : IsFabius F) :
    extendedFabius F 0 = 0 :=
  extendedFabius_eq_zero_of_nonpos F hF le_rfl

/-- The signed extension retains the bounded normalization at one. -/
@[simp] theorem extendedFabius_one (F : BoundedFabius) (hF : IsFabius F) :
    extendedFabius F 1 = 1 := by
  rw [extendedFabius_eq_fabiusReal F hF (by constructor <;> norm_num),
    hF.one_of_one_le 1 le_rfl]

/-- On the unit interval, the signed extension inherits the reflection
symmetry of the bounded Fabius function. -/
theorem extendedFabius_one_sub (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extendedFabius F (1 - x) = 1 - extendedFabius F x := by
  rw [extendedFabius_eq_fabiusReal F hF
      ⟨by linarith [hx.2], by linarith [hx.1]⟩,
    extendedFabius_eq_fabiusReal F hF hx]
  exact hF.symmetry x hx

/-- The signed global extension is infinitely differentiable. -/
theorem extendedFabius_contDiff (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℝ ∞ (extendedFabius F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (x + 1)
  have hsmooth : ContDiff ℝ ∞ (fun y : ℝ =>
      ∑ n ∈ range N, (-1 : ℝ) ^ binaryWeight n *
        rvachevUp F (y - 2 * (n : ℝ) - 1)) := by
    apply ContDiff.sum
    intro n hn
    exact contDiff_const.mul ((rvachev_contDiff F hF).comp
      ((contDiff_id.sub contDiff_const).sub contDiff_const))
  apply hsmooth.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (show x < x + 1 by linarith)] with y hy
  change y < x + 1 at hy
  unfold extendedFabius
  rw [tsum_eq_sum]
  intro n hn
  have hnN : N ≤ n := by simpa using hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hn0 : (0 : ℝ) ≤ n := by positivity
  apply extendedSummand_eq_zero_of_lt_two_mul F hF
  nlinarith

private lemma extendedFabius_refinement_tsum
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    (∑' n : ℕ, (-1 : ℝ) ^ binaryWeight n *
      (rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) -
        rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1))) =
      extendedFabius F (2 * x) := by
  let f : ℕ → ℝ := fun m => (-1 : ℝ) ^ binaryWeight m *
    rvachevUp F (2 * x - 2 * (m : ℝ) - 1)
  have hs : Summable f := by
    simpa [f] using extendedFabius_summable F hF (2 * x)
  have heven : Summable (fun n : ℕ => f (2 * n)) :=
    hs.comp_injective (mul_right_injective₀ (by omega : (2 : ℕ) ≠ 0))
  have hodd : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hs.comp_injective ((add_left_injective 1).comp
      (mul_right_injective₀ (by omega : (2 : ℕ) ≠ 0)))
  calc
    (∑' n : ℕ, (-1 : ℝ) ^ binaryWeight n *
        (rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) -
          rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1))) =
        ∑' n : ℕ, (f (2 * n) + f (2 * n + 1)) := by
          apply tsum_congr
          intro n
          simp only [f, binaryWeight_two_mul, binaryWeight_two_mul_add_one, pow_succ]
          push_cast
          ring_nf
    _ = (∑' n : ℕ, f (2 * n)) + ∑' n : ℕ, f (2 * n + 1) :=
      heven.tsum_add hodd
    _ = ∑' n : ℕ, f n := tsum_even_add_odd heven hodd
    _ = extendedFabius F (2 * x) := by rfl

private lemma deriv_extendedSummand
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => (-1 : ℝ) ^ binaryWeight n *
      rvachevUp F (y - 2 * (n : ℝ) - 1)) x =
      (-1 : ℝ) ^ binaryWeight n * 2 *
        (rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) -
          rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1)) := by
  rw [deriv_const_mul_field]
  have hfun : (fun y : ℝ => rvachevUp F (y - 2 * (n : ℝ) - 1)) =
      fun y : ℝ => rvachevUp F (y - (2 * (n : ℝ) + 1)) := by
    funext y
    congr 1
    ring
  rw [hfun, deriv_comp_sub_const,
    (rvachev_hasDerivAt F hF (x - (2 * (n : ℝ) + 1))).deriv]
  ring_nf

/-- The signed extension satisfies `F'(x) = 2 F(2x)` on all of `ℝ`. -/
theorem extendedFabius_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (extendedFabius F) (2 * extendedFabius F (2 * x)) x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (x + 1)
  have hevent : extendedFabius F =ᶠ[nhds x]
      (∑ n ∈ range N, fun z : ℝ => (-1 : ℝ) ^ binaryWeight n *
        rvachevUp F (z - 2 * (n : ℝ) - 1)) := by
    filter_upwards [Iio_mem_nhds (show x < x + 1 by linarith)] with y hy
    change y < x + 1 at hy
    unfold extendedFabius
    rw [tsum_eq_sum (s := range N)]
    · simp only [Finset.sum_apply]
    · intro n hn
      have hnN : N ≤ n := by simpa using hn
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hnN
      have hn0 : (0 : ℝ) ≤ n := by positivity
      apply extendedSummand_eq_zero_of_lt_two_mul F hF
      nlinarith
  have htermDiff : ∀ n ∈ range N, DifferentiableAt ℝ
      (fun y : ℝ => (-1 : ℝ) ^ binaryWeight n *
        rvachevUp F (y - 2 * (n : ℝ) - 1)) x := by
    intro n hn
    exact (contDiff_const.mul ((rvachev_contDiff F hF).comp
      ((contDiff_id.sub contDiff_const).sub contDiff_const))).differentiable
        (by simp) x
  have hderivFinite : deriv (extendedFabius F) x =
      ∑ n ∈ range N, (-1 : ℝ) ^ binaryWeight n * 2 *
        (rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) -
          rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1)) := by
    calc
      deriv (extendedFabius F) x =
          deriv (∑ n ∈ range N, fun y : ℝ => (-1 : ℝ) ^ binaryWeight n *
            rvachevUp F (y - 2 * (n : ℝ) - 1)) x := hevent.deriv_eq
      _ = ∑ n ∈ range N, deriv (fun y : ℝ => (-1 : ℝ) ^ binaryWeight n *
            rvachevUp F (y - 2 * (n : ℝ) - 1)) x := deriv_sum htermDiff
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        exact deriv_extendedSummand F hF n x
  have hsum : (∑ n ∈ range N, (-1 : ℝ) ^ binaryWeight n *
      (rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) -
        rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1))) =
      ∑' n : ℕ, (-1 : ℝ) ^ binaryWeight n *
      (rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) -
        rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1)) := by
    rw [tsum_eq_sum]
    intro n hn
    have hnN : N ≤ n := by simpa using hn
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hxlt : x < 2 * (n : ℝ) := by nlinarith
    have hleft : rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) = 0 := by
      apply rvachevUp_eq_zero_of_le_neg_one F hF
      nlinarith
    have hright : rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1) = 0 := by
      apply rvachevUp_eq_zero_of_le_neg_one F hF
      nlinarith
    rw [hleft, hright]
    ring
  have hcoeff : (∑ n ∈ range N, (-1 : ℝ) ^ binaryWeight n * 2 *
      (rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) -
        rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1))) =
      2 * extendedFabius F (2 * x) := by
    calc
      _ = 2 * (∑ n ∈ range N, (-1 : ℝ) ^ binaryWeight n *
          (rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) + 1) -
            rvachevUp F (2 * (x - 2 * (n : ℝ) - 1) - 1))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n hn
              ring
      _ = 2 * extendedFabius F (2 * x) := by
        rw [hsum, extendedFabius_refinement_tsum F hF x]
  have hderivValue : deriv (extendedFabius F) x = 2 * extendedFabius F (2 * x) :=
    hderivFinite.trans hcoeff
  have hd := (extendedFabius_contDiff F hF).differentiable (by simp) x
  rw [← hderivValue]
  exact hd.hasDerivAt

/-- Pointwise derivative form of the signed extension's refinement equation. -/
theorem deriv_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    deriv (extendedFabius F) x = 2 * extendedFabius F (2 * x) :=
  (extendedFabius_hasDerivAt F hF x).deriv

/-- Equation (3): every iterated derivative is a rescaled global Fabius value. -/
theorem iteratedDeriv_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (extendedFabius F) x =
      2 ^ (k + 1).choose 2 * extendedFabius F (2 ^ k * x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (extendedFabius F) = fun y : ℝ =>
          2 ^ (k + 1).choose 2 * extendedFabius F (2 ^ k * y) := by
        funext y
        exact ih y
      rw [hfun, deriv_const_mul_field, deriv_comp_mul_left,
        (extendedFabius_hasDerivAt F hF (2 ^ k * x)).deriv]
      have hchoose : (k + 2).choose 2 = (k + 1).choose 2 + (k + 1) := by
        rw [show k + 2 = (k + 1) + 1 by omega,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
      rw [show k + 1 + 1 = k + 2 by omega, hchoose, pow_add]
      ring_nf

/-- On the first block the signed extension is literally the translate of
Rvachev's compactly supported function: `extendedFabius F (x + 1) = up F x`
for every `x ≤ 1`.

This is the `b = 0` case of `extendedFabius_eq_single_translate` with the
sign `(-1) ^ binaryWeight 0 = 1` and the offset `2 * 0` already discharged.
It is the entry point for the Rvachev bridge of equation (32), for the
nowhere-analyticity transfer, and for the translated Legendre series, so it
is stated publicly rather than kept private to this module. -/
theorem extendedFabius_add_one_eq_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ≤ 1) :
    extendedFabius F (x + 1) = rvachevUp F x := by
  unfold extendedFabius
  rw [tsum_eq_single 0]
  · norm_num [binaryWeight]
  · intro n hn
    have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    rw [rvachevUp_eq_zero_of_le_neg_one F hF (by
      have : x + 1 - 2 * (n : ℝ) - 1 ≤ -1 := by linarith
      exact this)]
    ring

/-- Shifted form of `extendedFabius_add_one_eq_rvachevUp`: on `(-∞, 2]` the
signed extension is the single translate `up (y - 1)`.

No lower bound on `y` is needed: for `y ≤ 0` both sides vanish, since
`y - 1 ≤ -1` puts the argument outside the support of `up`.  Downstream
arguments that instantiate the `b = 0` block of
`extendedFabius_eq_single_translate` always have `y ≤ 2` in context, so this
is the shape they should use. -/
theorem extendedFabius_eq_rvachevUp_sub_one
    (F : BoundedFabius) (hF : IsFabius F) {y : ℝ} (hy : y ≤ 2) :
    extendedFabius F y = rvachevUp F (y - 1) := by
  have h := extendedFabius_add_one_eq_rvachevUp F hF (x := y - 1) (by linarith)
  rw [show y - 1 + 1 = y by ring] at h
  exact h

/-- The iterated derivatives of Rvachev's function are rescaled global Fabius values. -/
theorem iteratedDeriv_rvachev
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x : ℝ)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    iteratedDeriv n (rvachevUp F) x =
      2 ^ (n + 1).choose 2 * extendedFabius F (2 ^ n * (x + 1)) := by
  induction n generalizing x with
  | zero =>
      simpa using (extendedFabius_add_one_eq_rvachevUp F hF hx.2).symm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      let A : ℝ → ℝ := iteratedDeriv n (rvachevUp F)
      let B : ℝ → ℝ := fun y =>
        2 ^ (n + 1).choose 2 * extendedFabius F (2 ^ n * (y + 1))
      have heqOn : Set.EqOn A B (Icc (-1 : ℝ) 1) := by
        intro y hy
        exact ih y hy
      have hAdiff : Differentiable ℝ A := by
        apply (rvachev_contDiff F hF).differentiable_iteratedDeriv n
        exact WithTop.coe_lt_coe.mpr (ENat.coe_lt_top n)
      have hBdiff : Differentiable ℝ B := by
        dsimp [B]
        have hc : ContDiff ℝ ∞ (fun y : ℝ =>
            2 ^ (n + 1).choose 2 * extendedFabius F (2 ^ n * (y + 1))) :=
          contDiff_const.mul ((extendedFabius_contDiff F hF).comp
            (contDiff_const.mul (contDiff_id.add contDiff_const)))
        exact hc.differentiable (by norm_num)
      have hud : UniqueDiffOn ℝ (Icc (-1 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
      have hderivEq : deriv A x = deriv B x := by
        calc
          deriv A x = derivWithin A (Icc (-1 : ℝ) 1) x :=
            (hAdiff.differentiableAt.derivWithin (hud x hx)).symm
          _ = derivWithin B (Icc (-1 : ℝ) 1) x := derivWithin_congr heqOn (heqOn hx)
          _ = deriv B x := hBdiff.differentiableAt.derivWithin (hud x hx)
      rw [hderivEq]
      dsimp [B]
      rw [deriv_const_mul_field]
      have hargfun : (fun y : ℝ => extendedFabius F (2 ^ n * (y + 1))) =
          fun y : ℝ => (fun z : ℝ => extendedFabius F (z + 2 ^ n)) (2 ^ n * y) := by
        funext y
        congr 1
        ring
      rw [hargfun]
      have hmul :
          deriv (fun y : ℝ => (fun z : ℝ => extendedFabius F (z + 2 ^ n)) (2 ^ n * y)) x =
            2 ^ n * deriv (fun z : ℝ => extendedFabius F (z + 2 ^ n)) (2 ^ n * x) := by
        simpa only [smul_eq_mul] using
          (deriv_comp_mul_left (2 ^ n : ℝ)
            (fun z : ℝ => extendedFabius F (z + 2 ^ n)) x)
      rw [hmul, deriv_comp_add_const,
        (extendedFabius_hasDerivAt F hF (2 ^ n * x + 2 ^ n)).deriv]
      have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
      rw [show n + 1 + 1 = n + 2 by omega, hchoose, pow_add]
      ring_nf

end Fabius
