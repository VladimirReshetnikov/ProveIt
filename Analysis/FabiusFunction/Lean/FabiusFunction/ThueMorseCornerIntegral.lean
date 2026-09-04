import FabiusFunction.ThueMorseSymmetricDifference
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Fintype.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local integral formula for symmetric Thue--Morse corners

For half-steps `a 0, ..., a (N - 1)`, the product of symmetric differences
is the integral of the `N`-th derivative over the centered box

`[-a 0, a 0] × ... × [-a (N - 1), a (N - 1)]`.

The regularity hypothesis is deliberately local.  The function need only be
`C^N` on an open order-connected set containing the full symmetric segment
from `x - ∑ i < N, a i` to `x + ∑ i < N, a i`.  Thus the result matches the
locality of the continuous Thue--Morse corner theorem and does not replace it
by a global `ContDiff` assumption.  Zero half-steps are allowed; the
manuscript's positive half-steps are a special case.

## Main declarations

* `centeredBoxIntegral` -- the recursive centered box integral;
* `centeredBoxIntegral_zero`, `centeredBoxIntegral_succ` -- its boundary and
  recursion equations;
* `symmetricMixedDifference_range_eq_centeredBoxIntegral` -- the exact local
  corner identity for the first `N` entries of a sequence of half-steps;
* `symmetricMixedDifference_univ_eq_centeredBoxIntegral` -- the same identity
  with the coordinates indexed by `Fin N`.
-/

set_option autoImplicit false

open Finset Set
open intervalIntegral

namespace Fabius

/-- The nested integral over a centered box with successive half-widths
`a 0, ..., a (N - 1)`.  The last coordinate is the outermost integral.
At depth zero this is evaluation at the center. -/
noncomputable def centeredBoxIntegral (a : ℕ → ℝ) :
    ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, g, x => g x
  | N + 1, g, x =>
      ∫ u in -a N..a N, centeredBoxIntegral a N g (x + u)

/-- The empty centered box integral is evaluation at its center. -/
@[simp] theorem centeredBoxIntegral_zero (a : ℕ → ℝ) (g : ℝ → ℝ)
    (x : ℝ) :
    centeredBoxIntegral a 0 g x = g x :=
  rfl

/-- Peeling the outermost coordinate of a centered box integral. -/
theorem centeredBoxIntegral_succ (a : ℕ → ℝ) (N : ℕ) (g : ℝ → ℝ)
    (x : ℝ) :
    centeredBoxIntegral a (N + 1) g x =
      ∫ u in -a N..a N, centeredBoxIntegral a N g (x + u) :=
  rfl

private theorem symmetricMixedDifference_eq_sum_powerset_mul
    {ι : Type*} (a : ι → ℝ) (s : Finset ι) (g : ℝ → ℝ) (x : ℝ) :
    symmetricMixedDifference a s g x =
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card *
        g (((∑ i ∈ s, a i) - 2 * ∑ i ∈ t, a i) + x) := by
  simpa only [vadd_eq_add, nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Nat.cast_ofNat] using
      (symmetricMixedDifference_eq_sum_powerset_smul a s g x)

private theorem symmetricMixedDifference_map
    {ι κ : Type*} (e : ι ↪ κ) (a : κ → ℝ) (s : Finset ι)
    (g : ℝ → ℝ) (x : ℝ) :
    symmetricMixedDifference (a ∘ e) s g x =
      symmetricMixedDifference a (s.map e) g x := by
  classical
  induction s using Finset.induction_on generalizing g x with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.map_insert,
        symmetricMixedDifference_insert (a ∘ e) s g x hi,
        symmetricMixedDifference_insert a (s.map e) g x
          (i := e i) (by simpa using hi)]
      simp only [Function.comp_apply]
      rw [ih, ih]

private theorem symmetricMixedDifference_insert_eq_integral_deriv
    (a : ℕ → ℝ) (s : Finset ℕ) (g : ℝ → ℝ) (x : ℝ) (i : ℕ)
    (hi : i ∉ s) (ha : ∀ j ∈ s, 0 ≤ a j) (hai : 0 ≤ a i)
    {I : Set ℝ} (hIopen : IsOpen I) (hIord : OrdConnected I)
    (hgd : DifferentiableOn ℝ g I) (hg' : ContinuousOn (deriv g) I)
    (hsegment :
      Set.Icc (x - ((∑ j ∈ s, a j) + a i))
          (x + ((∑ j ∈ s, a j) + a i)) ⊆ I) :
    symmetricMixedDifference a (insert i s) g x =
      ∫ u in -a i..a i,
        symmetricMixedDifference a s (deriv g) (x + u) := by
  classical
  have hcorner : ∀ t ∈ s.powerset,
      IntervalIntegrable
          (fun u => deriv g
            (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (x + u)))
          MeasureTheory.volume (-a i) (a i) ∧
        g (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (a i + x)) -
            g (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (-a i + x)) =
          ∫ u in -a i..a i,
            deriv g
              (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (x + u)) := by
    intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    let r : ℝ := ∑ j ∈ s, a j
    let q : ℝ := ∑ j ∈ t, a j
    let y : ℝ := r - 2 * q + x
    have hr : 0 ≤ r := by
      dsimp only [r]
      exact Finset.sum_nonneg fun j hj => ha j hj
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      exact Finset.sum_nonneg fun j hj => ha j (hts hj)
    have hqr : q ≤ r := by
      dsimp only [q, r]
      exact Finset.sum_le_sum_of_subset_of_nonneg hts
        (fun j hjs _ => ha j hjs)
    have hylo : y - a i ∈ I := by
      apply hsegment
      constructor <;> dsimp only [y, r, q] <;> linarith
    have hyhi : y + a i ∈ I := by
      apply hsegment
      constructor <;> dsimp only [y, r, q] <;> linarith
    have hysegment : Set.uIcc (y - a i) (y + a i) ⊆ I :=
      hIord.uIcc_subset hylo hyhi
    have hmap : Set.MapsTo (fun u : ℝ => y + u)
        (Set.uIcc (-a i) (a i)) I := by
      intro u hu
      apply hysegment
      rw [Set.uIcc_of_le (neg_le_self hai)] at hu
      rw [Set.uIcc_of_le (by linarith : y - a i ≤ y + a i)]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hderiv : ∀ u ∈ Set.uIcc (-a i) (a i),
        HasDerivAt (fun v : ℝ => g (y + v)) (deriv g (y + u)) u := by
      intro u hu
      have hyu : y + u ∈ I := hmap hu
      exact ((hgd _ hyu).differentiableAt
        (hIopen.mem_nhds hyu)).hasDerivAt.comp_const_add y u
    have hcont : ContinuousOn (fun u : ℝ => deriv g (y + u))
        (Set.uIcc (-a i) (a i)) :=
      hg'.comp (continuous_const.add continuous_id).continuousOn hmap
    have hint : IntervalIntegrable (fun u : ℝ => deriv g (y + u))
        MeasureTheory.volume (-a i) (a i) :=
      hcont.intervalIntegrable
    have hFTC :
        (∫ u in -a i..a i, deriv g (y + u)) =
          g (y + a i) - g (y - a i) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hleft :
        ((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (a i + x) =
          y + a i := by
      dsimp only [y, r, q]
      ring
    have hright :
        ((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (-a i + x) =
          y - a i := by
      dsimp only [y, r, q]
      ring
    have hintegrand (u : ℝ) :
        ((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (x + u) =
          y + u := by
      dsimp only [y, r, q]
      ring
    constructor
    · exact hint.congr fun u _ => by rw [hintegrand]
    · rw [hleft, hright, ← hFTC]
      exact intervalIntegral.integral_congr fun u _ => by rw [hintegrand]
  rw [symmetricMixedDifference_insert a s g x hi,
    symmetricMixedDifference_eq_sum_powerset_mul,
    symmetricMixedDifference_eq_sum_powerset_mul,
    ← Finset.sum_sub_distrib]
  calc
    (∑ t ∈ s.powerset,
        ((-1 : ℝ) ^ t.card *
            g (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (a i + x)) -
          (-1 : ℝ) ^ t.card *
            g (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (-a i + x)))) =
        ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card *
          (g (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (a i + x)) -
            g (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (-a i + x))) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card *
          (∫ u in -a i..a i,
            deriv g
              (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (x + u))) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(hcorner t ht).2]
    _ = ∑ t ∈ s.powerset,
          ∫ u in -a i..a i, (-1 : ℝ) ^ t.card *
            deriv g
              (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (x + u)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ u in -a i..a i,
          ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card *
            deriv g
              (((∑ j ∈ s, a j) - 2 * ∑ j ∈ t, a j) + (x + u)) := by
      rw [intervalIntegral.integral_finsetSum]
      intro t ht
      exact (hcorner t ht).1.const_mul _
    _ = ∫ u in -a i..a i,
          symmetricMixedDifference a s (deriv g) (x + u) := by
      exact intervalIntegral.integral_congr fun u _ => by
        rw [symmetricMixedDifference_eq_sum_powerset_mul]

/-- **Local continuous Thue--Morse corner identity.**  Let the first `N`
half-steps be nonnegative.  If `g` is `C^N` on an open order-connected set
containing the entire symmetric segment
`[x - ∑ i < N, a i, x + ∑ i < N, a i]`, then its symmetric mixed difference
is exactly the centered `N`-fold box integral of `iteratedDeriv N g`.

The hypotheses are local to that segment.  Zero half-steps, `N = 0`, and
intervals strictly larger than the segment are all included. -/
theorem symmetricMixedDifference_range_eq_centeredBoxIntegral
    (N : ℕ) (a : ℕ → ℝ) (g : ℝ → ℝ) (x : ℝ) {I : Set ℝ}
    (ha : ∀ i ∈ Finset.range N, 0 ≤ a i)
    (hIopen : IsOpen I) (hIord : OrdConnected I)
    (hg : ContDiffOn ℝ N g I)
    (hsegment :
      Set.Icc (x - ∑ i ∈ Finset.range N, a i)
          (x + ∑ i ∈ Finset.range N, a i) ⊆ I) :
    symmetricMixedDifference a (Finset.range N) g x =
      centeredBoxIntegral a N (iteratedDeriv N g) x := by
  induction N generalizing g x with
  | zero => simp
  | succ N ih =>
      have haN : 0 ≤ a N := ha N (by simp)
      have ha' : ∀ i ∈ Finset.range N, 0 ≤ a i := by
        intro i hi
        apply ha i
        simp only [Finset.mem_range] at hi ⊢
        omega
      have hsegment' :
          Set.Icc (x - ((∑ i ∈ Finset.range N, a i) + a N))
              (x + ((∑ i ∈ Finset.range N, a i) + a N)) ⊆ I := by
        simpa only [Finset.sum_range_succ] using hsegment
      have hg1 : ContDiffOn ℝ ((N : WithTop ℕ∞) + 1) g I := by
        have h := hg
        rwa [Nat.cast_succ] at h
      have hsplit := (contDiffOn_succ_iff_deriv_of_isOpen hIopen).mp hg1
      have hgd : DifferentiableOn ℝ g I := hsplit.1
      have hg' : ContDiffOn ℝ N (deriv g) I := hsplit.2.2
      calc
        symmetricMixedDifference a (Finset.range (N + 1)) g x =
            ∫ u in -a N..a N,
              symmetricMixedDifference a (Finset.range N) (deriv g) (x + u) := by
          rw [Finset.range_add_one]
          exact symmetricMixedDifference_insert_eq_integral_deriv
            a (Finset.range N) g x N (by simp) ha' haN hIopen hIord hgd
              hg'.continuousOn hsegment'
        _ = ∫ u in -a N..a N,
              centeredBoxIntegral a N (iteratedDeriv (N + 1) g) (x + u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [Set.uIcc_of_le (neg_le_self haN)] at hu
          have hlocal :
              Set.Icc ((x + u) - ∑ i ∈ Finset.range N, a i)
                  ((x + u) + ∑ i ∈ Finset.range N, a i) ⊆ I := by
            intro y hy
            apply hsegment'
            constructor <;> linarith [hu.1, hu.2, hy.1, hy.2]
          simpa only [iteratedDeriv_succ'] using
            (ih (deriv g) (x + u) ha' hg' hlocal)
        _ = centeredBoxIntegral a (N + 1) (iteratedDeriv (N + 1) g) x :=
          (centeredBoxIntegral_succ a N (iteratedDeriv (N + 1) g) x).symm

/-- The local corner identity with its coordinates indexed by `Fin N`.
This is a reindexing of the range form through `Fin.valEmbedding`; its
hypotheses and centered-box integral are unchanged. -/
theorem symmetricMixedDifference_univ_eq_centeredBoxIntegral
    (N : ℕ) (a : ℕ → ℝ) (g : ℝ → ℝ) (x : ℝ) {I : Set ℝ}
    (ha : ∀ i ∈ Finset.range N, 0 ≤ a i)
    (hIopen : IsOpen I) (hIord : OrdConnected I)
    (hg : ContDiffOn ℝ N g I)
    (hsegment :
      Set.Icc (x - ∑ i ∈ Finset.range N, a i)
          (x + ∑ i ∈ Finset.range N, a i) ⊆ I) :
    symmetricMixedDifference (fun i : Fin N => a i) Finset.univ g x =
      centeredBoxIntegral a N (iteratedDeriv N g) x := by
  calc
    symmetricMixedDifference (fun i : Fin N => a i) Finset.univ g x =
        symmetricMixedDifference a (Finset.range N) g x := by
      change symmetricMixedDifference (a ∘ Fin.valEmbedding)
          (Finset.univ : Finset (Fin N)) g x =
        symmetricMixedDifference a (Finset.range N) g x
      simpa only [Fin.map_valEmbedding_univ, Nat.Iio_eq_range] using
          (symmetricMixedDifference_map Fin.valEmbedding a
            (Finset.univ : Finset (Fin N)) g x)
    _ = centeredBoxIntegral a N (iteratedDeriv N g) x :=
      symmetricMixedDifference_range_eq_centeredBoxIntegral
        N a g x ha hIopen hIord hg hsegment

end Fabius
