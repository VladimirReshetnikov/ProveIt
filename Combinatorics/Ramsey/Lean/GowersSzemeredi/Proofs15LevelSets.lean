import GowersSzemeredi.Sections14_15
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fin.Tuple.Finset
import GowersSzemeredi.Proofs00Basics

/-!
# Multiaffine level sets in Gowers's Section 15

This module proves the sharp fibre bound in Lemma 15.3.  The key auxiliary
result is the familiar grid lemma: a nonzero polynomial which is affine in
each of `k` variables is nonzero at at least `(q - 1)^k` points of a field
with `q` elements.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def multiaffineEval {R : Type*} [CommSemiring R] {k : Nat}
    (c : (Fin k → Bool) → R) (x : Fin k → R) : R :=
  ∑ e : Fin k → Bool, c e * ∏ i, if e i = true then x i else 1

private lemma multiaffineEval_succ {R : Type*} [CommSemiring R] {k : Nat}
    (c : (Fin (k + 1) → Bool) → R) (x : Fin (k + 1) → R) :
    multiaffineEval c x =
      multiaffineEval (fun e => c (Fin.cons false e)) (Fin.tail x) +
        x 0 * multiaffineEval (fun e => c (Fin.cons true e)) (Fin.tail x) := by
  rw [multiaffineEval, ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, add_comm]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail,
    multiaffineEval, Bool.false_eq_true, if_false, if_true, one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun u _ => mul_left_comm _ _ _

private lemma countWhere_pi_succ {R : Type*} [Fintype R] {k : Nat}
    (P : (Fin (k + 1) → R) → Prop) [DecidablePred P] :
    countWhere P = ∑ y : Fin k → R, countWhere fun t : R => P (Fin.cons t y) := by
  rw [feature_countWhere_equiv ((Equiv.prodComm _ _).trans (Fin.consEquiv fun _ => R)) P]
  exact context_countWhere_prod fun y t => P (Fin.cons t y)

private lemma countWhere_affine_ne_zero {R : Type*} [Fintype R]
    [Field R] [DecidableEq R] (a b : R) (hb : b ≠ 0) :
    countWhere (fun t : R => a + t * b ≠ 0) = Fintype.card R - 1 := by
  let root : R := -a / b
  have hroot (t : R) : a + t * b = 0 ↔ t = root := by
    constructor
    · intro h
      apply (eq_div_iff hb).2
      linear_combination h
    · intro h
      have hmul := (eq_div_iff hb).1 h
      linear_combination hmul
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  have hfilter :
      (Finset.univ.filter fun t : R => a + t * b ≠ 0) = Finset.univ.erase root := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [ne_eq, hroot]
    simp
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ root), Finset.card_univ]

private theorem multiaffine_nonzero_count_lower {R : Type*} [Fintype R]
    [Field R] [DecidableEq R] :
    ∀ (k : Nat) (c : (Fin k → Bool) → R),
      (∃ x, multiaffineEval c x ≠ 0) →
      (Fintype.card R - 1) ^ k ≤
        countWhere fun x : Fin k → R => multiaffineEval c x ≠ 0 := by
  intro k
  induction k with
  | zero =>
      rintro c ⟨x, hx⟩
      unfold countWhere
      rw [Finset.filter_congr_decidable]
      exact Finset.one_le_card.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  | succ k ih =>
      intro c hnonzero
      have heval (t : R) (y : Fin k → R) : multiaffineEval c (Fin.cons t y) =
          multiaffineEval (fun e => c (Fin.cons false e)) y +
            t * multiaffineEval (fun e => c (Fin.cons true e)) y := by
        simpa only [Fin.tail_cons, Fin.cons_zero] using multiaffineEval_succ c (Fin.cons t y)
      -- a nonzero coefficient row `b` (the `true` row unless it vanishes) such that over each
      -- `y` where row `b` is nonzero, the fibre `t ↦ (t, y)` has `|R| - 1` nonzero points
      obtain ⟨b, hb, hfib⟩ : ∃ b : Bool,
          (∃ y, multiaffineEval (fun e => c (Fin.cons b e)) y ≠ 0) ∧
          ∀ y, multiaffineEval (fun e => c (Fin.cons b e)) y ≠ 0 →
            Fintype.card R - 1 ≤
              countWhere fun t : R => multiaffineEval c (Fin.cons t y) ≠ 0 := by
        by_cases hq : ∃ y, multiaffineEval (fun e => c (Fin.cons true e)) y ≠ 0
        · refine ⟨true, hq, fun y hy => ?_⟩
          have h := countWhere_affine_ne_zero
            (multiaffineEval (fun e => c (Fin.cons false e)) y) _ hy
          simpa only [heval] using h.ge
        push Not at hq
        refine ⟨false, ?_, fun y hy => ?_⟩
        · obtain ⟨x, hx⟩ := hnonzero
          refine ⟨Fin.tail x, fun h => hx ?_⟩
          rw [← Fin.cons_self_tail x, heval, hq, mul_zero, add_zero, h]
        · have hall (t : R) : multiaffineEval c (Fin.cons t y) ≠ 0 := by
            rw [heval, hq, mul_zero, add_zero]
            exact hy
          unfold countWhere
          rw [Finset.filter_congr_decidable]
          simp [hall]
      rw [pow_succ, countWhere_pi_succ]
      refine (Nat.mul_le_mul_right _ (ih _ hb)).trans ?_
      rw [countWhere_eq_sum_ite, Finset.sum_mul]
      exact Finset.sum_le_sum fun y _ => by
        split_ifs with hy
        · simpa using hfib y hy
        · simp

private def shiftedCoefficients {R : Type*} [Ring R] {k : Nat}
    (c : (Fin k → Bool) → R) (a : R) (e : Fin k → Bool) : R :=
  c e - if e = fun _ => false then a else 0

private lemma multiaffineEval_shifted {R : Type*} [CommRing R] {k : Nat}
    (c : (Fin k → Bool) → R) (a : R) (x : Fin k → R) :
    multiaffineEval (shiftedCoefficients c a) x = multiaffineEval c x - a := by
  unfold multiaffineEval shiftedCoefficients
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp

private lemma real_pow_sub_pred_pow_le (N k : Nat) (hN : 1 ≤ N) :
    (N : Real) ^ k - (N - 1 : Nat) ^ k ≤ k * (N : Real) ^ (k - 1) := by
  let x : Real := N
  let y : Real := (N - 1 : Nat)
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hyx : y ≤ x := by
    dsimp only [x, y]
    exact_mod_cast Nat.sub_le N 1
  have hpows : y ^ k ≤ x ^ k := pow_le_pow_left₀ hy0 hyx k
  have hcastSub : y = x - 1 := by
    simp only [x, y, Nat.cast_sub hN, Nat.cast_one]
  have habsDiff : |x - y| = 1 := by rw [hcastSub]; simp
  have habsX : |x| = x := abs_of_nonneg hx0
  have habsY : |y| = y := abs_of_nonneg hy0
  have hmax : max |x| |y| = x := by rw [habsX, habsY, max_eq_left hyx]
  have hbound := abs_pow_sub_pow_le (a := x) (b := y) (n := k)
  rw [abs_of_nonneg (sub_nonneg.mpr hpows), habsDiff, hmax, one_mul] at hbound
  simpa only [x, y] using hbound

/-- Lemma 15.3: a nonconstant multiaffine polynomial over the prime field
has at most `N^k - (N-1)^k` points in any one fibre. -/
theorem lemma_15_3_holds : lemma_15_3 := by
  rintro N k _ hprime mu a ⟨c, hc⟩ hnconstant
  haveI := Fact.mk hprime
  -- `mu - a` is multiaffine with the shifted coefficients, and not identically zero
  have heval (x : Point N k) : multiaffineEval (shiftedCoefficients c a) x = mu x - a := by
    rw [multiaffineEval_shifted, hc x, multiaffineEval]
  have hgrid : (N - 1) ^ k ≤ countWhere fun x : Point N k => mu x ≠ a := by
    simpa only [heval, sub_ne_zero, ZMod.card] using
      multiaffine_nonzero_count_lower k (shiftedCoefficients c a) (by
        by_contra! hzero
        exact hnconstant ⟨a, fun x => sub_eq_zero.mp ((heval x).symm.trans (hzero x))⟩)
  -- the fibre and its complement partition `Point N k`
  have hpartition : countWhere (fun y : Point N k => mu y = a) +
      countWhere (fun y : Point N k => mu y ≠ a) = N ^ k := by
    rw [countWhere_eq_sum_ite, countWhere_eq_sum_ite, ← Finset.sum_add_distrib]
    simp [ite_add_ite, Point, ZMod.card]
  refine ⟨?_, real_pow_sub_pred_pow_le N k hprime.one_le⟩
  rw [le_sub_iff_add_le]
  exact_mod_cast (show countWhere (fun y : Point N k => mu y = a) + (N - 1) ^ k ≤ N ^ k by omega)

end LeanProofs.GowersSzemeredi
