import GowersSzemeredi.Sections14_15
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fin.Tuple.Finset

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
  let e := Fin.consEquiv (fun _ : Fin (k + 1) => Bool)
  rw [multiaffineEval]
  calc
    (∑ u : Fin (k + 1) → Bool,
        c u * ∏ i, if u i = true then x i else 1) =
        ∑ p : Bool × (Fin k → Bool),
          c (e p) * ∏ i, if e p i = true then x i else 1 :=
      (e.sum_comp _).symm
    _ = ∑ b : Bool, ∑ u : Fin k → Bool,
          c (Fin.cons b u) * ∏ i,
            if (Fin.cons b u : Fin (k + 1) → Bool) i = true then x i else 1 := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro b
      apply Fintype.sum_congr
      intro u
      change (c (Fin.cons b u) * ∏ i,
        if (Fin.cons b u : Fin (k + 1) → Bool) i = true then x i else 1) = _
      rfl
    _ = multiaffineEval (fun u => c (Fin.cons false u)) (Fin.tail x) +
        x 0 * multiaffineEval (fun u => c (Fin.cons true u)) (Fin.tail x) := by
      simp only [Fintype.sum_bool, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.tail, multiaffineEval, Bool.false_eq_true, if_false, if_true]
      rw [Finset.mul_sum]
      rw [add_comm]
      congr 1 <;> simp only [one_mul, mul_assoc, mul_comm]

private lemma countWhere_eq_sum_ite {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    countWhere P = ∑ x : T, if P x then 1 else 0 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

private lemma countWhere_pi_succ {R : Type*} [Fintype R] {k : Nat}
    (P : (Fin (k + 1) → R) → Prop) [DecidablePred P] :
    countWhere P = ∑ y : Fin k → R, countWhere fun t : R => P (Fin.cons t y) := by
  classical
  simp_rw [countWhere_eq_sum_ite]
  let e := Fin.consEquiv (fun _ : Fin (k + 1) => R)
  calc
    (∑ x : Fin (k + 1) → R, if P x then 1 else 0) =
        ∑ p : R × (Fin k → R), if P (e p) then 1 else 0 :=
      (e.sum_comp _).symm
    _ = ∑ t : R, ∑ y : Fin k → R,
        if P (Fin.cons t y) then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro t
      apply Fintype.sum_congr
      intro y
      change (if P (Fin.cons t y) then 1 else 0) = _
      rfl
    _ = ∑ y : Fin k → R, ∑ t : R,
        if P (Fin.cons t y) then 1 else 0 := by rw [Finset.sum_comm]

private lemma countWhere_affine_ne_zero {R : Type*} [Fintype R]
    [Field R] [DecidableEq R] (a b : R) (hb : b ≠ 0) :
    countWhere (fun t : R => a + t * b ≠ 0) = Fintype.card R - 1 := by
  classical
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
      intro c hnonzero
      obtain ⟨x, hx⟩ := hnonzero
      have hall (y : Fin 0 → R) : multiaffineEval c y ≠ 0 := by
        simpa only [Subsingleton.elim y x] using hx
      rw [pow_zero]
      unfold countWhere
      rw [Finset.filter_congr_decidable]
      simp [hall]
  | succ k ih =>
      intro c hnonzero
      let c0 : (Fin k → Bool) → R := fun e => c (Fin.cons false e)
      let c1 : (Fin k → Bool) → R := fun e => c (Fin.cons true e)
      let r : (Fin k → R) → R := fun y => multiaffineEval c0 y
      let q : (Fin k → R) → R := fun y => multiaffineEval c1 y
      have heval (t : R) (y : Fin k → R) :
          multiaffineEval c (Fin.cons t y) = r y + t * q y := by
        simpa only [r, q, c0, c1, Fin.tail_cons, Fin.cons_zero] using
          multiaffineEval_succ c (Fin.cons t y)
      rw [pow_succ]
      rw [countWhere_pi_succ]
      by_cases hq : ∃ y, q y ≠ 0
      · have ihq : (Fintype.card R - 1) ^ k ≤
            countWhere fun y : Fin k → R => q y ≠ 0 := by
          simpa only [q] using ih c1 hq
        calc
          (Fintype.card R - 1) ^ k * (Fintype.card R - 1) ≤
              countWhere (fun y : Fin k → R => q y ≠ 0) *
                (Fintype.card R - 1) :=
            Nat.mul_le_mul_right _ ihq
          _ = ∑ y : Fin k → R,
                if q y ≠ 0 then Fintype.card R - 1 else 0 := by
            rw [countWhere_eq_sum_ite, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y _
            split <;> simp_all
          _ ≤ ∑ y : Fin k → R,
              countWhere fun t : R => multiaffineEval c (Fin.cons t y) ≠ 0 := by
            apply Finset.sum_le_sum
            intro y _
            by_cases hy : q y ≠ 0
            · rw [if_pos hy]
              have hcount := countWhere_affine_ne_zero (r y) (q y) hy
              simpa only [heval] using hcount.ge
            · rw [if_neg hy]
              exact Nat.zero_le _
      · have hqzero : ∀ y, q y = 0 := by simpa only [not_exists, not_ne_iff] using hq
        have hr : ∃ y, r y ≠ 0 := by
          obtain ⟨x, hx⟩ := hnonzero
          refine ⟨Fin.tail x, ?_⟩
          have hs := heval (x 0) (Fin.tail x)
          rw [Fin.cons_self_tail] at hs
          rw [hqzero (Fin.tail x), mul_zero, add_zero] at hs
          exact fun hzero => hx (hs.trans hzero)
        have ihr : (Fintype.card R - 1) ^ k ≤
            countWhere fun y : Fin k → R => r y ≠ 0 := by
          simpa only [r] using ih c0 hr
        calc
          (Fintype.card R - 1) ^ k * (Fintype.card R - 1) ≤
              countWhere (fun y : Fin k → R => r y ≠ 0) *
                (Fintype.card R - 1) :=
            Nat.mul_le_mul_right _ ihr
          _ ≤ countWhere (fun y : Fin k → R => r y ≠ 0) * Fintype.card R :=
            Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = ∑ y : Fin k → R,
                if r y ≠ 0 then Fintype.card R else 0 := by
            rw [countWhere_eq_sum_ite, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y _
            split <;> simp_all
          _ ≤ ∑ y : Fin k → R,
              countWhere fun t : R => multiaffineEval c (Fin.cons t y) ≠ 0 := by
            apply Finset.sum_le_sum
            intro y _
            by_cases hy : r y ≠ 0
            · rw [if_pos hy]
              have hconst :
                  countWhere (fun t : R => multiaffineEval c (Fin.cons t y) ≠ 0) =
                    Fintype.card R := by
                have hall (t : R) : multiaffineEval c (Fin.cons t y) ≠ 0 := by
                  rw [heval, hqzero y, mul_zero, add_zero]
                  exact hy
                unfold countWhere
                rw [Finset.filter_congr_decidable]
                simp [hall]
              exact hconst.ge
            · rw [if_neg hy]
              exact Nat.zero_le _

private def shiftedCoefficients {R : Type*} [Ring R] {k : Nat}
    (c : (Fin k → Bool) → R) (a : R) (e : Fin k → Bool) : R :=
  c e - if e = fun _ => false then a else 0

private lemma multiaffineEval_shifted {R : Type*} [CommRing R] {k : Nat}
    (c : (Fin k → Bool) → R) (a : R) (x : Fin k → R) :
    multiaffineEval (shiftedCoefficients c a) x = multiaffineEval c x - a := by
  classical
  unfold multiaffineEval shiftedCoefficients
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp

private lemma levelSet_complement_count {N k : Nat} [NeZero N]
    (mu : Point N k → ZMod N) (a : ZMod N) :
    countWhere (fun y : Point N k => mu y = a) +
        countWhere (fun y : Point N k => mu y ≠ a) = N ^ k := by
  classical
  simp_rw [countWhere_eq_sum_ite]
  calc
    (∑ y : Point N k, if mu y = a then 1 else 0) +
          (∑ y : Point N k, if mu y ≠ a then 1 else 0) =
        ∑ y : Point N k,
          ((if mu y = a then 1 else 0) + (if mu y ≠ a then 1 else 0)) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ _y : Point N k, 1 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : mu y = a <;> simp [hy]
    _ = N ^ k := by simp [Point, ZMod.card]

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
  rw [abs_of_nonneg (sub_nonneg.mpr hpows)] at hbound
  rw [habsDiff, hmax, one_mul] at hbound
  simpa only [x, y] using hbound

/-- Lemma 15.3: a nonconstant multiaffine polynomial over the prime field
has at most `N^k - (N-1)^k` points in any one fibre. -/
theorem lemma_15_3_holds : lemma_15_3 := by
  intro N k _ hprime mu a hmultilinear hnconstant
  letI : Fact N.Prime := ⟨hprime⟩
  obtain ⟨c, hc⟩ := hmultilinear
  have hmu (x : Point N k) : mu x = multiaffineEval c x := by
    simpa only [multiaffineEval] using hc x
  let c' : (Fin k → Bool) → ZMod N := shiftedCoefficients c a
  have heval (x : Point N k) : multiaffineEval c' x = mu x - a := by
    change multiaffineEval (shiftedCoefficients c a) x = mu x - a
    rw [multiaffineEval_shifted, ← hmu]
  have hnonzero : ∃ x : Point N k, multiaffineEval c' x ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hnconstant
    refine ⟨a, fun x => ?_⟩
    exact sub_eq_zero.mp ((heval x).symm.trans (hzero x))
  have hnonzeroCount :
      (N - 1) ^ k ≤ countWhere fun x : Point N k => mu x ≠ a := by
    have hgrid := multiaffine_nonzero_count_lower k c' hnonzero
    have hcard : Fintype.card (ZMod N) = N := ZMod.card N
    rw [hcard] at hgrid
    calc
      (N - 1) ^ k ≤
          countWhere fun x : Point N k => multiaffineEval c' x ≠ 0 := hgrid
      _ = countWhere fun x : Point N k => mu x ≠ a := by
        unfold countWhere
        rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
        apply congrArg Finset.card
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, heval, sub_ne_zero]
  have hpartition := levelSet_complement_count mu a
  have hlevelNat :
      countWhere (fun x : Point N k => mu x = a) ≤ N ^ k - (N - 1) ^ k := by
    omega
  have hpowNat : (N - 1) ^ k ≤ N ^ k := Nat.pow_le_pow_left (Nat.sub_le N 1) k
  constructor
  · calc
      (countWhere (fun x : Point N k => mu x = a) : Real) ≤
          ((N ^ k - (N - 1) ^ k : Nat) : Real) := by exact_mod_cast hlevelNat
      _ = (N : Real) ^ k - (N - 1 : Nat) ^ k := by
        rw [Nat.cast_sub hpowNat, Nat.cast_pow, Nat.cast_pow]
  · exact real_pow_sub_pred_pow_le N k hprime.one_le

end LeanProofs.GowersSzemeredi
