import FabiusFunction.FinitePolynomialFunctional
import FabiusFunction.ThueMorseBitSupport
import FabiusFunction.ThueMorseBooleanCube
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Sparse Prouhet identities: signed powerset sums annihilate polynomials

The atlas's finite-difference chapter rests on one mechanism: expanding the
operator product `∏ (I - T_{w j})` produces the signed sums
`∑_{T ⊆ S} (-1)^{|T|} f (x + ∑_{j ∈ T} w j)`, which annihilate polynomials
of degree below `|S|` and evaluate to `(-1)^{|S|} |S|! ∏ w` at degree
exactly `|S|`.  This module proves that mechanism in **full generality** —
any commutative ring, any finite index set, arbitrary step weights `w` —
strictly more general than the atlas, whose steps are the powers of two.

* `sum_powerset_neg_one_pow_eval` — **general Prouhet annihilation**: the
  signed powerset sum of `p.eval` vanishes when `p.natDegree < S.card`.
* `sum_powerset_neg_one_pow_eval_of_degree_lt` — the degree-valued form of
  the same theorem, including the zero polynomial when `S` is empty.
* `sum_powerset_neg_one_pow_pow_card` — **general sharp moment**: at degree
  exactly `S.card`, the sum is `(-1)^{|S|} |S|! ∏_{j ∈ S} w j`.
* `sum_powerset_neg_one_pow_eval_eq_coeff_card` — **master coefficient
  extraction**: on every polynomial of degree at most `|S|`, the same
  functional is the top coefficient times the sharp moment.  Thus the
  cancellation and first surviving moment are the two faces of one formula.
* `sum_thueMorseSign_mul_affine_pow_eq_zero` and
  `sum_thueMorseSign_mul_affine_pow_card` — the Thue--Morse case, obtained
  by transporting along the Boolean-cube kernel: the classical Prouhet
  cancellation `∑_{n<2^m} ε(n)(x + nh)^r = 0` for `r < m`, and the sharp
  first moment `(-1)^m m! 2^(m choose 2) h^m`, over any commutative ring.
* `sum_thueMorseSign_mul_affine_eval_eq_coeff_card` — the dyadic polynomial
  extractor: for degree at most `m`, the whole signed block sum is the
  degree-`m` coefficient times that sharp factor.
* `sum_thueMorseSign_mul_affine_eval_of_degree_lt` — the degree-valued
  polynomial form of the same block cancellation.  It includes the true
  boundary case `m = 0`, where the zero polynomial is the unique polynomial
  of degree below zero.
* The imported canonical `bitSupport` dictionary parametrizes the
  **sparse Prouhet theorems** on the submasks of an arbitrary `n`:
  cancellation below `w(n)` and the sharp moment
  `(-1)^{w(n)} w(n)! 2^(β(n)) h^(w(n))`, where `β(n)` is the sum of the
  one-bit positions.
* `sum_submask_neg_one_pow_eval_of_degree_lt` — the degree-valued sparse
  cancellation, whose boundary case at `n = 0` includes the zero polynomial.
  The bridge to Mathlib's `Nat.bitIndices`, reconstruction, and cardinality
  identities live upstream in `ThueMorseBitSupport`.

The induction is the atlas's proof made exact: inserting one index into
`S` replaces `p` by `p - taylor (w a) p`, whose degree drops; Mathlib's
`taylor` API supplies the degree bookkeeping, and
`Finset.sum_powerset_insert` supplies the split of the powerset of
`insert a S` into the two halves that the induction pairs.

Linearity then upgrades the monomial results to arbitrary polynomials.  The
generic selected-coefficient principle in `FinitePolynomialFunctional`
packages the finite sum interchange once: the lower moments vanish and the
degree-`|S|` moment is the sole survivor.

The dyadic specializations all feed natural-number submasks into an engine
whose steps are ring elements; the cast bridge and the step-product
evaluation that this needs are isolated once, in the private section
`Dyadic step bookkeeping`, instead of being repeated at each call site.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-! ## The degree-drop lemma -/

/-- Translating a polynomial does not change its leading term, so the
difference with the original drops in degree. -/
private theorem natDegree_taylor_sub_lt {R : Type*} [CommRing R]
    (p : R[X]) (c : R) (hp : 1 ≤ p.natDegree) :
    (Polynomial.taylor c p - p).natDegree < p.natDegree := by
  rcases eq_or_ne (Polynomial.taylor c p - p) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    omega
  · have hle : (Polynomial.taylor c p - p).natDegree ≤ p.natDegree := by
      refine le_trans (natDegree_sub_le _ _) ?_
      simp [natDegree_taylor]
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hlead : (Polynomial.taylor c p - p).leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr h0
      rw [leadingCoeff, h, coeff_sub, coeff_taylor_natDegree,
        coeff_natDegree, sub_self] at hlead
      exact hlead rfl

/-! ## General Prouhet annihilation -/

/-- **General Prouhet annihilation.**  Over any commutative ring, for any
finite index set `S` and any step weights `w`, the signed powerset sum of
a polynomial of degree below `|S|` vanishes:
`∑_{T ⊆ S} (-1)^{|T|} p(x + ∑_{j ∈ T} w j) = 0`.
The atlas states this for the dyadic steps `w j = 2^j h`; the proof never
uses that choice. -/
theorem sum_powerset_neg_one_pow_eval {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → R) :
    ∀ (p : R[X]), p.natDegree < S.card → ∀ x : R,
      ∑ T ∈ S.powerset, (-1 : R) ^ T.card * p.eval (x + ∑ j ∈ T, w j) =
        0 := by
  induction S using Finset.induction_on with
  | empty =>
      intro p hdeg x
      exact absurd hdeg (by simp)
  | insert a S ha ih =>
      intro p hdeg x
      -- Split the powerset by membership of `a` and pair the halves.
      rw [Finset.sum_powerset_insert ha]
      -- The paired sum is the signed sum for `p - taylor (w a) p`.
      have hpair : ∀ T ∈ S.powerset,
          (-1 : R) ^ T.card * p.eval (x + ∑ j ∈ T, w j) +
            (-1 : R) ^ (insert a T).card *
              p.eval (x + ∑ j ∈ insert a T, w j) =
          (-1 : R) ^ T.card *
            (p - Polynomial.taylor (w a) p).eval (x + ∑ j ∈ T, w j) := by
        intro T hT
        have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
        rw [Finset.card_insert_of_notMem haT, Finset.sum_insert haT,
          eval_sub, taylor_eval]
        rw [show x + (w a + ∑ j ∈ T, w j) = x + ∑ j ∈ T, w j + w a by ring,
          pow_succ]
        ring
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hpair]
      -- Apply the induction hypothesis to the dropped-degree polynomial.
      rcases Nat.eq_zero_or_pos p.natDegree with hp0 | hp0
      · -- A constant polynomial: the pairing already cancels it.
        obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hp0
        simp [Polynomial.taylor_C]
      · have hdrop : (p - Polynomial.taylor (w a) p).natDegree < S.card := by
          have h1 : (Polynomial.taylor (w a) p - p).natDegree <
              p.natDegree := natDegree_taylor_sub_lt p (w a) hp0
          have h2 : (p - Polynomial.taylor (w a) p).natDegree =
              (Polynomial.taylor (w a) p - p).natDegree := by
            rw [show p - Polynomial.taylor (w a) p =
              -(Polynomial.taylor (w a) p - p) by ring, natDegree_neg]
          rw [Finset.card_insert_of_notMem ha] at hdeg
          omega
        exact ih _ hdrop x

/-- **Degree-valued general Prouhet annihilation.**  This is the natural
`Polynomial.degree` form of `sum_powerset_neg_one_pow_eval`.  Unlike its
`natDegree` formulation, it records that the zero polynomial has degree
`⊥`, so it also covers the zero polynomial on the empty index set.  The
ambient index type needs no decidable-equality instance in the public API. -/
theorem sum_powerset_neg_one_pow_eval_of_degree_lt
    {R : Type*} [CommRing R] {ι : Type*}
    (S : Finset ι) (w : ι → R) (p : R[X])
    (hdeg : p.degree < (S.card : WithBot ℕ)) (x : R) :
    ∑ T ∈ S.powerset, (-1 : R) ^ T.card * p.eval (x + ∑ j ∈ T, w j) =
      0 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  · exact sum_powerset_neg_one_pow_eval S w p
      ((Polynomial.natDegree_lt_iff_degree_lt hp).2 hdeg) x

/-! ## The general sharp moment -/

/-- **General sharp moment.**  At degree exactly `|S|`, the signed
powerset sum no longer cancels: it evaluates to
`(-1)^{|S|} · |S|! · ∏_{j ∈ S} w j`, independently of `x`.  The steps
enter only through their product. -/
theorem sum_powerset_neg_one_pow_pow_card {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → R) :
    ∀ x : R,
      ∑ T ∈ S.powerset, (-1 : R) ^ T.card *
          (x + ∑ j ∈ T, w j) ^ S.card =
        (-1 : R) ^ S.card * (S.card.factorial : R) * ∏ j ∈ S, w j := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      intro x
      set s := S.card with hs
      -- Pair the two halves of the powerset as in the annihilation proof.
      rw [Finset.sum_powerset_insert ha]
      have hcard : (insert a S).card = s + 1 :=
        Finset.card_insert_of_notMem ha
      -- Each pair contributes the difference `y^(s+1) - (y + c)^(s+1)`.
      have hpair : ∀ T ∈ S.powerset,
          (-1 : R) ^ T.card * (x + ∑ j ∈ T, w j) ^ (insert a S).card +
            (-1 : R) ^ (insert a T).card *
              (x + ∑ j ∈ insert a T, w j) ^ (insert a S).card =
          (-1 : R) ^ T.card *
            ((x + ∑ j ∈ T, w j) ^ (s + 1) -
              (x + ∑ j ∈ T, w j + w a) ^ (s + 1)) := by
        intro T hT
        have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
        rw [hcard, Finset.card_insert_of_notMem haT,
          Finset.sum_insert haT,
          show x + (w a + ∑ j ∈ T, w j) = x + ∑ j ∈ T, w j + w a by ring,
          pow_succ (-1 : R)]
        ring
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hpair]
      -- Binomial expansion of the difference, with the top term cancelling.
      have hbinom : ∀ y : R,
          y ^ (s + 1) - (y + w a) ^ (s + 1) =
            -∑ k ∈ range (s + 1),
              y ^ k * w a ^ (s + 1 - k) * ((s + 1).choose k : R) := by
        intro y
        rw [add_pow, Finset.sum_range_succ]
        simp
      rw [Finset.sum_congr rfl fun T _ => by rw [hbinom]]
      -- Pull the negation and the inner sum outside, then swap the sums.
      have hout : ∀ T ∈ S.powerset,
          (-1 : R) ^ T.card *
            -∑ k ∈ range (s + 1), (x + ∑ j ∈ T, w j) ^ k *
              w a ^ (s + 1 - k) * ((s + 1).choose k : R) =
          ∑ k ∈ range (s + 1),
            -((w a ^ (s + 1 - k) * ((s + 1).choose k : R)) *
              ((-1 : R) ^ T.card * (x + ∑ j ∈ T, w j) ^ k)) := by
        intro T _
        rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [Finset.sum_congr rfl hout, Finset.sum_comm]
      -- Inner sums below the top degree vanish.
      have hzero : ∀ k, k < S.card →
          ∑ T ∈ S.powerset, (-1 : R) ^ T.card *
            (x + ∑ j ∈ T, w j) ^ k = 0 := by
        intro k hk
        have hdeg : (Polynomial.X ^ k : R[X]).natDegree < S.card :=
          lt_of_le_of_lt (natDegree_X_pow_le k) hk
        have h := sum_powerset_neg_one_pow_eval S w
          (Polynomial.X ^ k) hdeg x
        simpa using h
      have hvanish : ∀ k ∈ range s,
          ∑ T ∈ S.powerset,
            -((w a ^ (s + 1 - k) * ((s + 1).choose k : R)) *
              ((-1 : R) ^ T.card * (x + ∑ j ∈ T, w j) ^ k)) = 0 := by
        intro k hk
        have hk' : k < S.card := by
          have := Finset.mem_range.mp hk
          omega
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hzero k hk',
          mul_zero, neg_zero]
      rw [Finset.sum_range_succ, Finset.sum_congr rfl hvanish,
        Finset.sum_const_zero, zero_add, Finset.sum_neg_distrib,
        ← Finset.mul_sum, ih x]
      -- Collect the constants.
      rw [hcard, Finset.prod_insert ha, Nat.choose_succ_self_right,
        Nat.factorial_succ, show s + 1 - s = 1 from by omega]
      push_cast
      ring

/-! ## The master coefficient-extraction identity -/

/-- **Master arbitrary-step coefficient extraction.**  Let `S` be any
finite set of steps in a commutative ring.  On polynomials of degree at most
`|S|`, its signed powerset functional extracts precisely the coefficient of
degree `|S|`:

`∑_{T ⊆ S} (-1)^{|T|} p(x + ∑_{j ∈ T} w j)`
`  = p.coeff |S| · ((-1)^{|S|} |S|! ∏_{j ∈ S} w j)`.

No nonzeroness hypotheses on the ring or the steps are needed.  In
particular the statement includes the zero polynomial and the empty set of
steps; the lower-degree cancellation and the sharp monomial moment are its
two extremal special cases. -/
theorem sum_powerset_neg_one_pow_eval_eq_coeff_card
    {R : Type*} [CommRing R] {ι : Type*}
    (S : Finset ι) (w : ι → R) (p : R[X])
    (hdeg : p.natDegree ≤ S.card) (x : R) :
    ∑ T ∈ S.powerset,
        (-1 : R) ^ T.card * p.eval (x + ∑ j ∈ T, w j) =
      p.coeff S.card *
        ((-1 : R) ^ S.card * (S.card.factorial : R) * ∏ j ∈ S, w j) := by
  classical
  have hselect := sum_weight_mul_eval₂_eq_topCoeff_mul_moment
    (RingHom.id R) S.powerset
    (fun T => (-1 : R) ^ T.card)
    (fun T => x + ∑ j ∈ T, w j)
    p S.card hdeg fun d hd => by
      have hzero := sum_powerset_neg_one_pow_eval S w
        (Polynomial.X ^ d)
        (lt_of_le_of_lt (Polynomial.natDegree_X_pow_le d) hd) x
      simpa only [Polynomial.eval_pow, Polynomial.eval_X] using hzero
  rw [sum_powerset_neg_one_pow_pow_card] at hselect
  simpa only [Polynomial.eval₂_id, RingHom.id_apply] using hselect

/-! ## Dyadic step bookkeeping -/

/-- The cast of a submask value times a step is the ring-valued sum of the
dyadic steps it selects: `(∑_{j∈T} 2^j : ℕ) · h = ∑_{j∈T} 2^j·h`. -/
private theorem cast_sum_two_pow_mul {R : Type*} [CommRing R]
    (T : Finset ℕ) (h : R) :
    ((∑ j ∈ T, 2 ^ j : ℕ) : R) * h = ∑ j ∈ T, (2 : R) ^ j * h := by
  push_cast
  rw [Finset.sum_mul]

/-- **Cast bridge for signed powerset sums.**  Rewrites a signed powerset
sum indexed by natural submasks into the ring-valued step form that
`sum_powerset_neg_one_pow_eval` and `sum_powerset_neg_one_pow_pow_card`
produce.  This power-valued packaging is used by the sharp sparse-submask
specialization; polynomial-valued bridges use `cast_sum_two_pow_mul`
directly. -/
private theorem sum_powerset_pow_cast_bridge {R : Type*} [CommRing R]
    (S : Finset ℕ) (x h : R) (k : ℕ) :
    ∑ T ∈ S.powerset,
        (-1 : R) ^ T.card * (x + ((∑ j ∈ T, 2 ^ j : ℕ) : R) * h) ^ k =
      ∑ T ∈ S.powerset,
        (-1 : R) ^ T.card * (x + ∑ j ∈ T, (2 : R) ^ j * h) ^ k := by
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [cast_sum_two_pow_mul]

/-- The product of the dyadic steps over a set of scales:
`∏_{j∈S} 2^j·h = 2^(∑_{j∈S} j) · h^{|S|}`.  The sharp moments differ only
in how they then evaluate the exponent `∑_{j∈S} j` and the cardinality. -/
private theorem prod_two_pow_mul {R : Type*} [CommRing R] (S : Finset ℕ)
    (h : R) :
    ∏ j ∈ S, ((2 : R) ^ j * h) = 2 ^ (∑ j ∈ S, j) * h ^ S.card := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]

/-! ## Thue--Morse specializations -/

/-- **Transport.**  A signed Thue--Morse block sum is a signed powerset
sum: the Boolean-cube kernel of `ThueMorseBooleanCube` rewrites
`∑_{n<2^m} ε(n) g(n)` as `∑_{T ⊆ range m} (-1)^{|T|} g(∑_{j∈T} 2^j)`. -/
theorem sum_thueMorseSign_mul_eq_sum_powerset {R : Type*} [CommRing R]
    (m : ℕ) (g : ℕ → R) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : R) * g n =
      ∑ T ∈ (range m).powerset,
        (-1 : R) ^ T.card * g (∑ j ∈ T, 2 ^ j) := by
  rw [← sum_powerset_two_pow m
    (fun n => ((thueMorseSign n : ℤ) : R) * g n)]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [thueMorseSign, binaryWeight_sum_two_pow (Finset.mem_powerset.mp hT)]
  push_cast
  ring

/-- **Dyadic polynomial coefficient extraction.**  For every polynomial of
degree at most `m`, the affine Thue--Morse block functional extracts its
degree-`m` coefficient:

`∑_{n<2^m} ε(n) p(x + nh)`
`  = p.coeff m · ((-1)^m m! 2^(m choose 2) h^m)`.

This is the dyadic specialization of
`sum_powerset_neg_one_pow_eval_eq_coeff_card`; it is strictly more general
than the unshifted, unit-step coefficient formula and is the public bridge
from the arbitrary-step engine to the traditional Prouhet block. -/
theorem sum_thueMorseSign_mul_affine_eval_eq_coeff_card
    {R : Type*} [CommRing R] (m : ℕ) (p : R[X])
    (hdeg : p.natDegree ≤ m) (x h : R) :
    ∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : R) * p.eval (x + (n : R) * h) =
      p.coeff m *
        ((-1 : R) ^ m * (m.factorial : R) * 2 ^ m.choose 2 * h ^ m) := by
  rw [sum_thueMorseSign_mul_eq_sum_powerset m
    (fun n => p.eval (x + (n : R) * h))]
  have hgen := sum_powerset_neg_one_pow_eval_eq_coeff_card (range m)
    (fun j => (2 : R) ^ j * h) p (by simpa using hdeg) x
  rw [Finset.card_range] at hgen
  calc
    ∑ T ∈ (range m).powerset,
        (-1 : R) ^ T.card *
          p.eval (x + ((∑ j ∈ T, 2 ^ j : ℕ) : R) * h) =
        ∑ T ∈ (range m).powerset,
          (-1 : R) ^ T.card *
            p.eval (x + ∑ j ∈ T, (2 : R) ^ j * h) := by
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [cast_sum_two_pow_mul]
    _ = p.coeff m *
        ((-1 : R) ^ m * (m.factorial : R) *
          ∏ j ∈ range m, ((2 : R) ^ j * h)) := hgen
    _ = p.coeff m *
        ((-1 : R) ^ m * (m.factorial : R) * 2 ^ m.choose 2 * h ^ m) := by
      rw [prod_two_pow_mul, Finset.card_range, Finset.sum_range_id,
        Nat.choose_two_right]
      ring

/-- **Degree-valued Thue--Morse Prouhet cancellation.**  Every polynomial
of degree below `m` vanishes under the signed affine block functional
`p ↦ ∑_{n<2^m} ε(n) p(x + nh)`, over any commutative ring.

The `Polynomial.degree` hypothesis is deliberately more inclusive at the
empty boundary than the traditional `natDegree < m` statement: for `m = 0`
it admits exactly the zero polynomial, and the one-term block sum is then zero.
No separate nonzero-polynomial or positive-block hypothesis is needed. -/
theorem sum_thueMorseSign_mul_affine_eval_of_degree_lt
    {R : Type*} [CommRing R] (m : ℕ) (p : R[X])
    (hdeg : p.degree < (m : WithBot ℕ)) (x h : R) :
    ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : R) * p.eval (x + (n : R) * h) = 0 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  · have hnat : p.natDegree < m :=
      (Polynomial.natDegree_lt_iff_degree_lt hp).2 hdeg
    rw [sum_thueMorseSign_mul_affine_eval_eq_coeff_card m p hnat.le x h,
      Polynomial.coeff_eq_zero_of_natDegree_lt hnat, zero_mul]

/-- **Prouhet cancellation over any commutative ring.**  For `r < m`,
`∑_{n<2^m} ε(n) (x + nh)^r = 0`.  The corpus proves this over `ℚ` and
`ℝ`; this is the monomial corollary of the degree-valued polynomial
cancellation above. -/
theorem sum_thueMorseSign_mul_affine_pow_eq_zero {R : Type*} [CommRing R]
    (m r : ℕ) (hr : r < m) (x h : R) :
    ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : R) * (x + (n : R) * h) ^ r = 0 := by
  have hdegree : (Polynomial.X ^ r : R[X]).degree < (m : WithBot ℕ) :=
    (Polynomial.degree_X_pow_le r).trans_lt (WithBot.coe_lt_coe.mpr hr)
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    sum_thueMorseSign_mul_affine_eval_of_degree_lt
      m (Polynomial.X ^ r : R[X]) hdegree x h

/-- **Sharp Prouhet moment over any commutative ring.**  At `r = m` the
cancellation breaks with the exact value
`(-1)^m · m! · 2^(m choose 2) · h^m`. -/
theorem sum_thueMorseSign_mul_affine_pow_card {R : Type*} [CommRing R]
    (m : ℕ) (x h : R) :
    ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : R) * (x + (n : R) * h) ^ m =
      (-1 : R) ^ m * (m.factorial : R) * 2 ^ m.choose 2 * h ^ m := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow_self, one_mul] using
    sum_thueMorseSign_mul_affine_eval_eq_coeff_card
      m (Polynomial.X ^ m : R[X]) (Polynomial.natDegree_X_pow_le m) x h

/-! ## Sparse Prouhet identities on bit supports -/

/- The canonical bit-support dictionary, including reconstruction and the
cardinality identity, is imported directly from `ThueMorseBitSupport`. -/

/-- **Sparse Prouhet cancellation.**  The signed sum over the submasks of
`n` (parametrized by the subsets of its bit support) annihilates
polynomials of degree below `binaryWeight n`, over any commutative ring.
Together with `binaryWeight_sum_two_pow`, the sign `(-1)^{|T|}` is exactly
the Thue--Morse sign of the submask `∑_{j ∈ T} 2^j`. -/
theorem sum_submask_neg_one_pow_eval {R : Type*} [CommRing R]
    (n : ℕ) (p : R[X]) (hdeg : p.natDegree < binaryWeight n) (x h : R) :
    ∑ T ∈ (bitSupport n).powerset,
      (-1 : R) ^ T.card * p.eval (x + ((∑ j ∈ T, 2 ^ j : ℕ) : R) * h) =
      0 := by
  have hgen := sum_powerset_neg_one_pow_eval (bitSupport n)
    (fun j => (2 : R) ^ j * h) p (by rwa [card_bitSupport]) x
  rw [← hgen]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [cast_sum_two_pow_mul]

/-- **Degree-valued sparse Prouhet cancellation.**  The submask sum
annihilates every polynomial whose `Polynomial.degree` is below the number of
set bits of `n`.  Using `degree` rather than `natDegree` includes the genuine
boundary case `n = 0`, where the zero polynomial is the only polynomial of
degree below `binaryWeight 0 = 0`. -/
theorem sum_submask_neg_one_pow_eval_of_degree_lt
    {R : Type*} [CommRing R] (n : ℕ) (p : R[X])
    (hdeg : p.degree < (binaryWeight n : WithBot ℕ)) (x h : R) :
    ∑ T ∈ (bitSupport n).powerset,
      (-1 : R) ^ T.card * p.eval (x + ((∑ j ∈ T, 2 ^ j : ℕ) : R) * h) =
      0 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  · exact sum_submask_neg_one_pow_eval n p
      ((Polynomial.natDegree_lt_iff_degree_lt hp).2 hdeg) x h

/-- **Sharp sparse moment.**  At degree exactly `binaryWeight n`, the
submask sum evaluates to
`(-1)^{w(n)} · w(n)! · 2^{β(n)} · h^{w(n)}`, where
`β(n) = ∑_{j ∈ bitSupport n} j` is the sum of the one-bit positions. -/
theorem sum_submask_neg_one_pow_pow {R : Type*} [CommRing R]
    (n : ℕ) (x h : R) :
    ∑ T ∈ (bitSupport n).powerset,
      (-1 : R) ^ T.card *
        (x + ((∑ j ∈ T, 2 ^ j : ℕ) : R) * h) ^ binaryWeight n =
      (-1 : R) ^ binaryWeight n * ((binaryWeight n).factorial : R) *
        2 ^ (∑ j ∈ bitSupport n, j) * h ^ binaryWeight n := by
  have hgen := sum_powerset_neg_one_pow_pow_card (bitSupport n)
    (fun j => (2 : R) ^ j * h) x
  rw [card_bitSupport] at hgen
  rw [sum_powerset_pow_cast_bridge (bitSupport n) x h (binaryWeight n),
    hgen]
  have hprod : ∏ j ∈ bitSupport n, ((2 : R) ^ j * h) =
      2 ^ (∑ j ∈ bitSupport n, j) * h ^ binaryWeight n := by
    rw [prod_two_pow_mul, card_bitSupport]
  rw [hprod]
  ring

end Fabius
