import FabiusFunction.ThueMorseBooleanCube
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.BitIndices

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
* `sum_powerset_neg_one_pow_pow_card` — **general sharp moment**: at degree
  exactly `S.card`, the sum is `(-1)^{|S|} |S|! ∏_{j ∈ S} w j`.
* `sum_thueMorseSign_mul_affine_pow_eq_zero` and
  `sum_thueMorseSign_mul_affine_pow_card` — the Thue--Morse case, obtained
  by transporting along the Boolean-cube kernel: the classical Prouhet
  cancellation `∑_{n<2^m} ε(n)(x + nh)^r = 0` for `r < m`, and the sharp
  first moment `(-1)^m m! 2^(m choose 2) h^m`, over any commutative ring.
* `bitSupport` — the set of one-bit positions of `n`, with its dictionary
  (`mem`, reconstruction `∑ 2^j = n`, cardinality `= binaryWeight n`), and
  the **sparse Prouhet theorems** on the submasks of an arbitrary `n`:
  cancellation below `w(n)` and the sharp moment
  `(-1)^{w(n)} w(n)! 2^(β(n)) h^(w(n))`, where `β(n)` is the sum of the
  one-bit positions.
* `bitSupport_eq_toFinset_bitIndices` — the bridge identifying `bitSupport`
  with Mathlib's `Nat.bitIndices`; the whole bit dictionary above is a
  corollary of it, so no bit recursion is redone here.

The induction is the atlas's proof made exact: inserting one index into
`S` replaces `p` by `p - taylor (w a) p`, whose degree drops; Mathlib's
`taylor` API supplies the degree bookkeeping, and
`Finset.sum_powerset_insert` supplies the split of the powerset of
`insert a S` into the two halves that the induction pairs.

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
        simp [Nat.sub_self]
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
produce.  Used at both the `range m` and the `bitSupport n` scale sets. -/
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

/-- **Prouhet cancellation over any commutative ring.**  For `r < m`,
`∑_{n<2^m} ε(n) (x + nh)^r = 0`.  The corpus proves this over `ℚ` and
`ℝ`; the powerset engine proves it uniformly. -/
theorem sum_thueMorseSign_mul_affine_pow_eq_zero {R : Type*} [CommRing R]
    (m r : ℕ) (hr : r < m) (x h : R) :
    ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : R) * (x + (n : R) * h) ^ r = 0 := by
  rw [sum_thueMorseSign_mul_eq_sum_powerset m
    (fun n => (x + (n : R) * h) ^ r)]
  have hgen := sum_powerset_neg_one_pow_eval (range m)
    (fun j => (2 : R) ^ j * h) (Polynomial.X ^ r)
    (lt_of_le_of_lt (natDegree_X_pow_le r) (by simpa using hr)) x
  rw [← hgen]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [eval_pow, eval_X, cast_sum_two_pow_mul]

/-- **Sharp Prouhet moment over any commutative ring.**  At `r = m` the
cancellation breaks with the exact value
`(-1)^m · m! · 2^(m choose 2) · h^m`. -/
theorem sum_thueMorseSign_mul_affine_pow_card {R : Type*} [CommRing R]
    (m : ℕ) (x h : R) :
    ∑ n ∈ range (2 ^ m),
      ((thueMorseSign n : ℤ) : R) * (x + (n : R) * h) ^ m =
      (-1 : R) ^ m * (m.factorial : R) * 2 ^ m.choose 2 * h ^ m := by
  rw [sum_thueMorseSign_mul_eq_sum_powerset m
    (fun n => (x + (n : R) * h) ^ m)]
  have hgen := sum_powerset_neg_one_pow_pow_card (range m)
    (fun j => (2 : R) ^ j * h) x
  rw [Finset.card_range] at hgen
  rw [sum_powerset_pow_cast_bridge (range m) x h m, hgen]
  have hprod : ∏ j ∈ range m, ((2 : R) ^ j * h) =
      2 ^ m.choose 2 * h ^ m := by
    rw [prod_two_pow_mul, Finset.card_range, Finset.sum_range_id,
      Nat.choose_two_right]
  rw [hprod]
  ring

/-! ## Bit supports and sparse Prouhet identities -/

/-- The set of one-bit positions of `n`.  Every set position is at most
`n`, so the window `range (n+1)` sees all of them. -/
def bitSupport (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun j => n.testBit j)

/-- Membership in the bit support is exactly the bit test.  The window
`range (n+1)` is wide enough because a set bit at position `j` forces
`2^j ≤ n` (Mathlib's `Nat.two_pow_le_of_mem_bitIndices`). -/
theorem mem_bitSupport {n j : ℕ} :
    j ∈ bitSupport n ↔ n.testBit j = true := by
  rw [bitSupport, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have h2 : 2 ^ j ≤ n :=
    Nat.two_pow_le_of_mem_bitIndices (Nat.mem_bitIndices.mpr h)
  have hj : j < 2 ^ j := Nat.lt_two_pow_self
  omega

/-- **Bridge to Mathlib.**  The bit support is the finset of Mathlib's
`Nat.bitIndices`, the sorted list of one-bit positions.  Every entry of
the bit dictionary below is read off from this identification. -/
theorem bitSupport_eq_toFinset_bitIndices (n : ℕ) :
    bitSupport n = n.bitIndices.toFinset := by
  ext j
  simp [mem_bitSupport]

/-- Shifting a list of positions up by one shifts the finset it spans. -/
private theorem toFinset_map_succ (l : List ℕ) :
    (l.map (· + 1)).toFinset = l.toFinset.image (· + 1) := by
  ext j
  simp

/-- The bit support of an even number: shift every position up. -/
theorem bitSupport_two_mul (k : ℕ) :
    bitSupport (2 * k) = (bitSupport k).image (· + 1) := by
  rw [bitSupport_eq_toFinset_bitIndices, bitSupport_eq_toFinset_bitIndices,
    Nat.bitIndices_two_mul, toFinset_map_succ]

/-- The bit support of an odd number: position zero plus the shifts. -/
theorem bitSupport_two_mul_add_one (k : ℕ) :
    bitSupport (2 * k + 1) = insert 0 ((bitSupport k).image (· + 1)) := by
  rw [bitSupport_eq_toFinset_bitIndices, bitSupport_eq_toFinset_bitIndices,
    Nat.bitIndices_two_mul_add_one, List.toFinset_cons, toFinset_map_succ]

/-- **Reconstruction.**  The one-bit positions reconstruct the number:
`∑_{j ∈ bitSupport n} 2^j = n`. -/
theorem sum_two_pow_bitSupport (n : ℕ) :
    ∑ j ∈ bitSupport n, 2 ^ j = n := by
  rw [bitSupport_eq_toFinset_bitIndices,
    List.sum_toFinset _ Nat.bitIndices_nodup,
    Nat.sum_map_two_pow_bitIndices]

/-- The bit support has `binaryWeight n` elements. -/
theorem card_bitSupport (n : ℕ) :
    (bitSupport n).card = binaryWeight n := by
  have hsub : bitSupport n ⊆ range (n + 1) := Finset.filter_subset _ _
  have hw := binaryWeight_sum_two_pow hsub
  rw [sum_two_pow_bitSupport] at hw
  omega

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
