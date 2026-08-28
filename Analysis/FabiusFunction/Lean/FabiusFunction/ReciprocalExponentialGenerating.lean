import FabiusFunction.BellPolynomialInversion
import FabiusFunction.MomentCumulantAlgebra

/-!
# The reciprocal of an exponential generating sequence

Sequences `ℕ → R` carry the binomial convolution `Bell.binomialConv`, the
coefficientwise shadow of multiplying exponential generating functions.  Its
unit is `Bell.unitSeq`, the coefficient sequence of the constant series `1`.
This module inverts a sequence for that product and identifies the inverse in
closed form: for `m 0 = 1` the reciprocal of `m` is the family of **complete
Bell polynomials of the negated cumulants** of `m`,

`reciprocal m = complete (-cumulant m)`,   `m ⋆ reciprocal m = (1, 0, 0, …)`.

The whole content is one line of formal exponential calculus,
`exp K · exp (-K) = exp 0 = 1` at `K = cumulant m`: `Bell.complete_add` is the
exponential formula, `Bell.complete_cumulant` says `m = exp (cumulant m)`, and
`complete_zero_eq_unitSeq` says `exp 0 = 1`.  No analysis, no probability, no
division and no limit is involved, so — unlike the sources, which read these
coefficients off real analytic series — the statement is proved over an
arbitrary commutative *ring*: cumulants exist there because the recurrence
solves for its last term against `m 0 = 1`.  A `ℚ`-algebra is not needed, and
neither is any characteristic hypothesis.

Two frontier computations in this corpus need exactly this object under
different names — reciprocal-series coefficients presented as
`b_j = B_j(1!·g_1, …, j!·g_j)/j!`, and a family of Appell constants that are
the same numbers up to sign and factorial normalisation.  They are one
sequence, and `eq_reciprocal_of_binomialConv` is what says so: the binomial
convolution *characterises* the reciprocal, so any other construction of it (a
recursion, a determinant, an Appell normalisation) is the Bell form, with no
further computation.

## Main results

* `Bell.binomialConv_unitSeq_right` / `_left` — `unitSeq` is the unit.
* `Bell.complete_zero_eq_unitSeq` — `exp 0 = 1`.
* `Bell.binomialConv_complete_neg` — negating a cumulant sequence inverts its
  complete Bell family: `exp K ⋆ exp (-K) = 1`, for *every* sequence `K`.
* `Bell.reciprocal` and `Bell.binomialConv_reciprocal` — the reciprocal of a
  normalised sequence, and the identity that names it.
* `Bell.eq_reciprocal_of_binomialConv` — uniqueness: nothing else convolves
  with `m` to the unit sequence.
* `Bell.reciprocal_succ` — the explicit backward recursion for the
  coefficients, the form a numerical caller uses.
* `Bell.reciprocal_reciprocal` — the reciprocal is an involution on normalised
  sequences, because negation is one on cumulants
  (`Bell.cumulant_reciprocal`).
* `Fabius.completeBellPolynomial_eq_complete` and
  `Fabius.momentCumulant_eq_cumulant` — the `ℚ`-algebra transforms of
  `MomentCumulantAlgebra` are the division-free ones of
  `BellPolynomialInversion`; consequently
  `Fabius.binomialConv_completeBellPolynomial_neg_momentCumulant` states the
  reciprocal in the notation the source documents use.

The algebraic core lives in the namespace `Bell` of `BellPolynomialInversion`,
where its ingredients are; only the dictionary with the `ℚ`-algebra transforms
is in `Fabius`.  No Fabius-specific or analytic instance appears here.
-/

set_option autoImplicit false

namespace Bell

variable {R : Type*}

section CommSemiring

variable [CommSemiring R]

/-! ### The unit sequence

`unitSeq` is a two-sided unit for the binomial convolution, and it is the
complete Bell family of the zero sequence.  These two facts are what makes
"reciprocal" mean something. -/

/-- The unit sequence is a right unit for the binomial convolution: only the
diagonal term `i = n` of `∑_{i+j=n}` survives. -/
theorem binomialConv_unitSeq_right (a : ℕ → R) :
    binomialConv a (unitSeq R) = a := by
  funext n
  rw [binomialConv_eq_sum_range, Finset.sum_range_succ]
  have hzero : ∀ k ∈ Finset.range n,
      (n.choose k : R) * (a k * unitSeq R (n - k)) = 0 := by
    intro k hk
    obtain ⟨d, hd⟩ : ∃ d, n - k = d + 1 :=
      ⟨n - k - 1, by have := Finset.mem_range.mp hk; omega⟩
    rw [hd, unitSeq_succ, mul_zero, mul_zero]
  rw [Finset.sum_eq_zero hzero, zero_add, Nat.choose_self, Nat.sub_self]
  simp

/-- The unit sequence is a left unit for the binomial convolution. -/
theorem binomialConv_unitSeq_left (a : ℕ → R) :
    binomialConv (unitSeq R) a = a := by
  rw [binomialConv_comm]
  exact binomialConv_unitSeq_right a

/-- `exp 0 = 1`: the complete Bell polynomials of the zero sequence are the
unit sequence. -/
theorem complete_zero_eq_unitSeq : complete (0 : ℕ → R) = unitSeq R := by
  funext n
  cases n with
  | zero => simp
  | succ n =>
    rw [complete_succ, unitSeq_succ, binomialConv_eq_sum_range]
    exact Finset.sum_eq_zero fun k _ => by simp

end CommSemiring

section CommRing

variable [CommRing R]

/-! ### The reciprocal sequence

Over a commutative ring the cumulants of a normalised sequence exist without
division, so the reciprocal can be written down: negate them. -/

/-- **Negation inverts the complete Bell transform.**  For every sequence `κ`,
the complete Bell family of `-κ` is the binomial-convolution inverse of that of
`κ`.  This is `exp K · exp (-K) = exp 0 = 1`, and it is the only computation in
this module: everything below is bookkeeping around it. -/
theorem binomialConv_complete_neg (κ : ℕ → R) :
    binomialConv (complete κ) (complete (-κ)) = unitSeq R := by
  have h : κ + -κ = 0 := by funext n; simp
  rw [← complete_add, h, complete_zero_eq_unitSeq]

/-- The **reciprocal** of an exponential generating sequence: the coefficients
of `1 / ∑ m n · Xⁿ/n!`, written as the complete Bell polynomials of the negated
cumulants of `m`.  For `m 0 = 1` — the only case in which the name is
deserved — it is the two-sided inverse of `m` for the binomial convolution. -/
def reciprocal (m : ℕ → R) : ℕ → R := complete (-cumulant m)

/-- The reciprocal is the complete Bell family of the negated cumulants; this
is the definition, recorded as a rewrite rule. -/
theorem reciprocal_eq_complete_neg_cumulant (m : ℕ → R) :
    reciprocal m = complete (-cumulant m) := rfl

/-- Reciprocals are normalised. -/
@[simp] theorem reciprocal_zero (m : ℕ → R) : reciprocal m 0 = 1 :=
  complete_zero _

/-- **The reciprocal identity.**  The binomial convolution of a normalised
sequence with the complete Bell family of its negated cumulants is the unit
sequence: `∑_{i+j=n} (n.choose i) · m i · b j = [n = 0]`. -/
theorem binomialConv_reciprocal (m : ℕ → R) (h0 : m 0 = 1) :
    binomialConv m (reciprocal m) = unitSeq R := by
  have h : binomialConv (complete (cumulant m)) (complete (-cumulant m))
      = unitSeq R := binomialConv_complete_neg (cumulant m)
  rw [complete_cumulant m h0] at h
  rw [reciprocal_eq_complete_neg_cumulant]
  exact h

/-- The reciprocal identity on the other side. -/
theorem binomialConv_reciprocal_left (m : ℕ → R) (h0 : m 0 = 1) :
    binomialConv (reciprocal m) m = unitSeq R := by
  rw [binomialConv_comm]
  exact binomialConv_reciprocal m h0

/-- **Uniqueness of the reciprocal.**  A normalised `m` has at most one inverse
for the binomial convolution, so any sequence convolving with `m` to the unit
sequence *is* the complete Bell family of the negated cumulants.  This is the
lemma that identifies differently-constructed reciprocal coefficients with each
other. -/
theorem eq_reciprocal_of_binomialConv {m b : ℕ → R} (h0 : m 0 = 1)
    (hb : binomialConv m b = unitSeq R) : b = reciprocal m := by
  refine binomialConv_right_cancel (w := m) (by rw [h0]; exact isUnit_one)
    fun n => ?_
  rw [binomialConv_comm b m, binomialConv_comm (reciprocal m) m, hb,
    binomialConv_reciprocal m h0]

/-- **The backward recursion for the reciprocal coefficients**: each is minus
the binomial convolution of the earlier ones against `m`.  Together with
`reciprocal_zero` this determines the sequence, and it is the form a numerical
caller evaluates. -/
theorem reciprocal_succ (m : ℕ → R) (h0 : m 0 = 1) (n : ℕ) :
    reciprocal m (n + 1)
      = -∑ k ∈ Finset.range (n + 1),
          ((n + 1).choose k : R) * (reciprocal m k * m (n + 1 - k)) := by
  have h : binomialConv (reciprocal m) m (n + 1) = 0 := by
    simpa using congrFun (binomialConv_reciprocal_left m h0) (n + 1)
  rw [binomialConv_eq_sum_range, Finset.sum_range_succ, Nat.choose_self,
    Nat.sub_self, h0, Nat.cast_one, one_mul, mul_one] at h
  exact eq_neg_of_add_eq_zero_right h

/-- **Taking reciprocals negates cumulants.**  No normalisation of `m` is
needed: `reciprocal m` is a complete Bell family by construction, and its
cumulants are read off by uniqueness of moment–cumulant inversion. -/
theorem cumulant_reciprocal (m : ℕ → R) :
    cumulant (reciprocal m) = -cumulant m := by
  have hκ : (-cumulant m) 0 = 0 := by simp
  exact (eq_cumulant_of_complete hκ
    (reciprocal_eq_complete_neg_cumulant m).symm).symm

/-- **The reciprocal is an involution** on normalised sequences — because
negation is one on cumulants. -/
theorem reciprocal_reciprocal (m : ℕ → R) (h0 : m 0 = 1) :
    reciprocal (reciprocal m) = m := by
  rw [reciprocal_eq_complete_neg_cumulant, cumulant_reciprocal, neg_neg,
    complete_cumulant m h0]

/-! ### The first three reciprocal coefficients

Read off the complete Bell polynomials of `-cumulant m`; the same two lines
give order four and beyond.  None of them needs `m 0 = 1`, but only under that
normalisation do they invert anything. -/

/-- `b₁ = -m₁`. -/
theorem reciprocal_one (m : ℕ → R) : reciprocal m 1 = -m 1 := by
  rw [reciprocal_eq_complete_neg_cumulant, complete_one, Pi.neg_apply,
    cumulant_one]

/-- `b₂ = 2m₁² - m₂`. -/
theorem reciprocal_two (m : ℕ → R) :
    reciprocal m 2 = 2 * m 1 ^ 2 - m 2 := by
  rw [reciprocal_eq_complete_neg_cumulant, complete_two]
  simp only [Pi.neg_apply, cumulant_one, cumulant_two]
  ring

/-- `b₃ = -m₃ + 6m₁m₂ - 6m₁³`. -/
theorem reciprocal_three (m : ℕ → R) :
    reciprocal m 3 = -m 3 + 6 * m 1 * m 2 - 6 * m 1 ^ 3 := by
  rw [reciprocal_eq_complete_neg_cumulant, complete_three]
  simp only [Pi.neg_apply, cumulant_one, cumulant_two, cumulant_three]
  ring

end CommRing

end Bell

/-! ## The dictionary with the rational-algebra transforms

`MomentCumulantAlgebra` builds the same two transforms by dividing and
multiplying by factorials around the formal `exp` and `log` of
`SaddleExpansion`.  Over a `ℚ`-algebra they agree with the division-free ones
above — both solve the same first-order recurrence — so the reciprocal
identity can be stated in the notation the source documents use. -/

namespace Fabius

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The factorially renormalised formal exponential and the division-free
complete Bell recursion compute the same polynomials.  Both start at `1` and
obey `B' = B ⋆ κ'`; the two written forms of that recurrence differ by the
reflection `j ↦ n - j` of the summation index. -/
theorem completeBellPolynomial_eq_complete (κ : ℕ → R) :
    completeBellPolynomial κ = Bell.complete κ := by
  refine Bell.eq_complete_of_recurrence κ _ (completeBellPolynomial_zero κ)
    fun n => ?_
  rw [completeBellPolynomial_succ, Bell.binomialConv_eq_sum_range,
    ← Finset.sum_range_reflect
      (fun j => (n.choose j : R) * κ (j + 1) * completeBellPolynomial κ (n - j))
      (n + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Nat.add_sub_cancel, Nat.choose_symm hj', Nat.sub_sub_self hj',
    Bell.shift_apply]
  ring

/-- The formal-logarithm transform of a normalised moment sequence is its
division-free cumulant sequence. -/
theorem momentCumulant_eq_cumulant (μ : ℕ → R) (hμ : μ 0 = 1) :
    momentCumulant μ = Bell.cumulant μ := by
  refine Bell.eq_cumulant_of_complete (momentCumulant_zero μ) ?_
  rw [← completeBellPolynomial_eq_complete]
  exact completeBellPolynomial_momentCumulant_of_zero_eq_one μ hμ

/-- The reciprocal coefficients in the notation of the source documents: the
complete Bell polynomials evaluated at the negated formal cumulants. -/
theorem reciprocal_eq_completeBellPolynomial (m : ℕ → R) (h0 : m 0 = 1) :
    Bell.reciprocal m = completeBellPolynomial (-momentCumulant m) := by
  rw [Bell.reciprocal_eq_complete_neg_cumulant,
    completeBellPolynomial_eq_complete, momentCumulant_eq_cumulant m h0]

/-- **The reciprocal identity over a `ℚ`-algebra**, in the notation the source
documents use: the binomial convolution of a normalised sequence with the
complete Bell polynomials of its negated cumulants is the unit sequence. -/
theorem binomialConv_completeBellPolynomial_neg_momentCumulant
    (m : ℕ → R) (h0 : m 0 = 1) :
    Bell.binomialConv m (completeBellPolynomial (-momentCumulant m))
      = Bell.unitSeq R := by
  rw [← reciprocal_eq_completeBellPolynomial m h0,
    Bell.binomialConv_reciprocal m h0]

end Fabius
