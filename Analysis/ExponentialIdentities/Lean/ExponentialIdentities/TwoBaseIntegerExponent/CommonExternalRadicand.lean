import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace LeanProofs.TwoBaseIntegerExponent

/-!
# A common external radicand in the multiplicatively dependent branch

Theorem `kn:thm-multiplicative` of the unified report splits every hypothetical counterexample
into two branches according to whether the four integers `M = 2 ^ β`, `A = 3 ^ β`, `2`, `3`
satisfy a multiplicative relation `M ^ a * A ^ b * 2 ^ c * 3 ^ d = 1`.  In the dependent
branch, taking `p`-adic valuations at a prime `p ≥ 5` — where `2` and `3` contribute nothing —
leaves
```
  a * v_p M + b * v_p A = 0 ,
```
so the exponent vectors of the two outputs are proportional away from `2` and `3`.
Proposition `kn:prop-dim` already records that `a` and `b` cannot share a sign and that the two
degenerate cases are exactly the smooth-output branches; both are kernel-verified in
`SecondIterateKernel`.

This module supplies the piece that was missing there: in the remaining, mixed-sign case the
proportionality forces the *external parts* of `M` and `A` to be perfect powers of one common
integer.  Writing the primitive ratio as `a₀ / b₀` with `Nat.Coprime a₀ b₀`, every prime
`p ≥ 5` has `b₀ ∣ v_p M` and `a₀ ∣ v_p A`, with the common quotient independent of which side
it is read from.  So `M`'s external part is a `b₀`-th power, `A`'s is an `a₀`-th power, and the
two share a radicand.

Nothing here uses transcendence.  The arithmetic input is only coprimality, and the single
hypothesis carried from the problem is that `M` and `A` are not both `{2,3}`-smooth, which is
what makes the radicand nontrivial; that exclusion is `integer_of_threeSmooth_outputs` in
`SmoothOutputs`.
-/

namespace CommonRadicand

/-- The arithmetic core: a proportionality `a₀ * x = b₀ * y` between natural exponents, with
`a₀` and `b₀` coprime, forces each coefficient to divide the opposite exponent. -/
theorem dvd_of_coprime_mul_eq {a₀ b₀ x y : ℕ} (h : Nat.Coprime a₀ b₀)
    (heq : a₀ * x = b₀ * y) : b₀ ∣ x ∧ a₀ ∣ y := by
  constructor
  · -- `b₀ ∣ a₀ * x` because that product is `b₀ * y`
    have hb : b₀ ∣ a₀ * x := ⟨y, heq⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left h.symm hb)
  · -- `a₀ ∣ b₀ * y` because that product is `a₀ * x`
    have ha : a₀ ∣ b₀ * y := ⟨x, heq.symm⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left h ha)

/-- The two quotients agree: the common exponent is well defined. -/
theorem quot_eq_of_coprime_mul_eq {a₀ b₀ x y : ℕ} (h : Nat.Coprime a₀ b₀)
    (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) (heq : a₀ * x = b₀ * y) :
    x / b₀ = y / a₀ := by
  obtain ⟨hbx, hay⟩ := dvd_of_coprime_mul_eq h heq
  obtain ⟨s, hs⟩ := hbx
  obtain ⟨t, ht⟩ := hay
  subst hs
  subst ht
  -- `a₀ * (b₀ * s) = b₀ * (a₀ * t)` cancels to `s = t`
  have hst : s = t := by
    have : a₀ * b₀ * s = a₀ * b₀ * t := by ring_nf at heq ⊢; omega
    have hpos : 0 < a₀ * b₀ := Nat.pos_of_ne_zero (by simpa using mul_ne_zero ha₀ hb₀)
    exact Nat.eq_of_mul_eq_mul_left hpos this
  simp [hst, Nat.pos_of_ne_zero hb₀, Nat.pos_of_ne_zero ha₀]

/-- **Common external radicand.**  If the exponent vectors of `M` and `A` are proportional in
the primitive ratio `a₀ : b₀` at every prime `p ≥ 5`, then at each such prime `b₀` divides the
exponent in `M`, `a₀` divides the exponent in `A`, and the two quotients coincide.  Hence the
external part of `M` is a `b₀`-th power and that of `A` is an `a₀`-th power, of one and the
same radicand. -/
theorem common_external_radicand {M A a₀ b₀ : ℕ}
    (hcop : Nat.Coprime a₀ b₀) (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0)
    (hprop : ∀ p, p.Prime → 5 ≤ p →
      a₀ * M.factorization p = b₀ * A.factorization p) :
    ∀ p, p.Prime → 5 ≤ p →
      b₀ ∣ M.factorization p ∧ a₀ ∣ A.factorization p ∧
        M.factorization p / b₀ = A.factorization p / a₀ := by
  intro p hp hp5
  have heq := hprop p hp hp5
  obtain ⟨h1, h2⟩ := dvd_of_coprime_mul_eq hcop heq
  exact ⟨h1, h2, quot_eq_of_coprime_mul_eq hcop ha₀ hb₀ heq⟩

/-- The radicand is nontrivial exactly when some external prime occurs, which is the
content of channel (i): `M` and `A` are not both `{2,3}`-smooth. -/
theorem radicand_exponent_pos {M A a₀ b₀ : ℕ} {p : ℕ}
    (hcop : Nat.Coprime a₀ b₀) (hb₀ : b₀ ≠ 0)
    (_hp : p.Prime) (_hp5 : 5 ≤ p)
    (heq : a₀ * M.factorization p = b₀ * A.factorization p)
    (hpos : 0 < M.factorization p) :
    0 < M.factorization p / b₀ := by
  obtain ⟨⟨s, hs⟩, _⟩ := dvd_of_coprime_mul_eq hcop heq
  rw [hs, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hb₀)]
  rcases Nat.eq_zero_or_pos s with h | h
  · rw [h, Nat.mul_zero] at hs; omega
  · exact h

end CommonRadicand

end LeanProofs.TwoBaseIntegerExponent
