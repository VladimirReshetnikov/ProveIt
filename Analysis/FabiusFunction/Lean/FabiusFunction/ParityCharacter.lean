import FabiusFunction.BitPositionGenerating

/-!
# The weighted binary parity character

The exponent-sequence volume's lobe-sign law is governed by the
character

`ε_a(N) = (-1)^{∑_h ā_h · b_h(N)}`,

where `b_h(N)` is the `h`-th binary digit of `N` and `ā_h = a_h mod 2`.
Only the parity of the weight sequence enters, and at the constant
sequence `a ≡ 1` the character is the Thue–Morse sign.  The corpus
formalizes the sign law only in that constant case; this module
supplies the character itself, in general.

Because `b_h(N) = 1` exactly when `h ∈ bitSupport N`, the exponent is
the plain sum of the weights over the bit support, which makes the
Boolean-cube machinery apply verbatim.  The result is a weighted
generalization of the corpus's finite Thue–Morse product identity:
over any commutative ring,

`∏_{j<m} (1 + (-1)^{a_j}·z^{2^j}) = ∑_{n<2^m} ε_a(n)·z^n`,

which at `a ≡ 1` is `∏_{j<m}(1 - z^{2^j}) = ∑_{n<2^m} ε_n z^n`.

The automaticity criterion of the volume — that `ε_a` is `2`-automatic
iff the parity word is eventually periodic — is **not** addressed
here; the library has no automatic-sequence theory.

* `parityCharacter` — the character;
* `parityCharacter_const_one` — it is the Thue–Morse sign at `a ≡ 1`;
* `parityCharacter_mod_two` — only the parity of `a` matters;
* `prod_one_add_neg_one_pow_eq_sum_parityCharacter` — **the weighted
  product identity**.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The weighted binary parity character
`ε_a(n) = (-1)^{∑_{h ∈ bitSupport n} a h}`. -/
def parityCharacter (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  (-1) ^ (∑ h ∈ bitSupport n, a h)

/-- The weighted parity character is one at the empty binary support. -/
@[simp] theorem parityCharacter_zero (a : ℕ → ℕ) :
    parityCharacter a 0 = 1 := by
  simp [parityCharacter]

/-- On an encoded finite set the character is the sign of the weight
sum over that set. -/
theorem parityCharacter_sum_two_pow (a : ℕ → ℕ) (T : Finset ℕ) :
    parityCharacter a (∑ j ∈ T, 2 ^ j) = (-1) ^ (∑ j ∈ T, a j) := by
  rw [parityCharacter, bitSupport_sum_two_pow]

/-- At the constant weight `a ≡ 1` the character is the Thue–Morse
sign, since the exponent counts the bits. -/
theorem parityCharacter_const_one (n : ℕ) :
    parityCharacter (fun _ => 1) n = thueMorseSign n := by
  rw [parityCharacter, thueMorseSign, ← Finset.card_eq_sum_ones,
    card_bitSupport]

/-- A sign depends only on the residue of its exponent. -/
private theorem neg_one_pow_mod_two (m : ℕ) :
    (-1 : ℤ) ^ m = (-1) ^ (m % 2) := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **Only the parity of the weights matters.** -/
theorem parityCharacter_mod_two (a : ℕ → ℕ) (n : ℕ) :
    parityCharacter a n = parityCharacter (fun h => a h % 2) n := by
  rw [parityCharacter, parityCharacter,
    neg_one_pow_mod_two (∑ h ∈ bitSupport n, a h),
    neg_one_pow_mod_two (∑ h ∈ bitSupport n, a h % 2),
    Finset.sum_nat_mod (bitSupport n) 2 a]

/-- **The weighted product identity.**  Over any commutative ring,

`∏_{j<m} (1 + (-1)^{a_j}·z^{2^j}) = ∑_{n<2^m} ε_a(n)·z^n`,

the Boolean-cube expansion with the weight sign attached to each
factor.  At `a ≡ 1` every factor is `1 - z^{2^j}` and this is the
finite Thue–Morse product identity. -/
theorem prod_one_add_neg_one_pow_eq_sum_parityCharacter
    {R : Type*} [CommRing R] (a : ℕ → ℕ) (z : R) (m : ℕ) :
    ∏ j ∈ range m, (1 + (((-1 : ℤ) ^ a j : ℤ) : R) * z ^ 2 ^ j) =
      ∑ n ∈ range (2 ^ m),
        ((parityCharacter a n : ℤ) : R) * z ^ n := by
  rw [prod_one_add_eq_sum_powerset]
  rw [← sum_powerset_two_pow m
    (fun n => ((parityCharacter a n : ℤ) : R) * z ^ n)]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hsign : (∏ j ∈ T, (((-1 : ℤ) ^ a j : ℤ) : R)) =
      (((-1 : ℤ) ^ (∑ j ∈ T, a j) : ℤ) : R) := by
    rw [← Int.cast_prod, Finset.prod_pow_eq_pow_sum]
  have hpow : (∏ j ∈ T, z ^ 2 ^ j) = z ^ (∑ j ∈ T, 2 ^ j) :=
    Finset.prod_pow_eq_pow_sum T _ z
  rw [Finset.prod_mul_distrib, hsign, hpow,
    parityCharacter_sum_two_pow]

end Fabius
