import FabiusFunction.QPochhammerInfinite
import FabiusFunction.ThueMorseInfiniteProduct
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The multiplicative dissection of the infinite q-Pochhammer symbol

Every positive integer factors uniquely as an odd number times a power of two.
Reindexing `(q;q)_∞ = ∏'_{n≥1} (1 - qⁿ)` along that factorization gives the
*multiplicative* dissection

`(q;q)_∞ = ∏'_{(k,j) : ℕ×ℕ} (1 - q^((2k+1)·2^j))
        = ∏'_{k≥0} ∏'_{j≥0} (1 - (q^(2k+1))^(2^j))`,

grouped so that the inner product over `j` is lacunary in the nome `q^(2k+1)`.

This is orthogonal to the *additive* residue-class dissection
`qPochhammerInfIn_dissection` of `QPochhammerInfinite`, which splits the index
set by congruence rather than by 2-adic valuation.

The flattening step `qPochhammerInfIn_self_eq_tprod_pair` needs **no hypothesis
on `q`**: transporting an unordered product along an equivalence is
unconditional, and both sides carry Mathlib's junk value `1` together when the
family fails to be multipliable.  Only the regrouping into a product of
products needs `‖q‖ < 1`, through multipliability of the double family.

The one corpus dependency beyond the q-Pochhammer definition is
`multipliable_one_sub_pow_two_pow_complex`, the multipliability of the
lacunary product `∏_j (1 - z^(2^j))` on the unit disc.  That fact carries no
Thue--Morse content either, despite living in `ThueMorseInfiniteProduct`;
it is imported rather than reproved.

Nothing here mentions the Thue--Morse sequence.  The consumer that does is
`ThueMorseEulerFunction`, which identifies each inner lacunary product with a
value of the Thue--Morse generating function and so writes Euler's function as
a product over odd multipliers.

## Main results

* `oddTwoPowEquiv` -- unique factorization into odd part times 2-power, as an
  equivalence `ℕ × ℕ ≃ ℕ`, with `oddTwoPowEquiv_apply_add_one` naming the
  positive integer a pair encodes.
* `summable_norm_pow_odd_mul_two_pow` and
  `multipliable_one_sub_pow_odd_mul_two_pow` -- absolute convergence of the
  double family on the open unit disc.
* `qPochhammerInfIn_self_eq_tprod_pair` -- the flattened double product.
* `qPochhammerInfIn_self_eq_tprod_lacunary` -- the odd-part-first grouping.
-/

set_option autoImplicit false

namespace Fabius

/-! ## The odd-part / two-power indexing of the positive integers -/

/-- **Unique factorization into odd part times `2`-power**, packaged as an
equivalence `ℕ × ℕ ≃ ℕ`: the pair `(k, j)` encodes the positive integer
`(2k+1)·2^j`, shifted down by one so that the codomain is all of `ℕ`.

The inverse reads the two-power exponent off `Nat.factorization` and the odd
part off `ordCompl[2]`, which `Nat.not_dvd_ordCompl` certifies to be odd. -/
def oddTwoPowEquiv : ℕ × ℕ ≃ ℕ where
  toFun p := (2 * p.1 + 1) * 2 ^ p.2 - 1
  invFun n := ((ordCompl[2] (n + 1) - 1) / 2, (n + 1).factorization 2)
  left_inv p := by
    obtain ⟨k, j⟩ := p
    have hodd : ¬ (2 ∣ 2 * k + 1) := Nat.two_dvd_ne_zero.mpr (by omega)
    have hne : (2 * k + 1) ≠ 0 := by omega
    have hpow : (2 : ℕ) ^ j ≠ 0 := (Nat.two_pow_pos j).ne'
    have hpos : 0 < (2 * k + 1) * 2 ^ j := by positivity
    have h1 : (2 * k + 1) * 2 ^ j - 1 + 1 = (2 * k + 1) * 2 ^ j := by omega
    have hfac : ((2 * k + 1) * 2 ^ j).factorization 2 = j := by
      rw [Nat.factorization_mul hne hpow, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hodd,
        Nat.factorization_pow_self Nat.prime_two, zero_add]
    have hdiv : (2 * k + 1) * 2 ^ j / 2 ^ j = 2 * k + 1 :=
      Nat.mul_div_cancel _ (Nat.two_pow_pos j)
    have hk : (2 * k + 1 - 1) / 2 = k := by omega
    show ((ordCompl[2] ((2 * k + 1) * 2 ^ j - 1 + 1) - 1) / 2,
        ((2 * k + 1) * 2 ^ j - 1 + 1).factorization 2) = (k, j)
    rw [h1, hfac, hdiv, hk]
  right_inv n := by
    have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
    have hodd : ¬ (2 ∣ ordCompl[2] (n + 1)) :=
      Nat.not_dvd_ordCompl Nat.prime_two hne
    have hmod : ordCompl[2] (n + 1) % 2 = 1 := Nat.two_dvd_ne_zero.mp hodd
    -- `omega` handles `/` and `%` by numerals, but only once the odd part is an
    -- opaque variable: left as the compound `(n+1) / 2 ^ (n+1).factorization 2`
    -- it loses track of the atom's nonnegativity.
    have hc : 2 * ((ordCompl[2] (n + 1) - 1) / 2) + 1 = ordCompl[2] (n + 1) := by
      obtain ⟨x, hx⟩ : ∃ x, ordCompl[2] (n + 1) = x := ⟨_, rfl⟩
      rw [hx] at hmod ⊢
      omega
    have key : (2 * ((ordCompl[2] (n + 1) - 1) / 2) + 1) *
        2 ^ ((n + 1).factorization 2) = n + 1 := by
      rw [hc, mul_comm]
      exact Nat.ordProj_mul_ordCompl_eq_self (n + 1) 2
    show (2 * ((ordCompl[2] (n + 1) - 1) / 2) + 1) *
      2 ^ ((n + 1).factorization 2) - 1 = n
    exact Nat.sub_eq_of_eq_add key

/-- The encoding map of `oddTwoPowEquiv`, unfolded. -/
theorem oddTwoPowEquiv_apply (p : ℕ × ℕ) :
    oddTwoPowEquiv p = (2 * p.1 + 1) * 2 ^ p.2 - 1 := rfl

/-- The encoding map of `oddTwoPowEquiv`, shifted back up: the pair `(k, j)`
names the positive integer `(2k+1)·2^j`. -/
theorem oddTwoPowEquiv_apply_add_one (p : ℕ × ℕ) :
    oddTwoPowEquiv p + 1 = (2 * p.1 + 1) * 2 ^ p.2 := by
  have hpos : 0 < (2 * p.1 + 1) * 2 ^ p.2 := by positivity
  show (2 * p.1 + 1) * 2 ^ p.2 - 1 + 1 = (2 * p.1 + 1) * 2 ^ p.2
  omega

/-! ## Absolute convergence of the double family -/

/-- **Norm-summability of the double family** `(k, j) ↦ q^((2k+1)·2^j)` on
the open unit disc.  The exponent dominates `k + j`, because `2^j ≥ j + 1`
and `2k + 1 ≥ k + 1`, so the norms are dominated termwise by the product of
two geometric series. -/
theorem summable_norm_pow_odd_mul_two_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun p : ℕ × ℕ => ‖q ^ ((2 * p.1 + 1) * 2 ^ p.2)‖ := by
  have hgeom : Summable fun k : ℕ => ‖q‖ ^ k :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  have hprod : Summable fun p : ℕ × ℕ => ‖q‖ ^ p.1 * ‖q‖ ^ p.2 :=
    hgeom.mul_of_nonneg hgeom (fun _ => by positivity) (fun _ => by positivity)
  refine hprod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
  obtain ⟨k, j⟩ := p
  have hj : j < 2 ^ j := Nat.lt_two_pow_self
  have hmul : (k + 1) * (j + 1) ≤ (2 * k + 1) * 2 ^ j :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : k + j ≤ (2 * k + 1) * 2 ^ j := by
    have hring : (k + 1) * (j + 1) = k * j + k + j + 1 := by ring
    omega
  show ‖q ^ ((2 * k + 1) * 2 ^ j)‖ ≤ ‖q‖ ^ k * ‖q‖ ^ j
  calc ‖q ^ ((2 * k + 1) * 2 ^ j)‖ = ‖q‖ ^ ((2 * k + 1) * 2 ^ j) := norm_pow q _
    _ ≤ ‖q‖ ^ (k + j) := pow_le_pow_of_le_one (norm_nonneg q) hq.le hexp
    _ = ‖q‖ ^ k * ‖q‖ ^ j := pow_add ‖q‖ k j

/-- **Multipliability of the double family** `(k, j) ↦ 1 - q^((2k+1)·2^j)`
on the open unit disc: the deviations from `1` are absolutely summable. -/
theorem multipliable_one_sub_pow_odd_mul_two_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun p : ℕ × ℕ => 1 - q ^ ((2 * p.1 + 1) * 2 ^ p.2) := by
  have hsum : Summable fun p : ℕ × ℕ => ‖-(q ^ ((2 * p.1 + 1) * 2 ^ p.2))‖ := by
    simpa only [norm_neg] using summable_norm_pow_odd_mul_two_pow hq
  exact (multipliable_one_add_of_summable hsum).congr fun _ => by ring

/-! ## The multiplicative dissection -/

/-- **The flattened double product**: for every `q : ℂ`,
`(q;q)_∞ = ∏'_{(k,j)} (1 - q^((2k+1)·2^j))`.

This is pure reindexing along `oddTwoPowEquiv`, so it needs no hypothesis on
`q`: transporting an unordered product along an equivalence is
unconditional, and both sides carry Mathlib's junk value `1` together when
the family fails to be multipliable. -/
theorem qPochhammerInfIn_self_eq_tprod_pair (q : ℂ) :
    qPochhammerInfIn q q =
      ∏' p : ℕ × ℕ, (1 - q ^ ((2 * p.1 + 1) * 2 ^ p.2)) := by
  have hshift : (∏' n : ℕ, (1 - q * q ^ n)) = ∏' n : ℕ, (1 - q ^ (n + 1)) :=
    tprod_congr fun n => by rw [pow_succ']
  have hreindex : (∏' p : ℕ × ℕ, (1 - q ^ (oddTwoPowEquiv p + 1))) =
      ∏' n : ℕ, (1 - q ^ (n + 1)) :=
    oddTwoPowEquiv.tprod_eq fun n : ℕ => 1 - q ^ (n + 1)
  have hfactor : (∏' p : ℕ × ℕ, (1 - q ^ (oddTwoPowEquiv p + 1))) =
      ∏' p : ℕ × ℕ, (1 - q ^ ((2 * p.1 + 1) * 2 ^ p.2)) :=
    tprod_congr fun p => by rw [oddTwoPowEquiv_apply_add_one]
  rw [qPochhammerInfIn_eq_tprod, hshift, ← hreindex, hfactor]

/-- **The odd-part-first grouping**: for `‖q‖ < 1`,
`(q;q)_∞ = ∏'_k ∏'_j (1 - (q^(2k+1))^(2^j))`.

Each inner product is the lacunary Thue–Morse product at the nome
`q^(2k+1)`.  This is the multiplicative counterpart of the additive
residue-class dissection `qPochhammerInfIn_dissection`. -/
theorem qPochhammerInfIn_self_eq_tprod_lacunary {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q =
      ∏' k : ℕ, ∏' j : ℕ, (1 - (q ^ (2 * k + 1)) ^ (2 ^ j)) := by
  have hinner : ∀ k : ℕ, Multipliable fun j : ℕ => 1 - q ^ ((2 * k + 1) * 2 ^ j) := by
    intro k
    have hnorm : ‖q ^ (2 * k + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
    refine (multipliable_one_sub_pow_two_pow_complex hnorm).congr fun j => ?_
    rw [← pow_mul]
  have hsplit : (∏' p : ℕ × ℕ, (1 - q ^ ((2 * p.1 + 1) * 2 ^ p.2))) =
      ∏' k : ℕ, ∏' j : ℕ, (1 - q ^ ((2 * k + 1) * 2 ^ j)) :=
    (multipliable_one_sub_pow_odd_mul_two_pow hq).tprod_prod' hinner
  rw [qPochhammerInfIn_self_eq_tprod_pair q, hsplit]
  exact tprod_congr fun k => tprod_congr fun j => by rw [← pow_mul]

end Fabius
