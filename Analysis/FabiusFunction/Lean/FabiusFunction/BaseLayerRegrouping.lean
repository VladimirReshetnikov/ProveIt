import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.Multiplicity
import Mathlib.Order.Interval.Finset.Nat

/-!
# Regrouping a base-`b` layer product

Counting the multiples of `1, b, b², …` up to `N` layer by layer, and
regrouping by the multiple instead of by the layer:

`∏_{j≤J} ∏_{n≤N/bʲ} f(bʲ·n) = ∏_{m≤N} f(m)^{#{j≤J : bʲ ∣ m}}`.

Three choices of generality, each of which the frontier reports take in
a special case only:

* **no relation between `N` and `J`** — the exponent is the *truncated*
  layer count `#{j ≤ J : bʲ ∣ m}`.  The reports always assume
  `N < b^{J+1}`, which merely lets the count be evaluated; that
  evaluation is `card_filter_pow_dvd` below and is a separate step;
* **an arbitrary commutative monoid** and arbitrary `f`, with
  `@[to_additive]` supplying the sum form free.  The reports use the
  real multiplicative case;
* **an arbitrary base** `b`, via `multiplicity`.  `padicValNat` is
  gated on primality, so it cannot state the `b = 4, 6, 10` cases the
  reports need; `multiplicity` has no such restriction.

The proof is double counting and nothing else: rewrite the inner
product over `n` as a product over the multiples of `bʲ` in `[1,N]`,
turn both filters into `if`s, exchange the two products, and collapse
the constant inner product into a power.

* `prod_multiples_eq_prod_filter` — the layer reindexing.
* `prod_layers_eq_prod_pow_card` — **the regrouping**.
* `card_filter_pow_dvd` — the layer count is `ν_b(m)+1`.
* `prod_layers_eq_prod_pow_multiplicity` — the two combined.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The `q`-multiples of `[1,N]` are the image of `[1, N/q]` under
`n ↦ q·n`. -/
theorem filter_dvd_eq_image {N q : ℕ} (hq : 0 < q) :
    (Finset.Icc 1 N).filter (fun m => q ∣ m) =
      (Finset.Icc 1 (N / q)).image (fun n => q * n) := by
  classical
  ext m
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hm1, hmN⟩, hdvd⟩
    refine ⟨m / q, ⟨?_, ?_⟩, Nat.mul_div_cancel' hdvd⟩
    · exact (Nat.one_le_div_iff hq).mpr (Nat.le_of_dvd (by omega) hdvd)
    · exact Nat.div_le_div_right hmN
  · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, Dvd.intro n rfl⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
    · calc q * n = n * q := Nat.mul_comm q n
        _ ≤ N := (Nat.le_div_iff_mul_le hq).mp hn2

/-- **The layer reindexing**: the `q`-multiples of `[1,N]` are exactly
`q·n` for `1 ≤ n ≤ N/q`. -/
@[to_additive]
theorem prod_multiples_eq_prod_filter {M : Type*} [CommMonoid M]
    (f : ℕ → M) (N q : ℕ) (hq : 0 < q) :
    ∏ n ∈ Finset.Icc 1 (N / q), f (q * n) =
      ∏ m ∈ (Finset.Icc 1 N).filter (fun m => q ∣ m), f m := by
  classical
  rw [filter_dvd_eq_image hq, Finset.prod_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hq hab

/-- **The regrouping**: summing the layer products by multiple instead
of by layer replaces each `f m` by its layer multiplicity. -/
@[to_additive]
theorem prod_layers_eq_prod_pow_card {M : Type*} [CommMonoid M]
    (f : ℕ → M) (b N J : ℕ) (hb : 0 < b) :
    ∏ j ∈ Finset.range (J + 1), ∏ n ∈ Finset.Icc 1 (N / b ^ j),
        f (b ^ j * n) =
      ∏ m ∈ Finset.Icc 1 N,
        f m ^ ((Finset.range (J + 1)).filter
          (fun j => b ^ j ∣ m)).card := by
  classical
  have hpow : ∀ j : ℕ, 0 < b ^ j := fun j => pow_pos hb j
  calc ∏ j ∈ Finset.range (J + 1), ∏ n ∈ Finset.Icc 1 (N / b ^ j),
        f (b ^ j * n)
      = ∏ j ∈ Finset.range (J + 1),
          ∏ m ∈ (Finset.Icc 1 N).filter (fun m => b ^ j ∣ m), f m :=
        Finset.prod_congr rfl (fun j _ =>
          prod_multiples_eq_prod_filter f N (b ^ j) (hpow j))
    _ = ∏ j ∈ Finset.range (J + 1), ∏ m ∈ Finset.Icc 1 N,
          (if b ^ j ∣ m then f m else 1) :=
        Finset.prod_congr rfl (fun j _ => Finset.prod_filter _ _)
    _ = ∏ m ∈ Finset.Icc 1 N, ∏ j ∈ Finset.range (J + 1),
          (if b ^ j ∣ m then f m else 1) := Finset.prod_comm
    _ = ∏ m ∈ Finset.Icc 1 N,
          f m ^ ((Finset.range (J + 1)).filter
            (fun j => b ^ j ∣ m)).card := by
        refine Finset.prod_congr rfl (fun m _ => ?_)
        rw [← Finset.prod_filter (p := fun j => b ^ j ∣ m)
          (f := fun _ => f m), Finset.prod_const]

/-- **The layer count**: for `1 < b` and `m ≠ 0`, the layers dividing
`m` are exactly `j ≤ ν_b(m)`, so a range containing them all counts
`ν_b(m)+1` of them. -/
theorem card_filter_pow_dvd {b m J : ℕ} (hb : 1 < b) (hm : m ≠ 0)
    (hJ : multiplicity b m ≤ J) :
    ((Finset.range (J + 1)).filter (fun j => b ^ j ∣ m)).card =
      multiplicity b m + 1 := by
  classical
  have hfin : FiniteMultiplicity b m :=
    Nat.finiteMultiplicity_iff.mpr ⟨by omega, Nat.pos_of_ne_zero hm⟩
  have hset : (Finset.range (J + 1)).filter (fun j => b ^ j ∣ m) =
      Finset.range (multiplicity b m + 1) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range,
      hfin.pow_dvd_iff_le_multiplicity]
    omega
  rw [hset, Finset.card_range]

/-- **The regrouping in valuation form**: when the layer range reaches
`ν_b(m)` for every `m ≤ N` — for instance when `N < b^{J+1}` — the
exponent is exactly `ν_b(m)+1`. -/
@[to_additive]
theorem prod_layers_eq_prod_pow_multiplicity {M : Type*} [CommMonoid M]
    (f : ℕ → M) (b N J : ℕ) (hb : 1 < b)
    (hJ : ∀ m ∈ Finset.Icc 1 N, multiplicity b m ≤ J) :
    ∏ j ∈ Finset.range (J + 1), ∏ n ∈ Finset.Icc 1 (N / b ^ j),
        f (b ^ j * n) =
      ∏ m ∈ Finset.Icc 1 N, f m ^ (multiplicity b m + 1) := by
  classical
  rw [prod_layers_eq_prod_pow_card f b N J (by omega)]
  refine Finset.prod_congr rfl (fun m hm => ?_)
  have hm0 : m ≠ 0 := by
    rw [Finset.mem_Icc] at hm
    omega
  rw [card_filter_pow_dvd hb hm0 (hJ m hm)]

end Fabius
