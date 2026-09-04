import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.GroupTheory.Perm.Support
import FabiusFunction.BellStirling

/-!
# Three Stirling-number identities: fixed points, a first-kind double sum, and reduced triangles

This module formalizes material from the manuscript *Combinatorial Coefficient
Calculus* (`docs/semi-formalized-research-frontiers/drafts/`
`combinatorial-coefficient-calculus/`), namely the three results labelled

* `thm:fixed-point-stirling-moments` — *Moments of the number of fixed points*;
* `thm:first-double-sum` — *Explicit first-kind double sum*;
* `thm:reduced-stirling` — *Reduction formula* for the reduced Stirling numbers.

Everything is built on `Nat.stirlingSecond`, `Nat.stirlingFirst` and the
factorial-basis machinery of `StirlingBasisChange`; nothing here re-proves a
basis change or an explicit formula.

## 1. Moments of the number of fixed points (`thm:fixed-point-stirling-moments`)

The manuscript states `E[Y_m^n] = ∑_{k ≤ m} S(n,k) = ∑_{k ≤ min(m,n)} S(n,k)`
for the number `Y_m` of fixed points of a uniform random permutation of `[m]`.
The formalization replaces the probability space by the counting measure and is
therefore *division free*:

`∑_{σ : Perm α} #Fix(σ)^n = (#α)! · ∑_{k ≤ min(#α, n)} S(n,k)`
(`sum_card_fixedPointsFinset_pow`),

with the upper-limit-`m` variant (`sum_card_fixedPointsFinset_pow_eq_sum_range`),
the Bell specialization for `n ≤ #α` (`sum_card_fixedPointsFinset_pow_eq_bell`)
and the expectation itself over `ℚ`
(`expectation_card_fixedPointsFinset_pow`) as corollaries.  Writing the identity
without dividing by `m!` shows that no hypothesis at all is needed: the statement
holds for every finite type, including `#α = 0`, and for `n = 0`.

The whole permutation input is one count,
`#{σ : ∀ a ∈ s, σ a = a} = (#α - #s)!` (`card_perm_fixing_eq_factorial`), proved
from Mathlib's `Equiv.Perm.subtypeEquivSubtypePerm`.  The manuscript's
factorial-moment step `E[(Y_m)_k] = 1` becomes the double count
`∑_σ C(#Fix σ, k) = C(#α,k)·(#α-k)!` (`sum_choose_card_fixedPointsFinset`), which
is `Finset.sum_comm` applied to the incidence "a `k`-subset `s` is fixed
pointwise by `σ`" — the ordered `k`-tuples of the manuscript are replaced by
`k`-subsets, which removes the `k!` from both sides of the count.

## 2. The explicit first-kind double sum (`thm:first-double-sum`)

The manuscript's proof substitutes the second-kind inclusion–exclusion formula
into the symmetric cross-formula `eq:symmetric-cross1` (Schlömilch's formula).
Only the *substitution* is formalized here:

`firstDoubleSumInner n k j = (-1)^(j-k) · S(j-k, j-n)`
(`firstDoubleSumInner_eq_stirlingSecond`), hence

`∑_j C(j-1,k-1) C(2n-k,j) · inner(j) = ∑_j (-1)^{j-k} C(j-1,k-1) C(2n-k,j) S(j-k,j-n)`
(`firstDoubleSum_eq_crossSum`),

together with the diagonal instance `k = n`, where the right-hand side collapses
to `c(n,n) = 1` and the manuscript's theorem is therefore proved outright
(`firstDoubleSum_diagonal`).

**Not covered.**  The cross-formula `eq:symmetric-cross1` itself,
`c(n,k) = ∑_{j=n}^{2n-k} (-1)^{j-k} C(j-1,k-1) C(2n-k,j) S(j-k,j-n)`, is *not*
formalized: the manuscript proves it by the `ω`-involution on the ring of
symmetric functions, which the corpus does not have.  Consequently
`thm:first-double-sum` is formalized only modulo that one input (and outright at
`k = n`).  The identity itself was verified in exact rational arithmetic for
`1 ≤ k ≤ n ≤ 12`.

The formalization also settles the manuscript's parity bookkeeping: the two
exponents differ by `2(j-n-m)`, matching the editorial correction printed in the
source; the originally printed `2(j-m-n+k)` is wrong (it fails for `1080` of the
`1296` index triples with all indices below `6`).

## 3. Reduced Stirling numbers (`thm:reduced-stirling`)

Write `e = d-1` and `m = n-d+1`.  The analytic core of the manuscript's proof is
the polynomial identity

`(X)_e · (X - e)^m = ∑_{r ≤ m} S(m,r) · (X)_{r+e}`
(`descPochhammer_mul_sub_pow_eq_sum_stirlingSecond`, over an arbitrary
commutative ring), whose natural-number shadow is

`q^{\underline e} · (q-e)^m = ∑_{r ≤ m} S(m,r) · q^{\underline{r+e}}`
(`descFactorial_mul_pow_eq_sum_stirlingSecond`).

The reduction formula is then a *uniqueness* statement in the falling-factorial
basis, which is the form a downstream user needs: any sequence whose
falling-factorial expansion reproduces the chromatic polynomial
`(q)_{d-1}(q-d+1)^{n-d+1}` is forced to be `S(n-d+1, k-d+1)`
(`descFactorial_expansion_coeff_eq`, `reducedStirling_eq_stirlingSecond`).  The
uniqueness input is `eq_of_forall_sum_descFactorial_eq`, proved by triangularity
— evaluating at `q = 0,1,2,…` and cancelling `q!` — rather than by a
polynomial-roots argument.

**Not covered.**  The two combinatorial inputs are not formalized, because the
corpus has no set-partition or chromatic-polynomial layer: (i) that the
independent-set partitions of the graph `G_{n,d}` into `k` blocks are exactly the
partitions of `[n]` into `k` blocks with all within-block gaps `≥ d`, so that
`χ_{G_{n,d}}(q) = ∑_k S^{[d]}(n,k) (q)_k`; and (ii) the greedy count
`χ_{G_{n,d}}(q) = (q)_{d-1}(q-d+1)^{n-d+1}`.  Both were verified by brute force
(all `d ≤ 4`, `n ≤ 6`, `q ≤ 6`), as was `thm:reduced-stirling` itself by
enumerating set partitions for `d ≤ 5`, `n ≤ 9`.

One thing the formalization exposes: the coefficient statement is true one step
below the manuscript's range.  The manuscript assumes `n ≥ k ≥ d`, but the
`k = d-1` coefficient is also determined, and equals `S(n-d+1, 0)`, i.e. `0`
unless `n = d-1`.  The manuscript's index `k-d+1` may not be used there, since in
`ℕ` one has `(d-1) - d + 1 = 1 ≠ 0 = (d-1) - (d-1)`; the shifted index `k - e` is
the robust one.

## Main results

* `card_perm_fixing_eq_factorial`, `sum_choose_card_fixedPointsFinset`,
  `sum_descFactorial_card_fixedPointsFinset`.
* `sum_card_fixedPointsFinset_pow`, `sum_card_fixedPointsFinset_pow_eq_sum_range`,
  `sum_card_fixedPointsFinset_pow_eq_bell`,
  `expectation_card_fixedPointsFinset_pow`.
* `firstDoubleSumInner_eq_stirlingSecond`, `firstDoubleSum_eq_crossSum`,
  `firstDoubleSum_diagonal`.
* `descPochhammer_mul_sub_pow_eq_sum_stirlingSecond`,
  `descFactorial_mul_pow_eq_sum_stirlingSecond`,
  `eq_of_forall_sum_descFactorial_eq`, `descFactorial_expansion_coeff_eq`,
  `reducedStirling_eq_stirlingSecond`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-! ### Moments of the number of fixed points -/

section FixedPoints

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The fixed points of a permutation, as a `Finset`.  This is the complement of
Mathlib's `Equiv.Perm.support` (see `fixedPointsFinset_eq_support_compl`); the
positive form is the one the counting arguments below use. -/
def fixedPointsFinset (σ : Equiv.Perm α) : Finset α :=
  Finset.univ.filter fun x => σ x = x

/-- Membership in `fixedPointsFinset` is being a fixed point. -/
@[simp] theorem mem_fixedPointsFinset {σ : Equiv.Perm α} {a : α} :
    a ∈ fixedPointsFinset σ ↔ σ a = a := by
  simp [fixedPointsFinset]

/-- The fixed-point set is the complement of Mathlib's `Equiv.Perm.support`. -/
theorem fixedPointsFinset_eq_support_compl (σ : Equiv.Perm α) :
    fixedPointsFinset σ = σ.supportᶜ := by
  ext a
  simp [Equiv.Perm.mem_support]

/-- The permutations fixing a given `Finset` pointwise are the permutations of its
complement: there are `(#α - #s)!` of them.  This is the only fact about
permutations that the fixed-point moment identity needs. -/
theorem card_perm_fixing_eq_factorial (s : Finset α) :
    (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ a ∈ s, σ a = a)).card
      = (Fintype.card α - s.card).factorial := by
  have hequiv : {σ : Equiv.Perm α // ∀ a ∈ s, σ a = a} ≃ Equiv.Perm {x : α // x ∉ s} :=
    (Equiv.subtypeEquivRight (fun σ : Equiv.Perm α =>
        ⟨fun h a ha => h a (not_not.mp ha), fun h a ha => h a (not_not.mpr ha)⟩)).trans
      (Equiv.Perm.subtypeEquivSubtypePerm (fun x : α => x ∉ s)).symm
  calc (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ a ∈ s, σ a = a)).card
      = Fintype.card {σ : Equiv.Perm α // ∀ a ∈ s, σ a = a} := (Fintype.card_subtype _).symm
    _ = Fintype.card (Equiv.Perm {x : α // x ∉ s}) := Fintype.card_congr hequiv
    _ = (Fintype.card {x : α // x ∉ s}).factorial := Fintype.card_perm
    _ = (Fintype.card α - s.card).factorial := by
        rw [Fintype.card_subtype_compl (fun x : α => x ∈ s), Fintype.card_coe]

/-- **The binomial factorial moment.**  Counting pairs `(σ, s)` with `s` a
`k`-subset fixed pointwise by `σ` in the two possible orders gives
`∑_σ C(#Fix σ, k) = C(#α, k) · (#α - k)!`.  This is the manuscript's step
`E[(Y_m)_k] = 1`, with `k`-subsets in place of ordered `k`-tuples. -/
theorem sum_choose_card_fixedPointsFinset (k : ℕ) :
    ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card.choose k
      = (Fintype.card α).choose k * (Fintype.card α - k).factorial := by
  have step1 : ∀ σ : Equiv.Perm α,
      (fixedPointsFinset σ).card.choose k
        = ((Finset.powersetCard k (Finset.univ : Finset α)).filter
            (fun t => ∀ a ∈ t, σ a = a)).card := by
    intro σ
    rw [← Finset.card_powersetCard k (fixedPointsFinset σ)]
    congr 1
    ext t
    constructor
    · intro ht
      rw [Finset.mem_powersetCard] at ht
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ t, ht.2⟩, fun a ha => mem_fixedPointsFinset.mp (ht.1 ha)⟩
    · intro ht
      rw [Finset.mem_filter, Finset.mem_powersetCard] at ht
      rw [Finset.mem_powersetCard]
      exact ⟨fun a ha => mem_fixedPointsFinset.mpr (ht.2 a ha), ht.1.2⟩
  calc ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card.choose k
      = ∑ σ : Equiv.Perm α,
          ((Finset.powersetCard k (Finset.univ : Finset α)).filter
            (fun t => ∀ a ∈ t, σ a = a)).card := Finset.sum_congr rfl fun σ _ => step1 σ
    _ = ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset α),
          (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ a ∈ t, σ a = a)).card := by
        simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact Finset.sum_comm
    _ = ∑ _t ∈ Finset.powersetCard k (Finset.univ : Finset α),
          (Fintype.card α - k).factorial := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mem_powersetCard] at ht
        rw [card_perm_fixing_eq_factorial, ht.2]
    _ = (Fintype.card α).choose k * (Fintype.card α - k).factorial := by
        simp [Finset.card_powersetCard]

/-- **The falling factorial moment.**  `∑_σ (#Fix σ)^{\underline k} = (#α)!` when
`k ≤ #α`, and `0` otherwise — the manuscript's `E[(Y_m)_k] = 1` for `k ≤ m` and
`0` for `k > m`, multiplied by `m!`. -/
theorem sum_descFactorial_card_fixedPointsFinset (k : ℕ) :
    ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card.descFactorial k
      = if k ≤ Fintype.card α then (Fintype.card α).factorial else 0 := by
  have h : ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card.descFactorial k
      = k.factorial * ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card.choose k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Nat.descFactorial_eq_factorial_mul_choose _ _
  rw [h, sum_choose_card_fixedPointsFinset]
  by_cases hk : k ≤ Fintype.card α
  · rw [if_pos hk]
    calc k.factorial * ((Fintype.card α).choose k * (Fintype.card α - k).factorial)
        = (Fintype.card α).choose k * k.factorial * (Fintype.card α - k).factorial := by ring
      _ = (Fintype.card α).factorial := Nat.choose_mul_factorial_mul_factorial hk
  · rw [if_neg hk, Nat.choose_eq_zero_of_lt (by omega), zero_mul, mul_zero]

/-- **Moments of the number of fixed points** (`thm:fixed-point-stirling-moments`),
in division-free form: summing the `n`-th power of the number of fixed points over
all permutations of a finite type gives

`∑_σ (#Fix σ)^n = (#α)! · ∑_{k ≤ min(#α, n)} S(n,k)`.

No hypothesis is needed; `#α = 0` and `n = 0` are included. -/
theorem sum_card_fixedPointsFinset_pow (n : ℕ) :
    ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card ^ n
      = (Fintype.card α).factorial *
          ∑ k ∈ Finset.range (min (Fintype.card α) n + 1), Nat.stirlingSecond n k := by
  have h1 : ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card ^ n
      = ∑ k ∈ Finset.range (n + 1),
          Nat.stirlingSecond n k *
            (if k ≤ Fintype.card α then (Fintype.card α).factorial else 0) := by
    calc ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card ^ n
        = ∑ σ : Equiv.Perm α, ∑ k ∈ Finset.range (n + 1),
            Nat.stirlingSecond n k * (fixedPointsFinset σ).card.descFactorial k :=
          Finset.sum_congr rfl fun σ _ => pow_eq_sum_stirlingSecond_mul_descFactorial _ n
      _ = ∑ k ∈ Finset.range (n + 1), ∑ σ : Equiv.Perm α,
            Nat.stirlingSecond n k * (fixedPointsFinset σ).card.descFactorial k :=
          Finset.sum_comm
      _ = ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k *
            ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card.descFactorial k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range (n + 1),
            Nat.stirlingSecond n k *
              (if k ≤ Fintype.card α then (Fintype.card α).factorial else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_descFactorial_card_fixedPointsFinset]
  have h2 : ∑ k ∈ Finset.range (n + 1),
        Nat.stirlingSecond n k *
          (if k ≤ Fintype.card α then (Fintype.card α).factorial else 0)
      = ∑ k ∈ Finset.range (min (Fintype.card α) n + 1),
        Nat.stirlingSecond n k *
          (if k ≤ Fintype.card α then (Fintype.card α).factorial else 0) := by
    have hsub : Finset.range (min (Fintype.card α) n + 1) ⊆ Finset.range (n + 1) :=
      fun x hx => Finset.mem_range.mpr (by rw [Finset.mem_range] at hx; omega)
    refine (Finset.sum_subset hsub ?_).symm
    intro k hk hk'
    rw [Finset.mem_range] at hk
    rw [Finset.mem_range] at hk'
    rw [if_neg (show ¬ k ≤ Fintype.card α by omega), mul_zero]
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [if_pos (show k ≤ Fintype.card α by omega)]
  exact Nat.mul_comm _ _

/-- The same identity with the manuscript's first upper limit, `∑_{k ≤ #α} S(n,k)`:
the terms with `k > n` vanish, so the two forms agree. -/
theorem sum_card_fixedPointsFinset_pow_eq_sum_range (n : ℕ) :
    ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card ^ n
      = (Fintype.card α).factorial *
          ∑ k ∈ Finset.range (Fintype.card α + 1), Nat.stirlingSecond n k := by
  rw [sum_card_fixedPointsFinset_pow]
  congr 1
  by_cases h : Fintype.card α ≤ n
  · rw [min_eq_left h]
  · rw [min_eq_right (show n ≤ Fintype.card α by omega)]
    have hsub : Finset.range (n + 1) ⊆ Finset.range (Fintype.card α + 1) :=
      fun x hx => Finset.mem_range.mpr (by rw [Finset.mem_range] at hx; omega)
    refine Finset.sum_subset hsub ?_
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    exact Nat.stirlingSecond_eq_zero_of_lt (by omega)

/-- **The Bell specialization.**  When the permuted set is at least as large as the
moment order, the moment is the Bell number: `∑_σ (#Fix σ)^n = (#α)! · B(n)`. -/
theorem sum_card_fixedPointsFinset_pow_eq_bell {n : ℕ} (hn : n ≤ Fintype.card α) :
    ∑ σ : Equiv.Perm α, (fixedPointsFinset σ).card ^ n
      = (Fintype.card α).factorial * Nat.bell n := by
  rw [sum_card_fixedPointsFinset_pow, min_eq_right hn, bell_eq_sum_stirlingSecond]

/-- **The expectation form** of `thm:fixed-point-stirling-moments`: for the uniform
distribution on permutations of a finite type, the `n`-th moment of the number of
fixed points is `∑_{k ≤ min(#α,n)} S(n,k)`. -/
theorem expectation_card_fixedPointsFinset_pow (n : ℕ) :
    (∑ σ : Equiv.Perm α, ((fixedPointsFinset σ).card : ℚ) ^ n) / (Fintype.card α).factorial
      = ∑ k ∈ Finset.range (min (Fintype.card α) n + 1), (Nat.stirlingSecond n k : ℚ) := by
  have hne : (((Fintype.card α).factorial : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have h : (∑ σ : Equiv.Perm α, ((fixedPointsFinset σ).card : ℚ) ^ n)
      = ((Fintype.card α).factorial : ℚ) *
          ∑ k ∈ Finset.range (min (Fintype.card α) n + 1), (Nat.stirlingSecond n k : ℚ) := by
    exact_mod_cast sum_card_fixedPointsFinset_pow (α := α) n
  rw [h, mul_comm, mul_div_assoc, div_self hne, mul_one]

end FixedPoints

/-! ### The explicit first-kind double sum -/

/-- `1/(i!(b-i)!) = C(b,i)/b!` for `i ≤ b`: the elementary rewriting that turns the
manuscript's inner sum into the second-kind inclusion–exclusion formula. -/
theorem one_div_factorial_mul_factorial {b i : ℕ} (h : i ≤ b) :
    1 / ((i.factorial : ℚ) * ((b - i).factorial : ℚ)) = (b.choose i : ℚ) / (b.factorial : ℚ) := by
  have h1 : ((i.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos i).ne'
  have h2 : (((b - i).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos (b - i)).ne'
  have hb : ((b.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos b).ne'
  have hkey : ((b.choose i : ℚ)) * (i.factorial : ℚ) * ((b - i).factorial : ℚ)
      = (b.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  rw [div_eq_div_iff (mul_ne_zero h1 h2) hb, one_mul, ← hkey]
  ring

/-- The inner sum of the manuscript's double sum `eq:first-double-sum`,

`∑_{m=0}^{j-n} (-1)^{m+n-k} m^{j-k} / (m! (j-n-m)!)`.

It is written exactly as printed; the truncated subtraction in the exponent is
harmless because the identities below assume `k ≤ n ≤ j`. -/
def firstDoubleSumInner (n k j : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (j - n + 1),
    (-1 : ℚ) ^ (m + n - k) * (m : ℚ) ^ (j - k) /
      ((m.factorial : ℚ) * ((j - n - m).factorial : ℚ))

/-- **The inner sum is a signed Stirling number of the second kind:**
`inner(n,k,j) = (-1)^{j-k} S(j-k, j-n)` for `k ≤ n ≤ j`.  This is the content of
the manuscript's proof of `thm:first-double-sum`, including its sign bookkeeping:
the two exponents `2j-k-n-m` and `m+n-k` differ by the even number `2(j-n-m)`. -/
theorem firstDoubleSumInner_eq_stirlingSecond {n k j : ℕ} (hk : k ≤ n) (hj : n ≤ j) :
    firstDoubleSumInner n k j
      = (-1 : ℚ) ^ (j - k) * (Nat.stirlingSecond (j - k) (j - n) : ℚ) := by
  rw [firstDoubleSumInner, stirlingSecond_eq_sum_div_factorial, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hib : i ≤ j - n := by omega
  have hexp : (j - k) + (j - n - i) = (i + n - k) + 2 * (j - n - i) := by omega
  have hsign : (-1 : ℚ) ^ (j - k) * (-1 : ℚ) ^ (j - n - i) = (-1 : ℚ) ^ (i + n - k) := by
    rw [← pow_add, hexp, pow_add, pow_mul]
    norm_num
  rw [div_eq_mul_one_div, one_div_factorial_mul_factorial hib, ← hsign]
  ring

/-- **The manuscript's double sum is the symmetric cross-sum.**  Substituting the
second-kind inclusion–exclusion formula into `eq:symmetric-cross1` gives back the
cross-sum; this is the entire proof of `thm:first-double-sum`.  What remains
unformalized is the cross-formula `eq:symmetric-cross1` itself, i.e. that the
right-hand side below equals `c(n,k)`. -/
theorem firstDoubleSum_eq_crossSum {n k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ Finset.Icc n (2 * n - k),
        (Nat.choose (j - 1) (k - 1) : ℚ) * (Nat.choose (2 * n - k) j : ℚ)
          * firstDoubleSumInner n k j
      = ∑ j ∈ Finset.Icc n (2 * n - k),
        (-1 : ℚ) ^ (j - k) * (Nat.choose (j - 1) (k - 1) : ℚ)
          * (Nat.choose (2 * n - k) j : ℚ) * (Nat.stirlingSecond (j - k) (j - n) : ℚ) := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [firstDoubleSumInner_eq_stirlingSecond hk hj.1]
  ring

/-- **The diagonal case `k = n` of `thm:first-double-sum`, proved outright.**  The
summation range collapses to the single index `j = n`, the inner sum is `1`, and
the double sum returns `c(n,n) = 1`.  This is the one instance of the theorem that
does not need the unformalized cross-formula. -/
theorem firstDoubleSum_diagonal (n : ℕ) :
    ∑ j ∈ Finset.Icc n (2 * n - n),
        (Nat.choose (j - 1) (n - 1) : ℚ) * (Nat.choose (2 * n - n) j : ℚ)
          * firstDoubleSumInner n n j
      = (Nat.stirlingFirst n n : ℚ) := by
  have h : 2 * n - n = n := by omega
  have h0 : firstDoubleSumInner n n n = 1 := by
    rw [firstDoubleSumInner]
    simp
  rw [h, Finset.Icc_self, Finset.sum_singleton, h0, Nat.stirlingFirst_self,
    Nat.choose_self, Nat.choose_self]
  norm_num

/-! ### Reduced Stirling numbers and the falling-factorial basis -/

/-- **The chromatic core of `thm:reduced-stirling`, as a polynomial identity over
an arbitrary commutative ring:** `(X)_e (X - e)^m = ∑_{r ≤ m} S(m,r) (X)_{r+e}`.
It is the second-kind basis change composed with the shift `X ↦ X - e`, followed
by the splitting `(X)_e · (X-e)_r = (X)_{e+r}` of a falling factorial. -/
theorem descPochhammer_mul_sub_pow_eq_sum_stirlingSecond (R : Type*) [CommRing R] (e m : ℕ) :
    descPochhammer R e * ((X : R[X]) - (e : R[X])) ^ m
      = ∑ r ∈ Finset.range (m + 1),
          (Nat.stirlingSecond m r : R[X]) * descPochhammer R (r + e) := by
  have hcomp : ((X : R[X]) ^ m).comp ((X : R[X]) - (e : R[X]))
      = ((X : R[X]) - (e : R[X])) ^ m := by
    rw [Polynomial.pow_comp, Polynomial.X_comp]
  have h2 : ((X : R[X]) - (e : R[X])) ^ m
      = ∑ r ∈ Finset.range (m + 1),
          (Nat.stirlingSecond m r : R[X]) *
            (descPochhammer R r).comp ((X : R[X]) - (e : R[X])) := by
    rw [← hcomp, X_pow_eq_sum_stirlingSecond_mul_descPochhammer R m, finsetSum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Polynomial.mul_comp, Polynomial.natCast_comp]
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_left_comm, descPochhammer_mul, Nat.add_comm e r]

/-- The natural-number shadow of the chromatic core:
`q^{\underline e} (q-e)^m = ∑_{r ≤ m} S(m,r) q^{\underline{r+e}}`, valid for all
`q, e, m`, including `q < e` where both sides vanish.  Proved from the
falling-factorial expansion of a power together with Mathlib's splitting
`Nat.descFactorial_mul_descFactorial`; no ring or subtraction hypothesis is used. -/
theorem descFactorial_mul_pow_eq_sum_stirlingSecond (q e m : ℕ) :
    q.descFactorial e * (q - e) ^ m
      = ∑ r ∈ Finset.range (m + 1), Nat.stirlingSecond m r * q.descFactorial (r + e) := by
  rw [pow_eq_sum_stirlingSecond_mul_descFactorial (q - e) m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hsplit := Nat.descFactorial_mul_descFactorial
    (k := e) (m := r + e) (n := q) (Nat.le_add_left e r)
  rw [Nat.add_sub_cancel] at hsplit
  rw [← hsplit]
  ring

/-- **Uniqueness of falling-factorial coordinates.**  Two finitely supported
sequences whose falling-factorial expansions agree at every natural number agree
term by term.  The proof is triangular rather than analytic: evaluating at
`q = 0, 1, 2, …` kills every term of index `> q`, and the diagonal term carries
the invertible factor `q!`. -/
theorem eq_of_forall_sum_descFactorial_eq {N : ℕ} (a b : ℕ → ℤ)
    (h : ∀ q : ℕ, ∑ i ∈ Finset.range (N + 1), a i * (q.descFactorial i : ℤ)
        = ∑ i ∈ Finset.range (N + 1), b i * (q.descFactorial i : ℤ)) :
    ∀ k ≤ N, a k = b k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hcut : ∀ c : ℕ → ℤ, ∑ i ∈ Finset.range (N + 1), c i * (k.descFactorial i : ℤ)
        = ∑ i ∈ Finset.range (k + 1), c i * (k.descFactorial i : ℤ) := by
      intro c
      have hsub : Finset.range (k + 1) ⊆ Finset.range (N + 1) :=
        fun x hx => Finset.mem_range.mpr (by rw [Finset.mem_range] at hx; omega)
      refine (Finset.sum_subset hsub ?_).symm
      intro i _ hi
      rw [Finset.mem_range, not_lt] at hi
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, mul_zero]
    have h' := h k
    rw [hcut a, hcut b, Finset.sum_range_succ, Finset.sum_range_succ] at h'
    have hlow : ∑ i ∈ Finset.range k, a i * (k.descFactorial i : ℤ)
        = ∑ i ∈ Finset.range k, b i * (k.descFactorial i : ℤ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [ih i hi (by omega)]
    rw [hlow, Nat.descFactorial_self] at h'
    have hfac : ((k.factorial : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'
    exact mul_right_cancel₀ hfac (add_left_cancel h')

/-- **`thm:reduced-stirling` in coefficient form.**  If a sequence `a` expands the
chromatic polynomial `(q)_e (q-e)^m` in the falling-factorial basis, then its
coefficients are forced: `a k = S(m, k-e)` for `e ≤ k`, and `a k = 0` below.  With
`e = d-1`, `m = n-d+1` and `a k = S^{[d]}(n,k)` this is exactly the manuscript's
reduction formula; the combinatorial identification of the hypothesis is the part
that is not formalized. -/
theorem descFactorial_expansion_coeff_eq {e m : ℕ} (a : ℕ → ℤ)
    (hchrom : ∀ q : ℕ, ∑ i ∈ Finset.range (m + e + 1), a i * (q.descFactorial i : ℤ)
        = (q.descFactorial e : ℤ) * ((q - e : ℕ) : ℤ) ^ m) :
    ∀ k ≤ m + e, a k = if e ≤ k then (Nat.stirlingSecond m (k - e) : ℤ) else 0 := by
  have hb : ∀ q : ℕ, ∑ i ∈ Finset.range (m + e + 1),
      (if e ≤ i then (Nat.stirlingSecond m (i - e) : ℤ) else 0) * (q.descFactorial i : ℤ)
        = (q.descFactorial e : ℤ) * ((q - e : ℕ) : ℤ) ^ m := by
    intro q
    have hcast : ((q.descFactorial e * (q - e) ^ m : ℕ) : ℤ)
        = (q.descFactorial e : ℤ) * ((q - e : ℕ) : ℤ) ^ m := by
      rw [Nat.cast_mul, Nat.cast_pow]
    rw [← hcast, descFactorial_mul_pow_eq_sum_stirlingSecond q e m]
    push_cast
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le e) (show e ≤ m + e + 1 by omega)]
    have hlow : ∑ i ∈ Finset.Ico 0 e,
        (if e ≤ i then (Nat.stirlingSecond m (i - e) : ℤ) else 0) * (q.descFactorial i : ℤ)
          = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [if_neg (show ¬ e ≤ i by omega), zero_mul]
    rw [hlow, zero_add, Finset.sum_Ico_eq_sum_range, show m + e + 1 - e = m + 1 by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (Nat.le_add_right e i), Nat.add_sub_cancel_left, Nat.add_comm e i]
  have hmain := eq_of_forall_sum_descFactorial_eq (N := m + e) a
    (fun i => if e ≤ i then (Nat.stirlingSecond m (i - e) : ℤ) else 0)
    (fun q => (hchrom q).trans (hb q).symm)
  intro k hk
  exact hmain k hk

/-- **Reduction formula (`thm:reduced-stirling`), in the manuscript's indices.**
Let `1 ≤ d ≤ n` and let `a` expand the chromatic polynomial
`(q)_{d-1} (q-d+1)^{n-d+1}` of the `d`-th power of the path on `n` vertices in the
falling-factorial basis — for the reduced Stirling numbers this is
`χ_{G_{n,d}}(q) = ∑_k S^{[d]}(n,k) (q)_k`.  Then for `d ≤ k ≤ n`,

`a k = S(n-d+1, k-d+1)`,

which is `S^{[d]}(n,k) = S(n-d+1,k-d+1)`. -/
theorem reducedStirling_eq_stirlingSecond {n d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) (a : ℕ → ℤ)
    (hchrom : ∀ q : ℕ, ∑ i ∈ Finset.range (n + 1), a i * (q.descFactorial i : ℤ)
        = (q.descFactorial (d - 1) : ℤ) * ((q - (d - 1) : ℕ) : ℤ) ^ (n - d + 1)) :
    ∀ k, d ≤ k → k ≤ n → a k = (Nat.stirlingSecond (n - d + 1) (k - d + 1) : ℤ) := by
  intro k hk hkn
  have hme : n - d + 1 + (d - 1) = n := by omega
  have hcoeff := descFactorial_expansion_coeff_eq (e := d - 1) (m := n - d + 1) a
    (by intro q; rw [hme]; exact hchrom q)
  have hval := hcoeff k (by omega)
  rw [if_pos (show d - 1 ≤ k by omega)] at hval
  rw [hval, show k - (d - 1) = k - d + 1 by omega]

end Fabius
