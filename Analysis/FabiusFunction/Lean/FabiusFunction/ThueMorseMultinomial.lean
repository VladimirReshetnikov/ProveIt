import FabiusFunction.ThueMorseBooleanMobius
import FabiusFunction.ThueMorseDigits
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Odd multinomial coefficients and the exact `r`-nomial logarithm

The number of odd coefficients in `(x_1 + ⋯ + x_r)^n` is `r^wt(n)`.  This
module proves the atlas's multinomial layer — the last open discrete row
of its proposal table — by pure valuation arithmetic and the bivariate
submask enumerator; no polynomial rings appear.

The valuation half of the argument is Legendre's formula run twice and
subtracted, and nothing in it is special to the prime `2`.  It is
therefore carried out here for an arbitrary prime `p`, writing `S_p` for
the base-`p` digit sum, and the Thue--Morse statements are recovered as
the case `p = 2`, where `S_2 = wt` is the binary weight.

* `digitSum_add_sub_one_mul_padicValNat_factorial` — the **additive
  Legendre formula in base `p`**: `S_p(n) + (p-1)·v_p(n!) = n`.
* `sum_digitSum_eq_sub_one_mul_padicValNat_multinomial` — **Legendre's
  formula for multinomials**: the digit sums of the parts exceed the
  digit sum of their total by exactly `(p-1)` times the valuation,
  `∑ S_p(k_i) = (p-1)·v_p(multinomial) + S_p(∑ k_i)`.
* `prime_not_dvd_multinomial_iff_digitSum` — **Kummer's criterion in base
  `p`**: `multinomial(n; k_1,…,k_r)` is prime to `p` exactly when the
  base-`p` digit sums are additive, `∑ S_p(k_i) = S_p(∑ k_i)` — that is,
  when the parts add without carrying in base `p`.
* `odd_multinomial_iff_binaryWeight` — **Kummer's criterion for
  multinomials**: the case `p = 2`.  A multinomial coefficient
  `multinomial(n; k_1,…,k_r)` is odd exactly when the binary weights are
  additive, `∑ wt(k_i) = wt(∑ k_i)` — that is, when the parts partition
  the binary digits of `n` without carries.  Stated for an arbitrary
  finite index set.
* `card_filter_odd_multinomial` — the **multinomial support count**
  `O_r(n) = r^wt(n)`: the odd positions of the `n`-th slice of the
  `r`-nomial Pascal pyramid number exactly `r^wt(n)`.  The induction on
  the index set splits off one part; the surviving inner sum is the
  bivariate submask enumerator at `(1, r)`.
* `sum_neg_one_pow_multinomial` — the **signed `r`-nomial row formula**:
  `∑_{k_1+⋯+k_r=n} (-1)^multinomial = #slice - 2·r^wt(n)`, where `#slice`
  is the number of positions in the `n`-th slice, i.e. of weak
  compositions of `n` into `r` parts.
* `thueMorseSign_eq_neg_one_pow_log_card` — the **exact `r`-nomial
  logarithm**: `ε(n) = (-1)^(log_r O_r(n))` for every base `r ≥ 2`, the
  logarithm exact.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The binary weight vanishes only at zero. -/
theorem binaryWeight_eq_zero_iff (n : ℕ) : binaryWeight n = 0 ↔ n = 0 := by
  rw [← card_bitSupport, Finset.card_eq_zero, bitSupport_eq_empty_iff]

/-! ## Legendre's formula in base `p` -/

/-- **Additive Legendre formula in base `p`.**  The base-`p` digit sum of
`n` and `(p - 1)` times the `p`-adic valuation of `n!` partition `n`
exactly: `S_p(n) + (p-1)·v_p(n!) = n`.  This is Mathlib's
`sub_one_mul_padicValNat_factorial` with the truncated subtraction
removed; at `p = 2` it is `binaryWeight_add_padicValNat_factorial`. -/
theorem digitSum_add_sub_one_mul_padicValNat_factorial (p : ℕ)
    [Fact p.Prime] (n : ℕ) :
    (Nat.digits p n).sum + (p - 1) * padicValNat p n.factorial = n := by
  rw [sub_one_mul_padicValNat_factorial (p := p) n]
  exact Nat.add_sub_cancel' (Nat.digit_sum_le p n)

/-- The `p`-adic valuation of a product of factorials splits over the
index set. -/
private theorem padicValNat_prod_factorial_prime {ι : Type*}
    [DecidableEq ι] (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ) :
    padicValNat p (∏ i ∈ s, (f i).factorial) =
      ∑ i ∈ s, padicValNat p (f i).factorial := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValNat.mul (p := p) (Nat.factorial_ne_zero _)
          (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _),
        ih]

/-- Arithmetic shim.  Subtracting two runs of Legendre's formula leaves a
pure cancellation: from `A' + X = N`, `A + Y = N` and `Y = X + Z` one
gets `A' = Z + A`, with `X`, `Y`, `Z` opaque products. -/
private theorem digitSum_cancel_aux {A A' N X Y Z : ℕ}
    (h₁ : A' + X = N) (h₂ : A + Y = N) (h₃ : Y = X + Z) : A' = Z + A := by
  omega

/-- Arithmetic shim.  For `q ≠ 0`, an identity `A = q * v + B` turns the
equality `A = B` into the vanishing of `v`. -/
private theorem digitSum_eq_iff_aux {q v A B : ℕ} (hq : q ≠ 0)
    (hid : A = q * v + B) : A = B ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    rw [Nat.mul_add, Nat.mul_one] at hid
    omega
  · rintro rfl
    simpa using hid

/-- **Legendre's formula for multinomial coefficients, base `p`.**  For a
prime `p` the base-`p` digit sums of the parts exceed the digit sum of
their total by exactly `(p - 1)` times the `p`-adic valuation of the
multinomial coefficient:
`∑_{i∈s} S_p(f i) = (p-1)·v_p(multinomial s f) + S_p(∑_{i∈s} f i)`. -/
theorem sum_digitSum_eq_sub_one_mul_padicValNat_multinomial {ι : Type*}
    [DecidableEq ι] (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ) :
    ∑ i ∈ s, (Nat.digits p (f i)).sum =
      (p - 1) * padicValNat p (Nat.multinomial s f) +
        (Nat.digits p (∑ i ∈ s, f i)).sum := by
  have hmultne : Nat.multinomial s f ≠ 0 := (Nat.multinomial_pos s f).ne'
  have hprodne : (∏ i ∈ s, (f i).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
  have hspec := Nat.multinomial_spec s f
  have hνmul : padicValNat p (∏ i ∈ s, (f i).factorial) +
      padicValNat p (Nat.multinomial s f) =
      padicValNat p ((∑ i ∈ s, f i).factorial) := by
    rw [← padicValNat.mul (p := p) hprodne hmultne, hspec]
  have hprodν := padicValNat_prod_factorial_prime p s f
  have hsumL : ∑ i ∈ s, (Nat.digits p (f i)).sum +
      (p - 1) * ∑ i ∈ s, padicValNat p (f i).factorial =
      ∑ i ∈ s, f i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      digitSum_add_sub_one_mul_padicValNat_factorial p (f i)
  have htotL :=
    digitSum_add_sub_one_mul_padicValNat_factorial p (∑ i ∈ s, f i)
  have hkey : (p - 1) * padicValNat p ((∑ i ∈ s, f i).factorial) =
      (p - 1) * ∑ i ∈ s, padicValNat p (f i).factorial +
        (p - 1) * padicValNat p (Nat.multinomial s f) := by
    rw [← hνmul, hprodν, Nat.mul_add]
  exact digitSum_cancel_aux hsumL htotL hkey

/-- **Kummer's criterion for multinomial coefficients, base `p`.**  A
multinomial coefficient is prime to `p` exactly when the base-`p` digit
sums of its parts are additive:
`¬ p ∣ multinomial s f ↔ ∑_{i∈s} S_p(f i) = S_p(∑_{i∈s} f i)` — the parts
add without carrying in base `p`. -/
theorem prime_not_dvd_multinomial_iff_digitSum {ι : Type*} [DecidableEq ι]
    (p : ℕ) [hp : Fact p.Prime] (s : Finset ι) (f : ι → ℕ) :
    ¬ p ∣ Nat.multinomial s f ↔
      ∑ i ∈ s, (Nat.digits p (f i)).sum =
        (Nat.digits p (∑ i ∈ s, f i)).sum := by
  have hmultne : Nat.multinomial s f ≠ 0 := (Nat.multinomial_pos s f).ne'
  have hid := sum_digitSum_eq_sub_one_mul_padicValNat_multinomial p s f
  have hq : p - 1 ≠ 0 := by
    have := hp.out.two_le
    omega
  rw [dvd_iff_padicValNat_ne_zero (p := p) hmultne, not_ne_iff]
  exact (digitSum_eq_iff_aux hq hid).symm

/-- **Kummer's criterion for multinomial coefficients.**  A multinomial
coefficient is odd exactly when the binary weights of its parts are
additive: `Odd (multinomial s f) ↔ ∑_{i∈s} wt(f i) = wt(∑_{i∈s} f i)` —
the parts partition the binary digits of the sum without carries.  This
is `prime_not_dvd_multinomial_iff_digitSum` at `p = 2`. -/
theorem odd_multinomial_iff_binaryWeight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) :
    Odd (Nat.multinomial s f) ↔
      ∑ i ∈ s, binaryWeight (f i) = binaryWeight (∑ i ∈ s, f i) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbin : ∀ m : ℕ, binaryWeight m = (Nat.digits 2 m).sum :=
    fun _ => rfl
  simp only [hbin]
  rw [← prime_not_dvd_multinomial_iff_digitSum 2 s f, Nat.odd_iff,
    Nat.two_dvd_ne_zero]

/-! ## The multinomial support count -/

/-- A point of `Finset.finsuppAntidiag s n` vanishes off `s`: if `a ∉ s`
then every such `g` has `g a = 0`.  Extracted from the induction step of
`card_filter_odd_multinomial`, where the fact was derived inline. -/
private theorem apply_eq_zero_of_mem_finsuppAntidiag {ι : Type*}
    [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∉ s) {n : ℕ}
    {g : ι →₀ ℕ} (hg : g ∈ Finset.finsuppAntidiag s n) : g a = 0 := by
  by_contra hne
  exact ha ((Finset.mem_finsuppAntidiag.mp hg).2
    (Finsupp.mem_support_iff.mpr hne))

/-- **Multinomial support count**: the odd coefficients in the `n`-th
slice of the Pascal pyramid on the index set `s` number exactly
`(#s)^wt(n)` (atlas: `O_r(n) = r^wt(n)`). -/
theorem card_filter_odd_multinomial {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ℕ) :
    ((Finset.finsuppAntidiag s n).filter
        (fun f : ι →₀ ℕ => Odd (Nat.multinomial s ⇑f))).card =
      s.card ^ binaryWeight n := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
      rw [Finset.finsuppAntidiag_empty]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [if_pos rfl]
        rw [show binaryWeight 0 = 0 from (binaryWeight_eq_zero_iff 0).mpr rfl]
        simp [Nat.multinomial]
      · rw [if_neg (by omega)]
        have hwt : binaryWeight n ≠ 0 := fun h =>
          (by omega : n ≠ 0) ((binaryWeight_eq_zero_iff n).mp h)
        simp [zero_pow hwt]
  | insert a s ha ih =>
      classical
      have hpart : (Finset.finsuppAntidiag (insert a s) n).filter
          (fun f : ι →₀ ℕ => Odd (Nat.multinomial (insert a s) ⇑f)) =
          (oddBinomialIndices n).biUnion (fun k =>
            ((Finset.finsuppAntidiag s (n - k)).filter
                (fun g : ι →₀ ℕ => Odd (Nat.multinomial s ⇑g))).image
              (fun g => Finsupp.update g a k)) := by
        ext F
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨hFmem, hFodd⟩
          obtain ⟨m, hm, g, rfl, hg⟩ :=
            (Finset.mem_finsuppAntidiag_insert ha n).mp hFmem
          have hmsum := Finset.mem_antidiagonal.mp hm
          have hFa : (Finsupp.update g a m.1) a = m.1 := by
            simp
          have hFs : ∀ i ∈ s, (Finsupp.update g a m.1) i = g i := by
            intro i hi
            have hne : i ≠ a := fun h => ha (h ▸ hi)
            rw [Finsupp.coe_update, Function.update_of_ne hne]
          have hsum : ∑ i ∈ s, (Finsupp.update g a m.1) i = m.2 := by
            rw [Finset.sum_congr rfl hFs]
            exact (Finset.mem_finsuppAntidiag.mp hg).1
          rw [Nat.multinomial_insert ha, Nat.odd_mul] at hFodd
          rw [hFa, hsum, hmsum] at hFodd
          refine ⟨m.1, ?_, g, ⟨?_, ?_⟩, rfl⟩
          · rw [oddBinomialIndices, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hFodd.1⟩
          · rw [show n - m.1 = m.2 by omega]
            exact hg
          · have := hFodd.2
            rwa [Nat.multinomial_congr hFs] at this
        · rintro ⟨k, hk, g, ⟨hg, hgodd⟩, rfl⟩
          have hkmem := Finset.mem_filter.mp
            (by rwa [oddBinomialIndices] at hk)
          have hkn : k ≤ n := by
            have := Finset.mem_range.mp hkmem.1
            omega
          have hFa : (Finsupp.update g a k) a = k := by
            simp
          have hFs : ∀ i ∈ s, (Finsupp.update g a k) i = g i := by
            intro i hi
            have hne : i ≠ a := fun h => ha (h ▸ hi)
            rw [Finsupp.coe_update, Function.update_of_ne hne]
          have hsum : ∑ i ∈ s, (Finsupp.update g a k) i = n - k := by
            rw [Finset.sum_congr rfl hFs]
            exact (Finset.mem_finsuppAntidiag.mp hg).1
          constructor
          · refine (Finset.mem_finsuppAntidiag_insert ha n).mpr
              ⟨(k, n - k), Finset.mem_antidiagonal.mpr (by omega), g,
                rfl, ?_⟩
            exact hg
          · rw [Nat.multinomial_insert ha, Nat.odd_mul, hFa, hsum,
              show k + (n - k) = n by omega,
              Nat.multinomial_congr hFs]
            exact ⟨hkmem.2, hgodd⟩
      rw [hpart]
      rw [Finset.card_biUnion]
      · have hterm : ∀ k ∈ oddBinomialIndices n,
            (((Finset.finsuppAntidiag s (n - k)).filter
                (fun g : ι →₀ ℕ => Odd (Nat.multinomial s ⇑g))).image
              (fun g => Finsupp.update g a k)).card =
            s.card ^ binaryWeight (n - k) := by
          intro k _
          rw [Finset.card_image_of_injOn, ih]
          intro g₁ h₁ g₂ h₂ h
          have hga : ∀ g ∈ (Finset.finsuppAntidiag s (n - k)).filter
              (fun g : ι →₀ ℕ => Odd (Nat.multinomial s ⇑g)), g a = 0 :=
            fun g hgm => apply_eq_zero_of_mem_finsuppAntidiag ha
              (Finset.mem_filter.mp hgm).1
          ext i
          by_cases hia : i = a
          · rw [hia, hga g₁ h₁, hga g₂ h₂]
          · have h' := congrArg (fun F => F i) h
            simp only [Finsupp.coe_update] at h'
            rwa [Function.update_of_ne hia, Function.update_of_ne hia] at h'
        rw [Finset.sum_congr rfl hterm]
        have hbiv := sum_oddBinomialIndices_pow_pow n 1 (s.card : ℕ)
        simp only [one_pow, one_mul] at hbiv
        rw [hbiv, Finset.card_insert_of_notMem ha]
        ring_nf
      · intro k₁ h₁ k₂ h₂ hne
        simp only [Finset.disjoint_left, Finset.mem_image]
        rintro F ⟨g₁, _, rfl⟩ ⟨g₂, _, hFg⟩
        apply hne
        have h1 : (Finsupp.update g₁ a k₁) a = k₁ := by simp
        have h2 : (Finsupp.update g₂ a k₂) a = k₂ := by simp
        rw [← h1, ← hFg, h2]

/-- Generic signed count: over any finset,
`∑ (-1)^(g x) = #A - 2·#{x ∈ A : g x odd}`. -/
theorem sum_neg_one_pow_eq_card_sub_two_mul {α : Type*}
    (A : Finset α) (g : α → ℕ) :
    ∑ x ∈ A, (-1 : ℤ) ^ g x =
      (A.card : ℤ) - 2 * (A.filter (fun x => Odd (g x))).card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not A (fun x => Odd (g x))]
  have hodd : ∀ x ∈ A.filter (fun x => Odd (g x)), (-1 : ℤ) ^ g x = -1 := by
    intro x hx
    exact Odd.neg_one_pow (Finset.mem_filter.mp hx).2
  have heven : ∀ x ∈ A.filter (fun x => ¬ Odd (g x)),
      (-1 : ℤ) ^ g x = 1 := by
    intro x hx
    have := (Finset.mem_filter.mp hx).2
    rw [Nat.not_odd_iff_even] at this
    exact Even.neg_one_pow this
  rw [Finset.sum_congr rfl hodd, Finset.sum_congr rfl heven,
    Finset.sum_const, Finset.sum_const, Finset.filter_not,
    Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
  have hle := Finset.card_le_card
    (Finset.filter_subset (fun x => Odd (g x)) A)
  simp only [nsmul_eq_mul, mul_one, mul_neg_one]
  push_cast [hle]
  ring

/-- **Signed `r`-nomial row formula**: the signed sum of parities over the
`n`-th multinomial slice is the number of positions minus twice the odd
support, `∑ (-1)^multinomial = #slice - 2·(#s)^wt(n)`. -/
theorem sum_neg_one_pow_multinomial {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ℕ) :
    ∑ f ∈ Finset.finsuppAntidiag s n, (-1 : ℤ) ^ Nat.multinomial s ⇑f =
      ((Finset.finsuppAntidiag s n).card : ℤ) -
        2 * (s.card : ℤ) ^ binaryWeight n := by
  rw [sum_neg_one_pow_eq_card_sub_two_mul, card_filter_odd_multinomial]
  push_cast
  ring

/-- **The exact `r`-nomial logarithm**: `ε(n) = (-1)^(log_r O_r(n))` for
every base `r ≥ 2` — the number of odd `r`-nomial coefficients determines
the Thue–Morse sign through an exact logarithm. -/
theorem thueMorseSign_eq_neg_one_pow_log_card {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : 2 ≤ s.card) (n : ℕ) :
    thueMorseSign n =
      (-1) ^ Nat.log s.card
        ((Finset.finsuppAntidiag s n).filter
            (fun f : ι →₀ ℕ => Odd (Nat.multinomial s ⇑f))).card := by
  rw [card_filter_odd_multinomial, Nat.log_pow (by omega), thueMorseSign]

end Fabius
