import FabiusFunction.ThueMorseLucasSupport
import FabiusFunction.ThueMorseSparseMoments
import FabiusFunction.TwoAdic

/-!
# Submask weight enumerators and Boolean Möbius inversion

The submasks of `n` form a Boolean lattice on the set of one-bit
positions of `n`.  This module proves the atlas's enumerator and Möbius
layer for that lattice, using the faithful powerset parametrization of
the odd Pascal positions.

Nothing in the powerset layer depends on the index type being `ℕ`, so the
three combinatorial engines are proved for `Finset α` over an arbitrary
index type (and, where the value ring was fixed, over an arbitrary
commutative ring); the `Finset ℕ` statements the rest of the corpus uses
are kept verbatim as corollaries.

The two facts that make the encoding `T ↦ ∑_{j∈T} 2^j` a lattice
isomorphism — `bitSupport_sum_two_pow` and `sum_two_pow_injective` —
now live in `ThueMorseLucasSupport`, beside the bit law
`testBit_sum_two_pow` that proves both; this file imports them and
uses them under the same names.

* `sub_sum_two_pow` / `xor_sum_two_pow` — complements in the lattice:
  `n - k` and `n ^^^ k` agree on submasks and are the encoded complement.
* `sum_powerset_pow_card'` — the **powerset weight enumerator**
  `∑_{T⊆S} z^|T| = (1+z)^|S|` for a finset of an arbitrary index type
  over an arbitrary commutative semiring; `sum_powerset_pow_card` is its
  `Finset ℕ` instance.
* `sum_oddBinomialIndices_pow_binaryWeight` — the **submask weight
  enumerator** `∑_{k⊑n} z^wt(k) = (1+z)^wt(n)` over any commutative
  semiring, with the bivariate refinement
  `∑_{k⊑n} x^wt(k)·y^wt(n-k) = (x+y)^wt(n)`
  (`sum_oddBinomialIndices_pow_pow`).
* `thueMorseSign_eq_sum_oddBinomialIndices_neg_two_pow` — the
  **reconstruction formula** `ε(n) = ∑_{k⊑n} (-2)^wt(k)`, and the
  inversion-polynomial identity `z^wt(n) = ∑_{k⊑n} (z-1)^wt(k)`.
* `sum_powerset_neg_one_pow_card'` and
  `sum_filter_superset_neg_one_pow'` — the alternating powerset sums
  `∑_{T⊆S} (-1)^|T| = [S = ∅]` and `∑_{U⊆T⊆S} (-1)^(|S∖T|) = [U = S]`
  for a finset of an arbitrary index type, valued in an arbitrary
  commutative ring; `sum_filter_superset_neg_one_pow` is the `ℤ`-valued
  `Finset ℕ` instance of the second.
* `sum_powerset_mobius'` — **Boolean Möbius inversion** on the finsets
  of an arbitrary index type, for any additive commutative group:
  `∑_{T⊆S} (-1)^(|S∖T|) • (∑_{U⊆T} f U) = f S`; `sum_powerset_mobius` is
  its `Finset ℕ` instance.
* `submask_mobius_inversion` — the numeric form on submasks: if
  `g(k) = ∑_{j⊑k} f(j)` for every `k ⊑ n`, then
  `f(n) = ∑_{k⊑n} ε(n ^^^ k) • g(k)`: the Möbius function of the
  submask poset is `μ(k,n) = ε(n ^^^ k)`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The encoding is a lattice isomorphism -/

/-- Subtraction of an encoded subset from the encoded full support is the
encoded complement. -/
theorem sub_sum_two_pow {S T : Finset ℕ} (hT : T ⊆ S) :
    (∑ j ∈ S, 2 ^ j) - (∑ j ∈ T, 2 ^ j) = ∑ j ∈ S \ T, 2 ^ j := by
  have h := Finset.sum_sdiff (f := fun j => 2 ^ j) hT
  omega

/-- XOR of an encoded subset with the encoded full support is the encoded
complement. -/
theorem xor_sum_two_pow {S T : Finset ℕ} (hT : T ⊆ S) :
    (∑ j ∈ S, 2 ^ j) ^^^ (∑ j ∈ T, 2 ^ j) = ∑ j ∈ S \ T, 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_sum_two_pow, testBit_sum_two_pow,
    testBit_sum_two_pow]
  by_cases hiS : i ∈ S
  · by_cases hiT : i ∈ T
    · simp [hiS, hiT, Finset.mem_sdiff]
    · simp [hiS, hiT, Finset.mem_sdiff]
  · have hiT : i ∉ T := fun h => hiS (hT h)
    simp [hiS, hiT, Finset.mem_sdiff]

/-! ### Weight enumerators -/

/-- **Powerset weight enumerator over an arbitrary index type**:
`∑_{T⊆S} z^|T| = (1+z)^|S|` for `S : Finset α` and `z` in any commutative
semiring.  No decidability hypothesis is needed, since only
`Finset.powerset` and cardinality occur in the statement. -/
theorem sum_powerset_pow_card' {α R : Type*} [CommSemiring R]
    (S : Finset α) (z : R) :
    ∑ T ∈ S.powerset, z ^ T.card = (1 + z) ^ S.card := by
  classical
  have h := Finset.prod_add (fun _ : α => z) (fun _ : α => (1 : R)) S
  simp only [Finset.prod_const, one_pow, mul_one] at h
  rw [add_comm (1 : R) z]
  exact h.symm

/-- Powerset weight enumerator: `∑_{T⊆S} z^|T| = (1+z)^|S|`. -/
theorem sum_powerset_pow_card {R : Type*} [CommSemiring R]
    (S : Finset ℕ) (z : R) :
    ∑ T ∈ S.powerset, z ^ T.card = (1 + z) ^ S.card :=
  sum_powerset_pow_card' S z

/-- **Submask weight enumerator**: `∑_{k⊑n} z^wt(k) = (1+z)^wt(n)` over
any commutative semiring. -/
theorem sum_oddBinomialIndices_pow_binaryWeight {R : Type*} [CommSemiring R]
    (n : ℕ) (z : R) :
    ∑ k ∈ oddBinomialIndices n, z ^ binaryWeight k =
      (1 + z) ^ binaryWeight n := by
  rw [oddBinomialIndices_eq_image_powerset,
    Finset.sum_image (sum_two_pow_injOn_powerset n)]
  have hterm : ∀ T ∈ (bitSupport n).powerset,
      z ^ binaryWeight (∑ j ∈ T, 2 ^ j) = z ^ T.card := by
    intro T _
    rw [binaryWeight_sum_two_pow_eq_card]
  rw [Finset.sum_congr rfl hterm, sum_powerset_pow_card, card_bitSupport]

/-- **Bivariate submask enumerator**:
`∑_{k⊑n} x^wt(k)·y^wt(n-k) = (x+y)^wt(n)`. -/
theorem sum_oddBinomialIndices_pow_pow {R : Type*} [CommSemiring R]
    (n : ℕ) (x y : R) :
    ∑ k ∈ oddBinomialIndices n,
        x ^ binaryWeight k * y ^ binaryWeight (n - k) =
      (x + y) ^ binaryWeight n := by
  rw [oddBinomialIndices_eq_image_powerset,
    Finset.sum_image (sum_two_pow_injOn_powerset n), ← card_bitSupport n]
  have hprod := Finset.prod_add (fun _ : ℕ => x) (fun _ : ℕ => y)
    (bitSupport n)
  rw [Finset.prod_const] at hprod
  rw [hprod]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTsub := Finset.mem_powerset.mp hT
  rw [Finset.prod_const, Finset.prod_const,
    binaryWeight_sum_two_pow_eq_card,
    show n - ∑ j ∈ T, 2 ^ j =
      ∑ j ∈ bitSupport n \ T, 2 ^ j from by
        conv_lhs => rw [← sum_two_pow_bitSupport n]
        exact sub_sum_two_pow hTsub,
    binaryWeight_sum_two_pow_eq_card]

/-- **Reconstruction formula**: `ε(n) = ∑_{k⊑n} (-2)^wt(k)`. -/
theorem thueMorseSign_eq_sum_oddBinomialIndices_neg_two_pow (n : ℕ) :
    thueMorseSign n =
      ∑ k ∈ oddBinomialIndices n, (-2 : ℤ) ^ binaryWeight k := by
  rw [sum_oddBinomialIndices_pow_binaryWeight n (-2 : ℤ), thueMorseSign]
  norm_num

/-- **Inversion-polynomial identity**:
`z^wt(n) = ∑_{k⊑n} (z-1)^wt(k)` over any commutative ring. -/
theorem pow_binaryWeight_eq_sum_oddBinomialIndices {R : Type*} [CommRing R]
    (n : ℕ) (z : R) :
    z ^ binaryWeight n =
      ∑ k ∈ oddBinomialIndices n, (z - 1) ^ binaryWeight k := by
  rw [sum_oddBinomialIndices_pow_binaryWeight n (z - 1)]
  ring_nf

/-- **Nested binomial formula**: combining the reconstruction with the
central-binomial valuation `ν₂ C(2k,k) = wt(k)` expresses the sign
through ordinary binomial data only:
`ε(n) = ∑_{C(n,k) odd} (-2)^(ν₂ C(2k,k))`. -/
theorem thueMorseSign_eq_sum_nested_binomial (n : ℕ) :
    thueMorseSign n =
      ∑ k ∈ oddBinomialIndices n,
        (-2 : ℤ) ^ padicValNat 2 ((2 * k).choose k) := by
  rw [thueMorseSign_eq_sum_oddBinomialIndices_neg_two_pow]
  exact Finset.sum_congr rfl fun k _ => by
    rw [centralChoose_padicValNat_two]

/-! ### Boolean Möbius inversion -/

/-- **Alternating powerset sum**, for a finset of an arbitrary index type
and values in an arbitrary commutative ring:
`∑_{T⊆S} (-1)^|T| = [S = ∅]`.  This is Mathlib's
`Finset.sum_powerset_neg_one_pow_card` with the value ring freed
from `ℤ`; it is the `z = -1` case of `sum_powerset_pow_card'`. -/
theorem sum_powerset_neg_one_pow_card' {α R : Type*} [DecidableEq α]
    [CommRing R] (S : Finset α) :
    ∑ T ∈ S.powerset, (-1 : R) ^ T.card = if S = ∅ then 1 else 0 := by
  have hz : (1 : R) + (-1) = 0 := by ring
  rw [sum_powerset_pow_card' S (-1 : R), hz, zero_pow_eq]
  simp [Finset.card_eq_zero]

/-- Signed sum over the interval `[U, S]` of the Boolean lattice of an
arbitrary finite set, with values in an arbitrary commutative ring:
`∑_{U⊆T⊆S} (-1)^(|S∖T|) = [U = S]`. -/
theorem sum_filter_superset_neg_one_pow' {α R : Type*} [DecidableEq α]
    [CommRing R] (S U : Finset α) (hU : U ⊆ S) :
    ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (-1 : R) ^ (S \ T).card =
      if U = S then 1 else 0 := by
  have himg : S.powerset.filter (fun T => U ⊆ T) =
      ((S \ U).powerset).image (fun V => U ∪ V) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hTS, hUT⟩
      refine ⟨T \ U, ?_, ?_⟩
      · intro v hv
        rw [Finset.mem_sdiff] at hv ⊢
        exact ⟨hTS hv.1, hv.2⟩
      · rw [Finset.union_sdiff_of_subset hUT]
    · rintro ⟨V, hV, rfl⟩
      constructor
      · exact Finset.union_subset hU ((hV).trans (Finset.sdiff_subset))
      · exact Finset.subset_union_left
  have hinj : ∀ V₁ ∈ (S \ U).powerset, ∀ V₂ ∈ (S \ U).powerset,
      U ∪ V₁ = U ∪ V₂ → V₁ = V₂ := by
    intro V₁ h₁ V₂ h₂ h
    have h₁' := Finset.mem_powerset.mp h₁
    have h₂' := Finset.mem_powerset.mp h₂
    ext v
    constructor
    · intro hv
      have hvU : v ∉ U := fun hU' =>
        (Finset.mem_sdiff.mp (h₁' hv)).2 hU'
      have : v ∈ U ∪ V₂ := h ▸ Finset.mem_union_right _ hv
      rcases Finset.mem_union.mp this with h' | h'
      · exact absurd h' hvU
      · exact h'
    · intro hv
      have hvU : v ∉ U := fun hU' =>
        (Finset.mem_sdiff.mp (h₂' hv)).2 hU'
      have : v ∈ U ∪ V₁ := h.symm ▸ Finset.mem_union_right _ hv
      rcases Finset.mem_union.mp this with h' | h'
      · exact absurd h' hvU
      · exact h'
  rw [himg, Finset.sum_image hinj]
  have hsd : ∀ V ∈ (S \ U).powerset,
      (-1 : R) ^ (S \ (U ∪ V)).card =
        (-1) ^ (S \ U).card * (-1) ^ V.card := by
    intro V hV
    have hV' := Finset.mem_powerset.mp hV
    have hset : S \ (U ∪ V) = (S \ U) \ V := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    have hcard : ((S \ U) \ V).card = (S \ U).card - V.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hV']
    have hle : V.card ≤ (S \ U).card := Finset.card_le_card hV'
    rw [hset, hcard]
    have hsplit : (-1 : R) ^ (S \ U).card =
        (-1) ^ ((S \ U).card - V.card) * (-1) ^ V.card := by
      rw [← pow_add]
      congr 1
      omega
    have hsq : ((-1 : R) ^ V.card) * ((-1) ^ V.card) = 1 := by
      rw [← pow_add, Even.neg_one_pow ⟨V.card, rfl⟩]
    calc (-1 : R) ^ ((S \ U).card - V.card)
        = (-1) ^ ((S \ U).card - V.card) *
            (((-1 : R) ^ V.card) * ((-1) ^ V.card)) := by rw [hsq, mul_one]
      _ = ((-1) ^ ((S \ U).card - V.card) * (-1) ^ V.card) *
            (-1) ^ V.card := by ring
      _ = (-1) ^ (S \ U).card * (-1) ^ V.card := by rw [← hsplit]
  rw [Finset.sum_congr rfl hsd, ← Finset.mul_sum,
    sum_powerset_neg_one_pow_card']
  have hiff : S \ U = ∅ ↔ U = S := by
    constructor
    · intro h
      exact Finset.Subset.antisymm hU
        (Finset.sdiff_eq_empty_iff_subset.mp h)
    · rintro rfl
      exact Finset.sdiff_self _
  by_cases h : U = S
  · rw [if_pos h, if_pos (hiff.mpr h), mul_one, h, Finset.sdiff_self,
      Finset.card_empty, pow_zero]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h')), mul_zero]

/-- Signed sum over the interval `[U, S]` of the Boolean lattice:
`∑_{U⊆T⊆S} (-1)^(|S∖T|) = [U = S]`. -/
theorem sum_filter_superset_neg_one_pow (S U : Finset ℕ) (hU : U ⊆ S) :
    ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (-1 : ℤ) ^ (S \ T).card =
      if U = S then 1 else 0 :=
  sum_filter_superset_neg_one_pow' S U hU

/-- **Boolean Möbius inversion on the finsets of an arbitrary index
type.**  For any additive commutative group,
`∑_{T⊆S} (-1)^(|S∖T|) • (∑_{U⊆T} f U) = f S`. -/
theorem sum_powerset_mobius' {α A : Type*} [DecidableEq α]
    [AddCommGroup A] (S : Finset α) (f : Finset α → A) :
    ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card • ∑ U ∈ T.powerset, f U =
      f S := by
  have hexpand : ∀ T ∈ S.powerset,
      (-1 : ℤ) ^ (S \ T).card • ∑ U ∈ T.powerset, f U =
      ∑ U ∈ S.powerset,
        (if U ⊆ T then (-1 : ℤ) ^ (S \ T).card • f U else 0) := by
    intro T hT
    have hTS := Finset.mem_powerset.mp hT
    rw [Finset.smul_sum]
    rw [← Finset.sum_filter]
    congr 1
    ext U
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro h
      exact ⟨h.trans hTS, h⟩
    · exact fun h => h.2
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  have hinner : ∀ U ∈ S.powerset,
      ∑ T ∈ S.powerset,
        (if U ⊆ T then (-1 : ℤ) ^ (S \ T).card • f U else 0) =
      (if U = S then 1 else 0 : ℤ) • f U := by
    intro U hU
    have hUS := Finset.mem_powerset.mp hU
    rw [← Finset.sum_filter, ← Finset.sum_smul,
      sum_filter_superset_neg_one_pow' (R := ℤ) S U hUS]
  rw [Finset.sum_congr rfl hinner]
  have hcollapse : ∀ U ∈ S.powerset,
      (if U = S then (1 : ℤ) else 0) • f U =
        (if U = S then f U else 0) := by
    intro U _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hcollapse, Finset.sum_ite_eq' S.powerset S f,
    if_pos (Finset.mem_powerset.mpr Finset.Subset.rfl)]

/-- **Boolean Möbius inversion on finsets.**  For any additive commutative
group, `∑_{T⊆S} (-1)^(|S∖T|) • (∑_{U⊆T} f U) = f S`. -/
theorem sum_powerset_mobius {A : Type*} [AddCommGroup A]
    (S : Finset ℕ) (f : Finset ℕ → A) :
    ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card • ∑ U ∈ T.powerset, f U =
      f S :=
  sum_powerset_mobius' S f

/-- **Submask Möbius inversion.**  If `g(k) = ∑_{j⊑k} f(j)` for every
submask `k` of `n`, then `f(n) = ∑_{k⊑n} ε(n ^^^ k) • g(k)`: the Möbius
function of the submask poset is `μ(k, n) = ε(n ^^^ k)`. -/
theorem submask_mobius_inversion {A : Type*} [AddCommGroup A]
    (n : ℕ) (f g : ℕ → A)
    (hg : ∀ k ∈ oddBinomialIndices n,
      g k = ∑ j ∈ oddBinomialIndices k, f j) :
    f n = ∑ k ∈ oddBinomialIndices n, thueMorseSign (n ^^^ k) • g k := by
  have hmob := sum_powerset_mobius (bitSupport n)
    (fun T => f (∑ j ∈ T, 2 ^ j))
  rw [oddBinomialIndices_eq_image_powerset,
    Finset.sum_image (sum_two_pow_injOn_powerset n)]
  have hterm : ∀ T ∈ (bitSupport n).powerset,
      thueMorseSign (n ^^^ ∑ j ∈ T, 2 ^ j) • g (∑ j ∈ T, 2 ^ j) =
      (-1 : ℤ) ^ (bitSupport n \ T).card •
        ∑ U ∈ T.powerset, f (∑ j ∈ U, 2 ^ j) := by
    intro T hT
    have hTsub := Finset.mem_powerset.mp hT
    have hxor : n ^^^ (∑ j ∈ T, 2 ^ j) = ∑ j ∈ bitSupport n \ T, 2 ^ j := by
      conv_lhs => rw [← sum_two_pow_bitSupport n]
      exact xor_sum_two_pow hTsub
    have hsign : thueMorseSign (n ^^^ ∑ j ∈ T, 2 ^ j) =
        (-1 : ℤ) ^ (bitSupport n \ T).card := by
      rw [hxor, thueMorseSign_sum_two_pow]
    have hgk : g (∑ j ∈ T, 2 ^ j) =
        ∑ U ∈ T.powerset, f (∑ j ∈ U, 2 ^ j) := by
      have hmem : (∑ j ∈ T, 2 ^ j) ∈ oddBinomialIndices n := by
        rw [oddBinomialIndices_eq_image_powerset]
        exact Finset.mem_image_of_mem _ hT
      rw [hg _ hmem, oddBinomialIndices_eq_image_powerset,
        bitSupport_sum_two_pow,
        Finset.sum_image (fun a _ b _ h => sum_two_pow_injective h)]
    rw [hsign, hgk]
  rw [Finset.sum_congr rfl hterm, hmob, sum_two_pow_bitSupport]

end Fabius
