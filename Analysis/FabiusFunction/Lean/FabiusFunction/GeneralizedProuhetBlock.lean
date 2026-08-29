import FabiusFunction.ParityCharacter
import FabiusFunction.ThueMorseSparseProuhet

/-!
# The first surviving moment of a generalized Prouhet block

The exponent-sequence volume's generalized Prouhet theorem evaluates
the first non-vanishing power moment of the weighted sign block:
writing `O` for the odd layers `{h < L : a h odd}` and `ω = |O|`,

`∑_{n<2^L} ε_a(n)·n^ω = (-1)^ω · ω! · 2^{L-ω} · 2^{∑_{h∈O} h}`.

Its offset-independent core is already formal, as
`sum_powerset_neg_one_pow_pow_card`, which evaluates
`∑_{U⊆S} (-1)^{|U|}(x + ∑_{j∈U} w_j)^{|S|}` for an arbitrary finite
`S`, arbitrary weights, and *every* offset `x`.  What the volume
records as missing is the step from that core to the block moment: the
**free-even-layer step**, which sums the core over the `2^{L-ω}`
choices of the even-layer digits.  This module supplies it, and hence
the moment itself.

The mechanism is that the sign `ε_a` does not see the even layers at
all.  Splitting a subset `T ⊆ range L` into `T ∩ O` and `T ∩ E`, the
sign depends only on `|T ∩ O|`, while the *value* `∑_{j∈T} 2^j` splits
as an odd-layer part plus an even-layer offset.  So the block sum is a
sum over even-layer offsets of the offset-independent core, and that
core leaves the inner sum unchanged — which is exactly why the answer
carries the factor `2^{L-ω}` and no more.

* `oddLayers`, `evenLayers` — the two halves of `range L`;
* `card_oddLayers_add_card_evenLayers` — they partition it;
* `parityCharacter_sum_two_pow_eq_inter` — the sign sees only `T ∩ O`;
* `sum_powerset_range_split` — **the free-even-layer decomposition**;
* `sum_range_two_pow_parityCharacter_mul_eval` — **the general
  evaluation**, for every polynomial of degree at most `ω`;
* `sum_range_two_pow_parityCharacter_mul_pow_eq_zero` and
  `sum_range_two_pow_parityCharacter_mul_pow` — its two extremal
  cases, the volume's two boxed displays;
* `sum_range_two_pow_thueMorseSign_mul_pow` — the constant-weight
  reading, where every layer is odd and the free factor is `1`.

The identification of `ω` with the order of the zero of the block
polynomial at `z = 1` is not proved here; it is
`Fabius.rootMultiplicity_prouhetBlockPoly` in the downstream module
`FabiusFunction.ProuhetBlockZeroOrder`, which imports this one.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The odd layers of a weight sequence below `L`: the positions whose
weight is odd, and so the positions the sign character can see. -/
def oddLayers (a : ℕ → ℕ) (L : ℕ) : Finset ℕ :=
  {h ∈ range L | a h % 2 = 1}

/-- The even layers below `L`: the complementary positions, which the
sign character ignores and which supply the free offsets. -/
def evenLayers (a : ℕ → ℕ) (L : ℕ) : Finset ℕ :=
  {h ∈ range L | ¬ a h % 2 = 1}

/-- Odd layers are positions below the cutoff. -/
theorem oddLayers_subset (a : ℕ → ℕ) (L : ℕ) :
    oddLayers a L ⊆ range L := Finset.filter_subset _ _

/-- Even layers are positions below the cutoff. -/
theorem evenLayers_subset (a : ℕ → ℕ) (L : ℕ) :
    evenLayers a L ⊆ range L := Finset.filter_subset _ _

/-- Membership in the odd-layer set is the defining range-and-parity condition. -/
theorem mem_oddLayers {a : ℕ → ℕ} {L h : ℕ} :
    h ∈ oddLayers a L ↔ h ∈ range L ∧ a h % 2 = 1 := Finset.mem_filter

/-- Membership in the even-layer set is the complementary range-and-parity condition. -/
theorem mem_evenLayers {a : ℕ → ℕ} {L h : ℕ} :
    h ∈ evenLayers a L ↔ h ∈ range L ∧ ¬ a h % 2 = 1 :=
  Finset.mem_filter

/-- The two layer sets are disjoint. -/
theorem disjoint_oddLayers_evenLayers (a : ℕ → ℕ) (L : ℕ) :
    Disjoint (oddLayers a L) (evenLayers a L) := by
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  exact (mem_evenLayers.mp hx').2 (mem_oddLayers.mp hx).2

/-- Every position below `L` is an odd layer or an even one. -/
theorem mem_oddLayers_or_mem_evenLayers {a : ℕ → ℕ} {L x : ℕ}
    (hx : x ∈ range L) :
    x ∈ oddLayers a L ∨ x ∈ evenLayers a L := by
  by_cases hodd : a x % 2 = 1
  · exact Or.inl (mem_oddLayers.mpr ⟨hx, hodd⟩)
  · exact Or.inr (mem_evenLayers.mpr ⟨hx, hodd⟩)

/-- The two layer sets partition `range L`. -/
theorem card_oddLayers_add_card_evenLayers (a : ℕ → ℕ) (L : ℕ) :
    (oddLayers a L).card + (evenLayers a L).card = L := by
  rw [oddLayers, evenLayers]
  have h := Finset.card_filter_add_card_filter_not
    (s := range L) (fun h => a h % 2 = 1)
  rwa [Finset.card_range] at h

/-- The number of even layers is the cutoff minus the number of odd layers. -/
theorem card_evenLayers (a : ℕ → ℕ) (L : ℕ) :
    (evenLayers a L).card = L - (oddLayers a L).card := by
  have h := card_oddLayers_add_card_evenLayers a L
  omega

/-- Two signs agree as soon as their exponents do modulo two. -/
private theorem neg_one_pow_eq_of_mod_two {m n : ℕ}
    (h : m % 2 = n % 2) : (-1 : ℤ) ^ m = (-1) ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  conv_rhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_add, pow_mul, pow_mul, neg_one_sq, one_pow, one_pow,
    one_mul, one_mul, h]

/-- **The sign sees only the odd layers.**  On the dyadic code of a
subset `T ⊆ range L`, the parity character is `(-1)` to the number of
odd layers that `T` meets. -/
theorem parityCharacter_sum_two_pow_eq_inter (a : ℕ → ℕ) (L : ℕ)
    {T : Finset ℕ} (hT : T ⊆ range L) :
    parityCharacter a (∑ j ∈ T, 2 ^ j) =
      (-1 : ℤ) ^ (T ∩ oddLayers a L).card := by
  classical
  rw [parityCharacter_sum_two_pow]
  refine neg_one_pow_eq_of_mod_two ?_
  have hmod : (∑ j ∈ T, a j) % 2 = (∑ j ∈ T, a j % 2) % 2 :=
    Finset.sum_nat_mod T 2 a
  have hstep : ∀ j ∈ T,
      a j % 2 = if j ∈ oddLayers a L then 1 else 0 := by
    intro j hj
    by_cases hodd : a j % 2 = 1
    · rw [if_pos (mem_oddLayers.mpr ⟨hT hj, hodd⟩), hodd]
    · have hzero : a j % 2 = 0 := by omega
      rw [if_neg (fun hc => hodd (mem_oddLayers.mp hc).2), hzero]
  have hcount : ∑ j ∈ T, a j % 2 = (T ∩ oddLayers a L).card := by
    rw [Finset.sum_congr rfl hstep, ← Finset.card_filter,
      Finset.filter_mem_eq_inter]
  rw [hmod, hcount]

/-- A subset of `range L` is the disjoint union of its odd-layer and
even-layer parts. -/
theorem inter_oddLayers_union_inter_evenLayers {a : ℕ → ℕ} {L : ℕ}
    {T : Finset ℕ} (hT : T ⊆ range L) :
    T ∩ oddLayers a L ∪ T ∩ evenLayers a L = T := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    rcases mem_oddLayers_or_mem_evenLayers (a := a) (hT hx) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

/-- **The free-even-layer decomposition.**  A sum over the subsets of
`range L` whose summand depends on the subset only through its odd and
even parts is a double sum, the even part ranging freely.  This is the
combinatorial content of the step the volume leaves open. -/
theorem sum_powerset_range_split {M : Type*} [AddCommMonoid M]
    (a : ℕ → ℕ) (L : ℕ) (g : Finset ℕ → Finset ℕ → M) :
    ∑ T ∈ (range L).powerset,
        g (T ∩ oddLayers a L) (T ∩ evenLayers a L) =
      ∑ V ∈ (evenLayers a L).powerset,
        ∑ U ∈ (oddLayers a L).powerset, g U V := by
  classical
  have hdisj := disjoint_oddLayers_evenLayers a L
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (fun T _ => (T ∩ evenLayers a L, T ∩ oddLayers a L))
    (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro T _
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩
  · rintro ⟨u, v⟩ huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    refine Finset.mem_powerset.mpr fun x hx => ?_
    rcases Finset.mem_union.mp hx with hx' | hx'
    · exact evenLayers_subset a L (Finset.mem_powerset.mp hu hx')
    · exact oddLayers_subset a L (Finset.mem_powerset.mp hv hx')
  · intro T hT
    have hTr := Finset.mem_powerset.mp hT
    rw [Finset.union_comm]
    exact inter_oddLayers_union_inter_evenLayers hTr
  · rintro ⟨u, v⟩ huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    have hu' := Finset.mem_powerset.mp hu
    have hv' := Finset.mem_powerset.mp hv
    have hleft : (u ∪ v) ∩ evenLayers a L = u := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxE⟩
        · exact hx
        · exact absurd hxE (Finset.disjoint_left.mp hdisj (hv' hx))
      · exact fun hx => ⟨Or.inl hx, hu' hx⟩
    have hright : (u ∪ v) ∩ oddLayers a L = v := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxO⟩
        · exact absurd (hu' hx) (Finset.disjoint_left.mp hdisj hxO)
        · exact hx
      · exact fun hx => ⟨Or.inr hx, hv' hx⟩
    simp only [Prod.mk.injEq]
    exact ⟨hleft, hright⟩
  · intro T _
    rfl

/-- The block sum recoded over the subsets of `range L`. -/
private theorem sum_range_two_pow_eq_sum_powerset (a : ℕ → ℕ) (L : ℕ)
    (p : Polynomial ℤ) :
    ∑ n ∈ range (2 ^ L), parityCharacter a n * p.eval (n : ℤ) =
      ∑ T ∈ (range L).powerset,
        parityCharacter a (∑ j ∈ T, 2 ^ j) *
          p.eval ((∑ j ∈ T, 2 ^ j : ℕ) : ℤ) :=
  (sum_powerset_two_pow L
    (fun n => parityCharacter a n * p.eval (n : ℤ))).symm

/-- Each summand, resolved into an odd-layer part carrying the sign
and an even-layer part carrying only an offset. -/
private theorem summand_split (a : ℕ → ℕ) (L : ℕ) (p : Polynomial ℤ)
    {T : Finset ℕ} (hT : T ⊆ range L) :
    parityCharacter a (∑ j ∈ T, 2 ^ j) *
        p.eval ((∑ j ∈ T, 2 ^ j : ℕ) : ℤ) =
      (-1 : ℤ) ^ (T ∩ oddLayers a L).card *
        p.eval (((∑ j ∈ T ∩ evenLayers a L, 2 ^ j : ℕ) : ℤ) +
          ∑ j ∈ T ∩ oddLayers a L, (2 : ℤ) ^ j) := by
  classical
  have hdisj := disjoint_oddLayers_evenLayers a L
  have hdT : Disjoint (T ∩ oddLayers a L) (T ∩ evenLayers a L) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj)
  have hsplit : ∑ j ∈ T, 2 ^ j =
      (∑ j ∈ T ∩ oddLayers a L, 2 ^ j) +
        ∑ j ∈ T ∩ evenLayers a L, 2 ^ j := by
    rw [← Finset.sum_union hdT]
    exact (Finset.sum_congr
      (inter_oddLayers_union_inter_evenLayers hT).symm
      fun _ _ => rfl)
  have hcast : (((∑ j ∈ T ∩ oddLayers a L, 2 ^ j) +
        ∑ j ∈ T ∩ evenLayers a L, 2 ^ j : ℕ) : ℤ) =
      ((∑ j ∈ T ∩ evenLayers a L, 2 ^ j : ℕ) : ℤ) +
        ∑ j ∈ T ∩ oddLayers a L, (2 : ℤ) ^ j := by
    push_cast
    ring
  rw [parityCharacter_sum_two_pow_eq_inter a L hT, hsplit, hcast]

/-- **The generalized Prouhet block evaluation.**  For every integer
polynomial of degree at most `ω = |O_L(a)|`,

`∑_{n<2^L} ε_a(n)·p(n) = p_ω · (-1)^ω·ω!·2^{L-ω}·2^{∑_{h∈O} h}`,

where `p_ω` is the coefficient of `X^ω`.  No nonzeroness hypothesis is
needed anywhere: the statement includes the zero polynomial and the
case `ω = 0`.

Both boxed displays of the volume's theorem are extremal cases of this
one — the vanishing below the threshold is `p_ω = 0`, and the first
surviving moment is `p = X^ω`, where `p_ω = 1`.

The factor `2^{L-ω}` counts the even-layer offsets, each of which
contributes the same offset-independent core. -/
theorem sum_range_two_pow_parityCharacter_mul_eval (a : ℕ → ℕ) (L : ℕ)
    (p : Polynomial ℤ) (hdeg : p.natDegree ≤ (oddLayers a L).card) :
    ∑ n ∈ range (2 ^ L), parityCharacter a n * p.eval (n : ℤ) =
      p.coeff (oddLayers a L).card *
        ((-1 : ℤ) ^ (oddLayers a L).card *
          ((oddLayers a L).card.factorial : ℤ) *
          2 ^ (L - (oddLayers a L).card) *
          2 ^ (∑ h ∈ oddLayers a L, h)) := by
  classical
  have step2 : ∑ T ∈ (range L).powerset,
      parityCharacter a (∑ j ∈ T, 2 ^ j) *
          p.eval ((∑ j ∈ T, 2 ^ j : ℕ) : ℤ) =
      ∑ T ∈ (range L).powerset,
        (-1 : ℤ) ^ (T ∩ oddLayers a L).card *
          p.eval (((∑ j ∈ T ∩ evenLayers a L, 2 ^ j : ℕ) : ℤ) +
            ∑ j ∈ T ∩ oddLayers a L, (2 : ℤ) ^ j) :=
    Finset.sum_congr rfl fun T hT =>
      summand_split a L p (Finset.mem_powerset.mp hT)
  have step3 : ∑ T ∈ (range L).powerset,
      (-1 : ℤ) ^ (T ∩ oddLayers a L).card *
          p.eval (((∑ j ∈ T ∩ evenLayers a L, 2 ^ j : ℕ) : ℤ) +
            ∑ j ∈ T ∩ oddLayers a L, (2 : ℤ) ^ j) =
      ∑ V ∈ (evenLayers a L).powerset,
        ∑ U ∈ (oddLayers a L).powerset,
          (-1 : ℤ) ^ U.card *
            p.eval (((∑ j ∈ V, 2 ^ j : ℕ) : ℤ) +
              ∑ j ∈ U, (2 : ℤ) ^ j) :=
    sum_powerset_range_split a L
      (fun U V => (-1 : ℤ) ^ U.card *
        p.eval (((∑ j ∈ V, 2 ^ j : ℕ) : ℤ) + ∑ j ∈ U, (2 : ℤ) ^ j))
  have step4 : ∀ V ∈ (evenLayers a L).powerset,
      (∑ U ∈ (oddLayers a L).powerset, (-1 : ℤ) ^ U.card *
          p.eval (((∑ j ∈ V, 2 ^ j : ℕ) : ℤ) +
            ∑ j ∈ U, (2 : ℤ) ^ j)) =
        p.coeff (oddLayers a L).card *
          ((-1 : ℤ) ^ (oddLayers a L).card *
            ((oddLayers a L).card.factorial : ℤ) *
            ∏ j ∈ oddLayers a L, (2 : ℤ) ^ j) :=
    fun V _ => sum_powerset_neg_one_pow_eval_eq_coeff_card
      (oddLayers a L) (fun j => (2 : ℤ) ^ j) p hdeg
      ((∑ j ∈ V, 2 ^ j : ℕ) : ℤ)
  rw [sum_range_two_pow_eq_sum_powerset a L, step2, step3,
    Finset.sum_congr rfl step4, Finset.sum_const,
    Finset.card_powerset, nsmul_eq_mul, Finset.prod_pow_eq_pow_sum,
    card_evenLayers a L]
  push_cast
  ring

/-- **The vanishing of the lower moments.**  Below the threshold `ω`
every power moment of the block is zero: the coefficient of `X^ω` in
`X^k` vanishes for `k < ω`. -/
theorem sum_range_two_pow_parityCharacter_mul_pow_eq_zero (a : ℕ → ℕ)
    (L k : ℕ) (hk : k < (oddLayers a L).card) :
    ∑ n ∈ range (2 ^ L), parityCharacter a n * (n : ℤ) ^ k = 0 := by
  have hdeg : ((Polynomial.X : Polynomial ℤ) ^ k).natDegree ≤
      (oddLayers a L).card := by
    rw [Polynomial.natDegree_X_pow]
    exact hk.le
  have h := sum_range_two_pow_parityCharacter_mul_eval a L
    ((Polynomial.X : Polynomial ℤ) ^ k) hdeg
  rw [Polynomial.coeff_X_pow, if_neg (Ne.symm (Nat.ne_of_lt hk)),
    zero_mul] at h
  simpa using h

/-- **The first surviving moment of a generalized Prouhet block.**
With `O` the odd layers below `L` and `ω = |O|`,

`∑_{n<2^L} ε_a(n)·n^ω = (-1)^ω·ω!·2^{L-ω}·2^{∑_{h∈O} h}`.

This is the previous theorem at `p = X^ω`, whose `ω`-th coefficient
is `1`. -/
theorem sum_range_two_pow_parityCharacter_mul_pow (a : ℕ → ℕ) (L : ℕ) :
    ∑ n ∈ range (2 ^ L),
        parityCharacter a n * (n : ℤ) ^ (oddLayers a L).card =
      (-1 : ℤ) ^ (oddLayers a L).card *
        ((oddLayers a L).card.factorial : ℤ) *
        2 ^ (L - (oddLayers a L).card) *
        2 ^ (∑ h ∈ oddLayers a L, h) := by
  have hdeg : ((Polynomial.X : Polynomial ℤ) ^
      (oddLayers a L).card).natDegree ≤ (oddLayers a L).card := by
    rw [Polynomial.natDegree_X_pow]
  have h := sum_range_two_pow_parityCharacter_mul_eval a L
    ((Polynomial.X : Polynomial ℤ) ^ (oddLayers a L).card) hdeg
  rw [Polynomial.coeff_X_pow_self, one_mul] at h
  simpa using h

/-- The constant-weight reading.  At `a ≡ 1` every layer below `L` is
odd, so `ω = L`, the free factor is `1`, and the moment is the
classical Prouhet–Thue–Morse evaluation

`∑_{n<2^L} (-1)^{w(n)}·n^L = (-1)^L·L!·2^{L(L-1)/2}`. -/
theorem sum_range_two_pow_thueMorseSign_mul_pow (L : ℕ) :
    ∑ n ∈ range (2 ^ L), thueMorseSign n * (n : ℤ) ^ L =
      (-1 : ℤ) ^ L * (L.factorial : ℤ) *
        2 ^ (∑ h ∈ range L, h) := by
  classical
  have hodd : oddLayers (fun _ => 1) L = range L := by
    ext h
    simp [oddLayers]
  have hmain := sum_range_two_pow_parityCharacter_mul_pow
    (fun _ => 1) L
  rw [hodd, Finset.card_range, Nat.sub_self, pow_zero,
    mul_one] at hmain
  rw [← hmain]
  exact Finset.sum_congr rfl fun n _ => by
    rw [parityCharacter_const_one]

end Fabius
