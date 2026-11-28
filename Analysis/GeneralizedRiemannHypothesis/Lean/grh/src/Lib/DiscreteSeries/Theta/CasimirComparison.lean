import Lib.DiscreteSeries.FlenstedJensen.CasimirEigenfunction
import Lib.DiscreteSeries.Theta.FockDualPair

/-!
# The Casimir elements of an oscillator pair

An oscillator pair is given by a `FockDualPair` `T` with `n = card R` rows and `n' = card C`
columns; the first group acts on the rows. This file proves that, with the centres (the weights of
the twisting characters) removed, the Casimir elements of the two groups differ by the constant
`n n' (n - n') / 4`, and that for matching parameters the numbers `|u|² - |ρ|²` and `|u'|² - |ρ'|²`
differ by the same constant, where `u`, `u'` are the centred parameters, that is, the entries
shifted by the centres. By `HCParam.HasGap.casimirValue_sub_centre` these numbers are the centred
Casimir values.

The notions that the statements use:
* a parameter `l : HCParam ε` is an integer vector that stands for `l = 2λ`; `l.HasGap h` says that
  its entries are distinct, of the parity of `n - 1`, and at least `2h` apart where the signs `ε`
  differ;
* for symmetric `r`, `twoRho l r` is the sum of the roots selected by `r` that are positive for `l`,
  so `twoRho l ⊤` is `2ρ`, and `l.casimirValue` is `|λ|² - |ρ|²`;
* `T.oscRows` is the oscillator action of `gl R` on polynomials, and `T.swap` is the same pair with
  rows and columns exchanged;
* `T.centredParam l r` is `2u_r = l r - 2γ + n'` with `γ = T.rowShift` the scalar on the diagonal of
  the row action (`T.columnShift` is that of the column action `T.swap.oscRows`), and
  `IsMatch T l l'` says that `l` and `l'` have gap `500 (n + n')³`, that each row is matched with a
  column or has `|2u_r| < n - n'`, and that each column is matched with a row or has
  `|2u'_c| < n' - n`; the row `r` and the column `c` are matched if `u_r = -u'_c` and
  `T.globalSign * ε r * ε' c * 2u_r > |n - n'|`.

## Relation to the literature

Known result: the constant difference of the centred Casimir elements of the two groups of an
oscillator pair, a case of the correspondence of infinitesimal characters. Source: compare A. Paul,
First occurrence for the dual pairs (U(p,q), U(r,s)), Canad. J. Math. 51 (1999), Theorem 2.11.

See also `Lib.DiscreteSeries.Theta.LocalCorrespondence`.
-/

namespace New

open Finset Fock
open Fintype (card)

section SumsOfSquares

/-- The sum `∑ (2k - c)²` over `k < d`, times `3`, in closed form. -/
theorem three_mul_sum_range_two_mul_sub_sq (c : ℤ) (d : ℕ) :
    3 * ∑ k ∈ range d, (2 * (k : ℤ) - c) ^ 2 =
      2 * d * (d - 1) * (2 * d - 1) - 6 * c * d * (d - 1) + 3 * d * c ^ 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, mul_add, ih]
    grind

/-- A set of `d` distinct integers of the parity of `d - 1` and of modulus below `d` is
`{1 - d, 3 - d, …, d - 1}`, so the sum of their squares is `d (d² - 1) / 3`. -/
theorem three_mul_sum_sq_of_injOn {α : Type*} (s : Finset α) (f : α → ℤ) (h_inj : Set.InjOn f s)
    (h_parity : ∀ i ∈ s, Even (f i + #s - 1)) (h_bound : ∀ i ∈ s, |f i| < #s) :
    3 * ∑ i ∈ s, f i ^ 2 = #s * (#s ^ 2 - 1) := by
  let g (k : ℕ) : ℤ := 2 * k - (#s - 1)
  have hg_inj : Function.Injective g := fun j k hjk ↦ by simpa [g] using hjk
  have h_subset : s.image f ⊆ (range #s).image g := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hz
    obtain ⟨k, hk⟩ := h_parity i hi
    have hi_bound := abs_lt.1 (h_bound i hi)
    exact mem_image.2 ⟨k.toNat, mem_range.2 (by lia), by grind⟩
  have h_image : s.image f = (range #s).image g := eq_of_subset_of_card_le h_subset <| by
    simp [card_image_of_injective _ hg_inj, card_image_of_injOn h_inj]
  calc 3 * ∑ i ∈ s, f i ^ 2 = 3 * ∑ z ∈ s.image f, z ^ 2 := by rw [sum_image h_inj]
    _ = 3 * ∑ k ∈ range #s, g k ^ 2 := by rw [h_image, sum_image hg_inj.injOn]
    _ = #s * (#s ^ 2 - 1) := by linear_combination three_mul_sum_range_two_mul_sub_sq (#s - 1) #s

variable {n : Type} [Fintype n]

/-- For a vector `l` with distinct entries, `twoRho l ⊤ = 2ρ` is the sum of the roots positive for
`l`. The squares of its entries sum to `N (N² - 1) / 3` with `N = card n`, that is,
`|ρ|² = N (N² - 1) / 12`. -/
theorem three_mul_sum_twoRho_sq {l : n → ℤ} (hl : l.Injective) :
    3 * ∑ i : n, twoRho l ⊤ i ^ 2 = card n * (card n ^ 2 - 1) := by
  classical
  have h_count (i : n) : (#{j | l j < l i} + #{j | l i < l j} + 1 : ℤ) = card n :=
    mod_cast card_lt_add_card_gt_add_one hl i
  have h_value (i : n) : twoRho l ⊤ i = #{j | l j < l i} - #{j | l i < l j} := by
    simp [twoRho]
  have h_inj : Function.Injective (twoRho l ⊤) := by
    intro a b hab
    obtain h | h | h := lt_trichotomy (l a) (l b)
    exacts [absurd hab (twoRho_lt_twoRho h).ne, hl h, absurd hab (twoRho_lt_twoRho h).ne']
  have h_parity (i : n) : Even (twoRho l ⊤ i + card n - 1) :=
    ⟨#{j | l j < l i}, by linear_combination h_value i - h_count i⟩
  have h_bound (i : n) : |twoRho l ⊤ i| < card n := by grind
  exact three_mul_sum_sq_of_injOn univ _ h_inj.injOn (fun i _ ↦ h_parity i) fun i _ ↦ h_bound i

/-- For a symmetric relation `r`, the entries of `twoRho l r` sum to zero. -/
theorem sum_twoRho_eq_zero (l : n → ℤ) (r : n → n → Prop) [DecidableRel r]
    (hr : ∀ i j : n, r i j → r j i) : ∑ i : n, twoRho l r i = 0 := by
  -- Both counts run over the pairs with `r`, ordered by `l`.
  simp only [twoRho, sum_sub_distrib, card_filter, Nat.cast_sum, sub_eq_zero]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [Iff.intro (hr j i) (hr i j)]

/-- For a parameter `l = 2λ` with a gap (distinct entries of the parity of `n - 1`, those of
different signs `ε` far apart), the lowest K-type and `λ` have the same sum of entries. -/
theorem HCParam.HasGap.two_mul_sum_lowestKType {ε : n → ℤˣ} {l : HCParam ε} {h : ℕ}
    (hg : l.HasGap h) : 2 * ∑ i : n, l.lowestKType i = ∑ i : n, l i := by
  have h_noncompact : ∑ i, twoRho l (fun i j ↦ ε i ≠ ε j) i = 0 :=
    sum_twoRho_eq_zero l _ fun i j ↦ Ne.symm
  have h_compact : ∑ i, twoRho l (fun i j ↦ ε i = ε j) i = 0 :=
    sum_twoRho_eq_zero l _ fun i j ↦ Eq.symm
  simp [mul_sum, two_mul_lowestKType hg, sum_sub_distrib, sum_add_distrib, h_noncompact, h_compact]

/-- Let `l = 2λ` be a parameter with a gap (distinct entries of the parity of `n - 1`, those of
different signs far apart), with Casimir value `κ = |λ|² - |ρ|²` and lowest K-type `μ`. For any
scalar `w`, the value with the centre `w` removed, `κ - 2w ∑ μ_a + n w²`, is
`∑ (λ_a - w)² - n (n² - 1) / 12`, where `n` is the number of entries. -/
theorem HCParam.HasGap.casimirValue_sub_centre {ε : n → ℤˣ} {l : HCParam ε} {h : ℕ}
    (hg : l.HasGap h) (w : ℂ) :
    l.casimirValue - 2 * w * ∑ a : n, (l.lowestKType a : ℂ) + card n * w ^ 2 =
      ∑ a : n, (l a / 2 - w) ^ 2 - (card n * (card n ^ 2 - 1) / 12 : ℂ) := by
  have h_rho : 3 * ∑ a, (twoRho l ⊤ a : ℂ) ^ 2 = card n * (card n ^ 2 - 1) :=
    mod_cast three_mul_sum_twoRho_sq hg.injective
  have h_sum : 2 * ∑ a, (l.lowestKType a : ℂ) = ∑ a, (l a : ℂ) :=
    mod_cast hg.two_mul_sum_lowestKType
  have h_value : (l.casimirValue : ℂ) =
      (∑ a, (l a : ℂ) ^ 2 - ∑ a, (twoRho l ⊤ a : ℂ) ^ 2) / 4 := by
    simp [casimirValue, ← sum_div, sum_sub_distrib]
  have h_term (a : n) : (l a / 2 - w : ℂ) ^ 2 = (l a : ℂ) ^ 2 / 4 - w * l a + w ^ 2 := by ring
  have h_square : ∑ a, (l a / 2 - w : ℂ) ^ 2 =
      (∑ a, (l a : ℂ) ^ 2) / 4 - w * ∑ a, (l a : ℂ) + card n * w ^ 2 := by
    simp [h_term, sum_add_distrib, ← sum_div, ← mul_sum]
  rw [h_value, h_square]
  linear_combination -w * h_sum - h_rho / 12

end SumsOfSquares

section Casimir

variable {R C ι : Type} [Fintype R] [DecidableEq R] [Fintype C] {ε : R → ℤˣ} {ε' : C → ℤˣ}

omit [Fintype R] [DecidableEq R] in
/-- The centred parameters `l r - 2γ + card C` of a vector `l` with distinct entries are
distinct. -/
theorem FockDualPair.centredParam_injective (T : FockDualPair ε ε' ι) {l : HCParam ε}
    (hl : Function.Injective l) : Function.Injective (T.centredParam l) :=
  fun a b hab ↦ hl (by simpa [FockDualPair.centredParam] using hab)

/-- Let `l`, `l'` be matching parameters of the pair `T`: they have a large gap, and each row and
column is matched, with opposite centred parameters, or has a small one. Let `n' ≤ n` for
`n = card R` and `n' = card C`. The squares of the centred parameters `l r - 2 T.rowShift + n'` of
the rows and `l' c - 2 T.columnShift + n` of the columns (the rows of `T.swap`) differ in sum by
`d₀ (d₀² - 1) / 3` with `d₀ = n - n'`, the share of the unmatched rows. -/
theorem IsMatch.three_mul_sum_sq_sub_of_le {T : FockDualPair ε ε' ι} {l : HCParam ε}
    {l' : HCParam ε'} (hm : IsMatch T l l') (h_le : card C ≤ card R) :
    3 * (∑ r : R, T.centredParam l r ^ 2 - ∑ c : C, T.swap.centredParam l' c ^ 2) =
      (card R - card C) * ((card R - card C) ^ 2 - 1) := by
  -- Every index of the smaller group is matched, with one row `m c`.
  have h_matched (c : C) : ∃ r : R, T.centredParam l r = -T.swap.centredParam l' c := by
    obtain ⟨r, h_eq, -⟩ | h_lt := hm.right c
    · exact ⟨r, h_eq⟩
    · grind [abs_nonneg]
  choose m h_opposite using h_matched
  have h_row_inj : Function.Injective (T.centredParam l) :=
    T.centredParam_injective hm.hasGap_row.injective
  have hm_inj : Function.Injective m := by
    refine fun c c' hc ↦ T.swap.centredParam_injective hm.hasGap_column.injective (neg_injective ?_)
    rw [← h_opposite c, ← h_opposite c', hc]
  -- So the larger group has `n - n'` unmatched entries.
  set free : Finset R := (univ.image m)ᶜ with h_free
  have h_card : (#free : ℤ) = card R - card C := by
    simp [h_free, card_compl, card_image_of_injective _ hm_inj, h_le]
  have h_split : ∑ r, T.centredParam l r ^ 2 =
      ∑ c, T.swap.centredParam l' c ^ 2 + ∑ r ∈ free, T.centredParam l r ^ 2 := by
    rw [← sum_add_sum_compl (univ.image m), sum_image hm_inj.injOn]
    simp only [h_opposite, neg_sq, h_free]
  -- They are distinct, of the parity of `n - n' - 1` and of modulus below `n - n'`.
  have h_small (r : R) (hr : r ∈ free) : |T.centredParam l r| < #free := by
    rw [h_card]
    refine (hm.left r).resolve_left ?_
    rintro ⟨c, hr_eq, -⟩
    have h_eq : m c = r := h_row_inj ((h_opposite c).trans hr_eq.symm)
    exact mem_compl.1 hr (mem_image.2 ⟨c, mem_univ c, h_eq⟩)
  have h_parity (r : R) (_ : r ∈ free) : Even (T.centredParam l r + #free - 1) := by
    obtain ⟨k, hk⟩ : Even (l r + card R - 1) := hm.hasGap_row.parity r
    refine ⟨k - T.rowShift, ?_⟩
    rw [h_card, FockDualPair.centredParam]
    lia
  rw [h_split, add_sub_cancel_left, ← h_card]
  exact three_mul_sum_sq_of_injOn free _ h_row_inj.injOn h_parity h_small

/-- For matching parameters `l`, `l'` of the pair `T`, the squares of the centred parameters
`l r - 2γ + n'` of the rows and `l' c - 2γ' + n` of the columns differ in sum by `d₀ (d₀² - 1) / 3`,
where `n = card R`, `n' = card C`, and `d₀ = n - n'` may have either sign. -/
theorem IsMatch.three_mul_sum_sq_sub [DecidableEq C] {T : FockDualPair ε ε' ι} {l : HCParam ε}
    {l' : HCParam ε'} (hm : IsMatch T l l') :
    3 * (∑ r : R, T.centredParam l r ^ 2 - ∑ c : C, T.swap.centredParam l' c ^ 2) =
      (card R - card C) * ((card R - card C) ^ 2 - 1) := by
  obtain h_le | h_le := le_total (card C) (card R)
  · exact hm.three_mul_sum_sq_sub_of_le h_le
  · have h_swap : 3 * (∑ c, T.swap.centredParam l' c ^ 2 - ∑ r, T.centredParam l r ^ 2) =
        (card C - card R : ℤ) * ((card C - card R : ℤ) ^ 2 - 1) := by
      simpa only [T.swap_swap] using hm.swap.three_mul_sum_sq_sub_of_le h_le
    linear_combination -h_swap

variable [DecidableEq C] {A : Type*} [Ring A] [Algebra ℂ A]

/-- For a square array `F` in a complex algebra, adding a scalar `t` to the diagonal adds
`2t ∑ F_aa + n t²` to `∑ F_ab F_ba`, where `n = card R`. -/
theorem sum_add_scalar_mul_add_scalar (F : R → R → A) (t : ℂ) :
    ∑ a : R, ∑ b : R, (F a b + if a = b then t • 1 else 0) * (F b a + if b = a then t • 1 else 0) =
      ∑ a : R, ∑ b : R, F a b * F b a + (2 * t) • ∑ a : R, F a a + (card R * t ^ 2) • (1 : A) := by
  have h_term (a b : R) :
      (F a b + if a = b then t • 1 else 0) * (F b a + if b = a then t • 1 else 0) =
        F a b * F b a + if a = b then (2 * t) • F a a + t ^ 2 • (1 : A) else 0 := by
    obtain rfl | hab := eq_or_ne a b
    · simp only [ite_true, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      module
    · simp [hab, hab.symm]
  simp only [h_term, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← smul_sum, sum_const,
    card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  module

/-- Normal ordering. Let `x`, `d` be arrays in a complex algebra with
`d_rc x_rc' = x_rc' d_rc + δ_cc'`. With `n = card R` and `n' = card C`, the Casimir sum of the
elements `∑ c, x_ac d_bc + (n'/2) δ_ab` is `D₄ + (n + n') D₂ + n n'² / 4`, where
`D₄ = ∑ x_ac x_bc' d_bc d_ac'` and `D₂ = ∑ x_rc d_rc`. -/
theorem sum_mul_eq_normal_order (x d : R → C → A)
    (h_comm : ∀ (r : R) (c c' : C), d r c * x r c' = x r c' * d r c + if c = c' then 1 else 0) :
    ∑ a : R, ∑ b : R, (∑ c : C, x a c * d b c + if a = b then (card C / 2 : ℂ) • 1 else 0) *
        (∑ c : C, x b c * d a c + if b = a then (card C / 2 : ℂ) • 1 else 0) =
      ∑ a : R, ∑ b : R, ∑ c : C, ∑ c' : C, x a c * x b c' * d b c * d a c' +
        (card R + card C : ℂ) • ∑ r : R, ∑ c : C, x r c * d r c +
          (card R * card C ^ 2 / 4 : ℂ) • (1 : A) := by
  -- The commutators give `n D₂`.
  have h_move (a b : R) (c c' : C) : x a c * d b c * (x b c' * d a c') =
      x a c * x b c' * d b c * d a c' + if c = c' then x a c * d a c' else 0 := by
    rw [mul_assoc, ← mul_assoc (d b c), h_comm]
    split_ifs <;> noncomm_ring
  have h_quartic : ∑ a, ∑ b, (∑ c, x a c * d b c) * ∑ c, x b c * d a c =
      ∑ a, ∑ b, ∑ c, ∑ c', x a c * x b c' * d b c * d a c' +
        (card R : ℂ) • ∑ r, ∑ c, x r c * d r c := by
    simp only [sum_mul_sum, h_move, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, sum_const,
      card_univ, Nat.cast_smul_eq_nsmul, smul_sum]
  -- The scalar `n'/2` gives `n' D₂` and a constant.
  rw [sum_add_scalar_mul_add_scalar fun a b ↦ ∑ c, x a c * d b c, h_quartic]
  module

/-- The Casimir element with the centre `w` removed: it is formed with `E_ab - w δ_ab` in place of
`E_ab`. -/
noncomputable def GlModule.centredCasimir {M : Type*} [AddCommGroup M] [Module ℂ M]
    (ρ : GlModule R M) (w : ℂ) : Module.End ℂ M :=
  ∑ a : R, ∑ b : R, (ρ.E a b - if a = b then w • 1 else 0) * (ρ.E b a - if b = a then w • 1 else 0)

/-- On a vector of weight `ν`, the Casimir element with the centre `w` removed is
`Ω - 2w ∑ ν_a + n w²`, where `n = card R`. Here `Ω = ρ.casimirK 1` is the full Casimir element
`∑ E_ab E_ba`: all signs are `1`, so every pair of indices counts. -/
theorem GlModule.centredCasimir_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (ρ : GlModule R M) (w : ℂ) {ν : R → ℤ} {v : M} (hv : ∀ a : R, ρ.E a a v = (ν a : ℂ) • v) :
    ρ.centredCasimir w v =
      ρ.casimirK 1 v - (2 * w * ∑ a : R, (ν a : ℂ)) • v + (card R * w ^ 2) • v := by
  have h_expand : ρ.centredCasimir w =
      ρ.casimirK 1 + (2 * -w) • ∑ a, ρ.E a a + (card R * (-w) ^ 2) • 1 := by
    have h_casimir : ρ.casimirK 1 = ∑ a, ∑ b, ρ.E a b * ρ.E b a := by
      simp [GlModule.casimir]
    rw [h_casimir, ← sum_add_scalar_mul_add_scalar]
    simp only [centredCasimir, sub_eq_add_neg, neg_ite, neg_zero, neg_smul]
  simp [h_expand, hv, ← sum_smul]
  module

namespace FockDualPair

variable (T : FockDualPair ε ε' ι)

/-- The centre `w` of the action on the rows: the scalar `T.rowShift` on the diagonal is `w + n'/2`.
It is the weight of the character of the determinant by which the action is twisted. -/
noncomputable def centre : ℂ := T.rowShift - card C / 2

/-- The operator `x_rc`: for the variable `T.varEquiv (r, c)` of `MvPolynomial ι ℂ` attached to the
entry `(r, c)`, multiplication by the variable where its sign `T.indexSign` is `+`, minus the
derivative where it is `-`. -/
noncomputable abbrev raise (r : R) (c : C) : Module.End ℂ (MvPolynomial ι ℂ) :=
  raiseOp T.indexSign (T.varEquiv (r, c))

/-- The operator `d_rc`: for the variable `T.varEquiv (r, c)` of `MvPolynomial ι ℂ` attached to the
entry `(r, c)`, the derivative where the sign `T.indexSign` of the variable is `+`, multiplication
by the variable where it is `-`. -/
noncomputable abbrev lower (r : R) (c : C) : Module.End ℂ (MvPolynomial ι ℂ) :=
  lowerOp T.indexSign (T.varEquiv (r, c))

/-- The operator `D₄ = ∑ x_ac x_bc' d_bc d_ac'` of a Fock dual pair, over all rows `a`, `b` and
columns `c`, `c'`. -/
noncomputable def quarticOp : Module.End ℂ (MvPolynomial ι ℂ) :=
  ∑ a : R, ∑ b : R, ∑ c : C, ∑ c' : C, T.raise a c * T.raise b c' * T.lower b c * T.lower a c'

/-- The operator `D₂ = ∑ x_rc d_rc` of a Fock dual pair, over all rows `r` and columns `c`. -/
noncomputable def quadraticOp : Module.End ℂ (MvPolynomial ι ℂ) :=
  ∑ r : R, ∑ c : C, T.raise r c * T.lower r c

omit [Fintype R] [Fintype C] in
/-- The canonical commutation relation `d_rc x_r'c' = x_r'c' d_rc + δ_rr' δ_cc'` of the operators
`T.lower` and `T.raise`. -/
theorem lower_mul_raise (r r' : R) (c c' : C) : T.lower r c * T.raise r' c' =
    T.raise r' c' * T.lower r c + if r = r' ∧ c = c' then 1 else 0 := by
  classical
  refine LinearMap.ext fun P ↦ ?_
  split_ifs with h <;> simp_all [lowerOp_raiseOp]

omit [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] in
theorem lower_mul_lower (r r' : R) (c c' : C) :
    T.lower r c * T.lower r' c' = T.lower r' c' * T.lower r c := by
  classical
  exact LinearMap.ext fun P ↦ lowerOp_comm T.indexSign _ _ P

omit [DecidableEq R] [DecidableEq C] in
/-- `D₄` summed first over the columns: since the `d_rc` commute, the last two factors may be
exchanged. -/
theorem sum_columns_eq_quarticOp :
    ∑ c : C, ∑ c' : C, ∑ a : R, ∑ b : R,
      T.raise a c * T.raise b c' * T.lower a c' * T.lower b c = T.quarticOp := by
  calc
    _ = ∑ p : C × C, ∑ q : R × R,
          T.raise q.1 p.1 * T.raise q.2 p.2 * T.lower q.2 p.1 * T.lower q.1 p.2 := by
      simp only [Fintype.sum_prod_type, mul_assoc, T.lower_mul_lower]
    _ = ∑ q : R × R, ∑ p : C × C,
          T.raise q.1 p.1 * T.raise q.2 p.2 * T.lower q.2 p.1 * T.lower q.1 p.2 := sum_comm
    _ = T.quarticOp := by simp only [quarticOp, Fintype.sum_prod_type]

/-- For signs `δ` and a sign `s` (read in `ℂ`), the factor that is `1` if `δ a = δ b` and `s`
otherwise, times the same factor for `(b, a)`, is `1`. So these factors drop out of a Casimir
element. -/
theorem sign_mul_sign {n : Type*} (δ : n → ℤˣ) (s : ℤˣ) (a b : n) :
    (if δ a = δ b then 1 else s : ℂ) * (if δ b = δ a then 1 else s : ℂ) = 1 := by
  obtain hab | hab := eq_or_ne (δ a) (δ b)
  · simp [hab]
  · rw [ite_eq_right hab, ite_eq_right hab.symm, ← Int.cast_mul, Int.units_coe_mul_self,
      Int.cast_one]

/-- The row action of the matrix unit `(a, b)` less `T.centre = T.rowShift - n'/2` on the diagonal
is `∑ c, x_ac d_bc + (n'/2) δ_ab`, times the sign `T.globalSign` of the pair where the signs `ε a`,
`ε b` differ; here `n' = card C`, `x = T.raise` and `d = T.lower`. -/
theorem oscRows_E_sub_centre (a b : R) :
    (T.oscRows.E a b - if a = b then T.centre • 1 else 0) =
      (if ε a = ε b then 1 else T.globalSign : ℂ) •
      (∑ c : C, T.raise a c * T.lower b c + if a = b then (card C / 2 : ℂ) • 1 else 0) := by
  have h_unit : T.oscRows.E a b = (if ε a = ε b then 1 else T.globalSign : ℂ) •
      ∑ c, T.raise a c * T.lower b c + if a = b then (T.rowShift : ℂ) • 1 else 0 := by
    simp [oscRows_E, oscRowsUnit, glOp, Int.cast_smul_eq_zsmul]
  rw [h_unit]
  obtain rfl | hab := eq_or_ne a b
  · simp only [ite_true, centre]
    module
  · simp [hab]

/-- The column action of the matrix unit `(a, b)` less `T.swap.centre = T.columnShift - n/2` on the
diagonal is `-(∑ r, x_rb d_ra + (n/2) δ_ab)`, times the sign `T.globalSign` of the pair where the
signs `ε' a`, `ε' b` differ; here `n = card R`, `x = T.raise`, `d = T.lower`, and `T.swap` is `T`
with rows and columns exchanged. -/
theorem swap_oscRows_E_sub_centre (a b : C) :
    (T.swap.oscRows.E a b - if a = b then T.swap.centre • 1 else 0) =
      -(if ε' a = ε' b then 1 else T.globalSign : ℂ) •
        (∑ r : R, T.raise r b * T.lower r a + if b = a then (card R / 2 : ℂ) • 1 else 0) := by
  have h_unit : T.swap.oscRows.E a b = (if ε' a = ε' b then 1 else T.globalSign : ℂ) •
      -∑ r, T.lower r a * T.raise r b + if a = b then (T.columnShift : ℂ) • 1 else 0 := by
    simp [swap_oscRows_E, Int.cast_smul_eq_zsmul]
  rw [h_unit, show T.swap.centre = T.columnShift - card R / 2 from rfl]
  simp only [lower_mul_raise, true_and, sum_add_distrib, sum_const, card_univ]
  obtain rfl | hab := eq_or_ne a b
  · simp only [ite_true, ← Nat.cast_smul_eq_nsmul ℂ]
    module
  · simp [hab, hab.symm]

/-- The Casimir element of the row action `T.oscRows` with the centre `T.centre` removed is
`D₄ + (n + n') D₂ + n n'² / 4`, where `D₄ = T.quarticOp`, `D₂ = T.quadraticOp`, `n = card R` and
`n' = card C`. -/
theorem centredCasimir_oscRows : T.oscRows.centredCasimir T.centre =
    T.quarticOp + (card R + card C : ℂ) • T.quadraticOp +
      (card R * card C ^ 2 / 4 : ℂ) • 1 := by
  have h_comm (r : R) (c c' : C) : T.lower r c * T.raise r c' =
      T.raise r c' * T.lower r c + if c = c' then 1 else 0 := by simp [lower_mul_raise]
  -- The sign factors cancel in the products.
  have h_unsigned : T.oscRows.centredCasimir T.centre = ∑ a, ∑ b,
      (∑ c, T.raise a c * T.lower b c + if a = b then (card C / 2 : ℂ) • 1 else 0) *
        (∑ c, T.raise b c * T.lower a c + if b = a then (card C / 2 : ℂ) • 1 else 0) := by
    simp only [GlModule.centredCasimir, oscRows_E_sub_centre, smul_mul_smul_comm, sign_mul_sign,
      one_smul]
  rw [h_unsigned, sum_mul_eq_normal_order T.raise T.lower h_comm, quarticOp, quadraticOp]

/-- The Casimir element of the column action `T.swap.oscRows` with the centre `T.swap.centre`
removed is `D₄ + (n + n') D₂ + n² n' / 4`, where `D₄ = T.quarticOp`, `D₂ = T.quadraticOp`,
`n = card R` and `n' = card C`. -/
theorem centredCasimir_swap_oscRows : T.swap.oscRows.centredCasimir T.swap.centre =
    T.quarticOp + (card R + card C : ℂ) • T.quadraticOp +
      (card R ^ 2 * card C / 4 : ℂ) • 1 := by
  -- Normal ordering with the roles of rows and columns exchanged gives the same `D₄` and `D₂`.
  have h_comm (c : C) (r r' : R) : T.lower r c * T.raise r' c =
      T.raise r' c * T.lower r c + if r = r' then 1 else 0 := by simp [lower_mul_raise]
  have h_quadratic : ∑ c, ∑ r, T.raise r c * T.lower r c = T.quadraticOp := sum_comm
  -- The sign factors cancel in the products.
  have h_unsigned : T.swap.oscRows.centredCasimir T.swap.centre = ∑ a, ∑ b,
      (∑ r, T.raise r b * T.lower r a + if b = a then (card R / 2 : ℂ) • 1 else 0) *
        (∑ r, T.raise r a * T.lower r b + if a = b then (card R / 2 : ℂ) • 1 else 0) := by
    simp only [GlModule.centredCasimir, swap_oscRows_E_sub_centre, smul_mul_smul_comm,
      neg_mul_neg, sign_mul_sign, one_smul]
  rw [h_unsigned, sum_comm,
    sum_mul_eq_normal_order (fun c r ↦ T.raise r c) (fun c r ↦ T.lower r c) h_comm,
    T.sum_columns_eq_quarticOp, h_quadratic]
  module

/-- The centred Casimir element of the column action `T.swap.oscRows` is that of the row action
`T.oscRows` plus the constant `n n' d₀ / 4`, where `n = card R`, `n' = card C` and `d₀ = n - n'`. -/
theorem centredCasimir_swap_oscRows_eq_add : T.swap.oscRows.centredCasimir T.swap.centre =
    T.oscRows.centredCasimir T.centre + (card R * card C * (card R - card C) / 4 : ℂ) • 1 := by
  rw [centredCasimir_swap_oscRows, centredCasimir_oscRows]
  module

omit [DecidableEq R] [DecidableEq C] in
/-- The squares of the centred parameters `T.centredParam l r = l r - 2γ + n'` (with
`γ = T.rowShift`, `n' = card C`) sum to four times the sum of the squares of `λ_r - T.centre`, for
`l = 2λ`. -/
theorem sum_centredParam_sq (l : HCParam ε) :
    ∑ r : R, (T.centredParam l r : ℂ) ^ 2 = 4 * ∑ r : R, (l r / 2 - T.centre) ^ 2 := by
  rw [mul_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  push_cast [centre]
  ring

end FockDualPair

/-- For matching parameters `l = 2λ`, `l' = 2λ'` of the pair `T` (both of large gap, with centred
parameters that are opposite or small), `|u|² - |ρ|² + n n' d₀ / 4 = |u'|² - |ρ'|²`. Here
`u = λ - T.centre` and `u' = λ' - T.swap.centre`, with the centres `T.rowShift - n'/2` and
`T.columnShift - n/2` of the row and column actions; `|u|²` is the sum of squares, `n = card R`,
`n' = card C`, `d₀ = n - n'`, and `n (n² - 1) / 12`, `n' (n'² - 1) / 12` are `|ρ|²`, `|ρ'|²`. -/
theorem IsMatch.centred_casimirValue_eq {T : FockDualPair ε ε' ι} {l : HCParam ε}
    {l' : HCParam ε'} (hm : IsMatch T l l') :
    (∑ r : R, (l r / 2 - T.centre) ^ 2 - card R * (card R ^ 2 - 1) / 12 +
        card R * card C * (card R - card C) / 4 : ℂ) =
      (∑ c : C, (l' c / 2 - T.swap.centre) ^ 2 - card C * (card C ^ 2 - 1) / 12 : ℂ) := by
  have h_unmatched :
      3 * (∑ r, (T.centredParam l r : ℂ) ^ 2 - ∑ c, (T.swap.centredParam l' c : ℂ) ^ 2) =
        (card R - card C) * ((card R - card C) ^ 2 - 1) :=
    mod_cast hm.three_mul_sum_sq_sub
  -- What remains is `n³ - n'³ - d₀³ = 3 n n' d₀`.
  rw [T.sum_centredParam_sq, T.swap.sum_centredParam_sq] at h_unmatched
  linear_combination h_unmatched / 12

end Casimir

end New
