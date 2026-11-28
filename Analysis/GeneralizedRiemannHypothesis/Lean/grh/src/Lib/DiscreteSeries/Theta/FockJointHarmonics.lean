import Lib.DiscreteSeries.Theta.FockDualPair

/-!
# Weights of matched pairs and uniqueness of joint harmonics in Fock space

This file studies the weights of matched pairs of the parameters `l` and `l'` of a dual pair
`T : New.FockDualPair`. It proves that the joint harmonic is unique up to a scalar, and that one of
its two weights suffices for this. Here `New.FockDualPair.IsMatchedPair` says that row `r` is
matched with column `c`.

The proof of uniqueness has three steps.
* The weights relative to the vacuum: `New.IsMatch.relWeight_eq_neg`,
  `New.IsMatch.sign_mul_relWeight_nonneg`.
* Both polarisations in a raising operator kill a highest harmonic polynomial, and a row has
  variables of one sign: `New.DiscreteSeries.polarisation_eq_zero_of_isCompactPrimitive`,
  `New.DiscreteSeries.polarisation_self_eq_smul_of_isCompactPrimitive`.
* Such a polynomial does not vanish at the 0-1 matrix of the matching:
  `New.IsMatch.eval_matchingPoint_ne_zero`.

## Main definitions and results

* `New.IsMatch.unique`, `New.IsJointHarmonic.exists_eq_smul_of_row_weight`,
  `New.IsJointHarmonic.exists_eq_smul_of_column_weight`: the joint harmonic is unique up to a
  scalar, and one of its two weights suffices for this.
* `New.IsMatch.eval_matchingPoint_ne_zero`: a pre-joint harmonic does not vanish at the point
  `New.FockDualPair.matchingPoint`, the 0-1 matrix of the matching.

Notions from other files:
* `New.HCParam.HasGap`: `l.HasGap h` says that the entries of `l = 2λ` are distinct and congruent to
  `n − 1` mod 2, where `n` is their number, and `|λ_i − λ_j| ≥ h` whenever `ε_i ≠ ε_j`.
* `New.HCParam.IsKHighest`: `x` is a `K`-highest vector of weight `ν`: each `E a a` acts on it by
  `ν a`, and it is killed by the compact raising operators, the `E a b` with `ε a = ε b` and
  `l b < l a`. The second condition alone is `New.GlModule.IsCompactPrimitive`.
* `New.HCParam.lowestKType`: for a parameter `l = 2λ`, the integer vector `λ + ρ − 2ρ_c`, which is
  the highest weight of the lowest `K`-type.
* `New.FockDualPair.IsPreJointHarmonic`: `Φ ≠ 0` is killed by the compact raising operators of the
  columns and by the Laplacians of both sides, and is `K`-highest of weight `l.lowestKType` for
  rows.
* `New.FockDualPair.relWeight`: the entry in row `r` of the lowest `K`-type for `l`, minus the
  weight of the vacuum on a row of sign `ε r`.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Theta.LocalCorrespondence` for sources.
-/

noncomputable section

section JointHarmonicUnique

open Fintype (card)

namespace New

variable {R C ι : Type} [Fintype R] [Fintype C]
  {ε : R → ℤˣ} {ε' : C → ℤˣ} {l : HCParam ε} {l' : HCParam ε'} {T : FockDualPair ε ε' ι}

@[local grind .] theorem DiscreteSeries.int_unit_val_eq_one_or_neg_one (x : ℤˣ) :
    (x : ℤ) = 1 ∨ (x : ℤ) = -1 :=
  Int.isUnit_iff.1 x.isUnit

open MvPolynomial Finset InnerProductSpace ComplexOrder Fischer Fock Int Units DiscreteSeries
  FockDualPair

/-! ### The weights of rows and columns relative to the vacuum -/

/-- Let `l` be a parameter with a gap (only distinctness and parity of its entries matter). Twice
`T.relWeight l r`, the entry of the lowest `K`-type minus the weight of the vacuum in row `r`, is
`l r + ∑ j, ε r * ε j * sign (l j - l r) - 2γ + card C - ∑ c, η (r, c)`, where `γ` is the constant
of the row action and `η (r, c)` the sign of the variable `(r, c)`. -/
@[local grind .] theorem HCParam.HasGap.two_mul_relWeight {h : ℕ} (r : R) (hg : l.HasGap h) :
    2 * T.relWeight l r = l r + ∑ j : R, ε r * ε j * (l j - l r).sign -
      (2 * T.rowShift - (card C - ∑ c : C, (T.varSign (r, c) : ℤ))) := by
  have rows : twoRho l (fun a b : R ↦ ε a ≠ ε b) r - twoRho l (fun a b : R ↦ ε a = ε b) r =
      ∑ j : R, ε r * ε j * (l j - l r).sign := by
    push_cast [twoRho, card_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [ne_eq, Units.ext_iff]
    grind
  have cols : (2 * #{c : C | T.globalSign * ε r * ε' c ≠ 1} : ℤ) =
      card C - ∑ c : C, (T.varSign (r, c) : ℤ) := by
    push_cast [Fintype.card_eq_sum_ones, card_filter, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun c _ ↦ ?_
    obtain h_sign | h_sign := units_eq_one_or (T.globalSign * ε r * ε' c) <;>
      simp [pairSign, h_sign]
  rw [relWeight, mul_sub, two_mul_lowestKType hg, vacuumWeight, ← rows, ← cols]
  ring

/-- If the parameters `l` of the rows and `l'` of the columns are matched, then `l` has the gap
`500 * card R ^ 3 + A` for every `A` up to the number `card ι` of variables. -/
theorem IsMatch.hasLargeGap [Fintype ι] (hm : IsMatch T l l') {A : ℕ} (hA : A ≤ Fintype.card ι) :
    l.HasLargeGap A := by
  -- A matching has the gap `500 * (card R + card C) ^ 3`, and `A ≤ card ι = card R * card C`.
  have card_eq : Fintype.card ι = card R * card C := by
    rw [← Fintype.card_congr T.varEquiv, Fintype.card_prod]
  have mul_le : card R * card C ≤ card R * card C ^ 2 :=
    Nat.mul_le_mul_left (card R) (Nat.le_self_pow two_ne_zero (card C))
  refine hm.hasGap_row.mono ?_
  calc gapThreshold R A
      ≤ 500 * card R ^ 3 + card R * card C ^ 2 :=
        Nat.add_le_add_left ((hA.trans_eq card_eq).trans mul_le) _
    _ ≤ 500 * (card R + card C) ^ 3 := by ring_nf; lia

/-- If `l` and `l'` match, a row is matched with at most one column. -/
theorem IsMatch.col_eq_of_isMatchedPair (hm : IsMatch T l l') {r : R} {c d : C}
    (hc : T.IsMatchedPair l l' r c) (hd : T.IsMatchedPair l l' r d) : c = d := by
  grind [hm.hasGap_column.injective]

/-- If `l` and `l'` match, a column is matched with at most one row. -/
theorem IsMatch.row_eq_of_isMatchedPair (hm : IsMatch T l l') {a r : R} {c : C}
    (ha : T.IsMatchedPair l l' a c) (hr : T.IsMatchedPair l l' r c) : a = r := by
  grind [hm.hasGap_row.injective]

/-- Let `l`, `l'` match. Then `∑ c, G c ≤ ∑ r, F r`, provided that `G c ≤ F r` when row `r` is
matched with column `c`, that `0 ≤ F r` when the centred parameter `l r - 2γ + card C` is less than
`card R - card C` in absolute value, and that `G c ≤ 0` when `l' c - 2γ' + card R` is less than
`card C - card R` in absolute value. -/
theorem IsMatch.sum_cols_le_sum_rows (hm : IsMatch T l l') (F : R → ℤ) (G : C → ℤ)
    (h_matched : ∀ (r : R) (c : C), T.IsMatchedPair l l' r c → G c ≤ F r)
    (h_rows : ∀ r : R, |T.centredParam l r| < card R - card C → 0 ≤ F r)
    (h_cols : ∀ c : C, |T.swap.centredParam l' c| < card C - card R → G c ≤ 0) :
    ∑ c : C, G c ≤ ∑ r : R, F r := by
  -- The matching is a partial bijection. Compare both sides with the sum of `F r` over the matched
  -- pairs `(r, c)`.
  calc ∑ c : C, G c ≤ ∑ c : C, ∑ r : R, if T.IsMatchedPair l l' r c then F r else 0 := by
        gcongr with c
        obtain ⟨r, hr⟩ | h_free := hm.right c
        · rw [sum_eq_single_of_mem r (mem_univ r) fun a _ ha ↦
            ite_eq_right fun hac ↦ ha (hm.row_eq_of_isMatchedPair hac hr), ite_eq_left hr]
          exact h_matched r c hr
        · rw [sum_eq_zero fun r _ ↦ ite_eq_right (show ¬T.IsMatchedPair l l' r c by grind)]
          exact h_cols c h_free
    _ = ∑ r : R, ∑ c : C, if T.IsMatchedPair l l' r c then F r else 0 := sum_comm
    _ ≤ ∑ r : R, F r := by
        gcongr with r
        obtain ⟨c, hc⟩ | h_free := hm.left r
        · rw [sum_eq_single_of_mem c (mem_univ c) fun d _ hd ↦
            ite_eq_right fun hrd ↦ hd (hm.col_eq_of_isMatchedPair hrd hc), ite_eq_left hc]
        · rw [sum_eq_zero fun c _ ↦ ite_eq_right (show ¬T.IsMatchedPair l l' r c by grind)]
          exact h_rows r h_free

/-- Let `l`, `l'` match. If row `r` is matched with column `c`, then Λ_r − v_r = −(Λ'_c − v'_c),
where Λ, Λ' are the lowest `K`-types of `l`, `l'` and v, v' the weights of the vacuum `1` for the
row and the column action. -/
theorem IsMatch.relWeight_eq_neg (hm : IsMatch T l l') {r : R} {c : C}
    (hrc : T.IsMatchedPair l l' r c) :
    T.relWeight l r = -T.swap.relWeight l' c := by
  -- By `HasGap.two_mul_relWeight` the claim is `∑ d, G d = ∑ j, F j`. This holds
  -- termwise: matched terms agree and unmatched terms vanish, since by `hrc` the centred parameter
  -- of `r` is the negative of that of `c` and exceeds `|card R - card C|` in absolute value.
  let F (j : R) : ℤ := T.swap.varSign (c, j) - ε r * ε j * (l j - l r).sign
  let G (d : C) : ℤ := ε' c * ε' d * (l' d - l' c).sign - T.varSign (r, d)
  have matched (j : R) (d : C) (hjd : T.IsMatchedPair l l' j d) : G d = F j := by
    grind [pairSign, val_mul, Units.val_neg]
  have free_row (j : R) (hj : |T.centredParam l j| < card R - card C) : F j = 0 := by
    grind [pairSign, val_mul, Units.val_neg]
  have free_col (d : C) (hd : |T.swap.centredParam l' d| < card C - card R) : G d = 0 := by
    grind [pairSign, val_mul, Units.val_neg]
  have sum_eq : ∑ d : C, G d = ∑ j : R, F j :=
    le_antisymm
      (hm.sum_cols_le_sum_rows F G (fun j d hjd ↦ (matched j d hjd).le)
        (fun j hj ↦ (free_row j hj).ge) fun d hd ↦ (free_col d hd).le)
      (by simpa using hm.sum_cols_le_sum_rows (-F) (-G)
            (fun j d hjd ↦ neg_le_neg (matched j d hjd).ge)
            (fun j hj ↦ neg_nonneg.2 (free_row j hj).le) fun d hd ↦ neg_nonpos.2 (free_col d hd).ge)
  have param : l r - 2 * T.rowShift + card C = -(l' c - 2 * T.columnShift + card R) := hrc.1
  simp only [F, G, sum_sub_distrib] at sum_eq
  linarith [hm.hasGap_row.two_mul_relWeight (T := T) r,
    hm.hasGap_column.two_mul_relWeight (T := T.swap) c]

/-- Let `l`, `l'` match and let `s` be a sign. If `s` times the centred parameter
`l r - 2 * γ + card C` exceeds `card C - card R`, then `T.relWeight l r`, the weight of the lowest
`K`-type in row `r` relative to the vacuum, has the sign `s` or is zero. -/
theorem IsMatch.sign_mul_relWeight_nonneg (hm : IsMatch T l l') (r : R) (s : ℤˣ)
    (hr : card C - card R < (s : ℤ) * T.centredParam l r) :
    0 ≤ s * T.relWeight l r := by
  have inj : Function.Injective l := hm.hasGap_row.injective
  have parity (j : R) : Even (l j + card R - 1) := hm.hasGap_row.parity j
  have gap (i j : R) (hij : (ε i : ℤ) ≠ ε j) : 2 * card R ≤ |l i - l j| := by
    have hg : l.HasGap (card R) := hm.hasGap_row.mono (mod_cast by cases card R <;> lia)
    exact_mod_cast hg.gap i j fun h_eq ↦ hij (by rw [h_eq])
  -- The numbers `s * T.centredParam l j + card R - card C` are odd and distinct; write them as
  -- `2 * v j + 1`. At most `v r + 1` rows have `0 ≤ v j ≤ v r`.
  let v (j : R) : ℤ := (s * T.centredParam l j + card R - card C) / 2
  let S : Finset ℤ := Icc 0 (v r)
  have card_le : #{j : R | v j ∈ S} ≤ #S :=
    card_le_card_of_injOn v (fun j hj ↦ by simpa using hj) fun i _ j _ hij ↦ by grind
  specialize parity r

  -- Termwise comparison. Column terms are `≤ 0`, and row terms with `v j ∈ S` are `≥ 0`. For
  -- `v j ∉ S` a matched row has the term of its column, and an unmatched row is close to `r`, so
  -- `ε j = ε r` by `gap` and its term is `0`.
  let F (j : R) : ℤ := s * (ε r * ε j * (l j - l r).sign) + (if v j ∈ S then 2 else 0) - 1
  let G (c : C) : ℤ := s * T.varSign (r, c) - 1
  have matched (j : R) (c : C) (hjc : T.IsMatchedPair l l' j c) : G c ≤ F j := by
    have j_large : |(card R - card C : ℤ)| < T.globalSign * ε j * ε' c * T.centredParam l j := hjc.2
    have sign_rc : (T.varSign (r, c) : ℤ) = T.globalSign * ε r * ε' c := by simp [pairSign]
    grind
  have free_row (j : R) (hj : |T.centredParam l j| < card R - card C) : 0 ≤ F j := by
    grind [gap r j]
  have key : s * ∑ c : C, (T.varSign (r, c) : ℤ) ≤
      s * ∑ j : R, ε r * ε j * (l j - l r).sign + #{j : R | v j ∈ S} * 2 - card R + card C := by
    simpa [F, G, ← mul_sum, sum_ite, sum_add_distrib] using
      hm.sum_cols_le_sum_rows F G matched free_row fun c _ ↦ show G c ≤ 0 by grind
  have two_mul_eq : 2 * T.relWeight l r = l r + ∑ j : R, ε r * ε j * (l j - l r).sign -
      (2 * T.rowShift - (card C - ∑ c : C, (T.varSign (r, c) : ℤ))) :=
    hm.hasGap_row.two_mul_relWeight r
  -- Twice the right side of the goal is at least `2 * v r + 1 - 2 * #S = -1`.
  have lower_bound : 2 * v r + 1 - 2 * #S ≤ 2 * (s * T.relWeight l r) := by grind
  have card_S : (#S : ℤ) = v r + 1 := by grind [card_Icc]
  lia

/-! ### Highest harmonic polynomials

A compact raising operator `E a b` is the difference of two polarisations. -/

/-- Let `P` be killed by the compact raising operators of the rows for `l`, and let `ε a = ε b` and
`l b < l a`. Then the two polarisations whose difference is `E a b P` are equal: `∑ X_ac ∂_bc P`
over the columns `c` where `(b, c)` has sign `1`, and `∑ X_bc ∂_ac P` over those where it has sign
`-1`. -/
theorem DiscreteSeries.polarisation_one_eq_of_lt [DecidableEq R] [DecidableEq C]
    {P : MvPolynomial ι ℂ}
    (h_prim : T.oscRows.IsCompactPrimitive l P) {a b : R} (hab : ε a = ε b) (h_lt : l b < l a) :
    T.polarisation P a b 1 = T.polarisation P b a (-1) := by
  have h_ne : a ≠ b := fun h ↦ h_lt.ne (congrArg l h.symm)
  have h_E : T.oscRows.E a b P = T.polarisation P a b 1 - T.polarisation P b a (-1) +
      (if a = b then (T.vacuumWeight (ε a) : ℂ) else 0) • P :=
    oscRows_E_eq_polarisation_sub hab
  rw [h_prim a b hab h_lt, ite_eq_right h_ne, zero_smul, add_zero] at h_E
  exact sub_eq_zero.1 h_E.symm

/-- Let the entries of `l` be distinct, let `P` be killed by the compact raising operators of the
rows for `l` and by the Laplacians of the columns. For rows `a`, `b` of equal sign, the
polarisations `∑ X_bc ∂_ac P` over the columns `c` where `(a, c)` has sign `-s` and `∑ X_ac ∂_bc P`
over those where it has sign `s` are orthogonal for the Fischer inner product. For `s = 1` and
`a ≠ b` these are the two parts of `E a b P`. -/
theorem DiscreteSeries.inner_polarisation_eq_zero [DecidableEq R] [DecidableEq C]
    {P : MvPolynomial ι ℂ} (hl : l.Injective)
    (h_prim : T.oscRows.IsCompactPrimitive l P) (h_harm : T.swap.IsLaplaceHarmonic P) (s : ℤˣ)
    {a b : R} (hab : ε a = ε b) :
    ⟪T.polarisation P b a (-s), T.polarisation P a b s⟫_ℂ = 0 := by
  -- The pairing in the claim is `N s a b`, which does not depend on `s`. The numbers `N 1 a b` are
  -- `≥ 0`, and their sum over the rows `b` with `ε b = ε a` is a pairing with the Laplacians of the
  -- columns, which is `0`. So all of them vanish.
  let u (a : R) (c d : C) : MvPolynomial ι ℂ :=
    pderiv (T.varEquiv (a, c)) (pderiv (T.varEquiv (a, d)) P)
  let N (s : ℤˣ) (a b : R) : ℂ :=
    ∑ d with T.varSign (a, d) = -s, ∑ c with T.varSign (a, c) = s, ⟪u a c d, u b c d⟫_ℂ
  have u_comm (a : R) (c d : C) : u a c d = u a d c := pderiv_comm ..
  have N_neg (s : ℤˣ) (a b : R) : N (-s) a b = N s a b := by
    simp only [N, neg_neg]
    rw [sum_comm]
    simp only [u_comm a, u_comm b]
  -- `X` is adjoint to `pderiv`; no commutator term arises, as the two columns have opposite signs.
  have inner_pol (s : ℤˣ) {a b : R} (hab : ε a = ε b) :
      ⟪T.polarisation P b a (-s), T.polarisation P a b s⟫_ℂ = N s a b := by
    have sign_eq (c : C) : T.varSign (b, c) = T.varSign (a, c) := by simp only [pairSign, hab]
    simp only [polarisation, sum_inner, sign_eq, N]
    refine sum_congr rfl fun d hd ↦ (inner_sum ..).trans (sum_congr rfl fun c hc ↦ ?_)
    have hcd : T.varEquiv (a, c) ≠ T.varEquiv (b, d) := by
      grind [T.varEquiv.injective.eq_iff, neg_units_ne_self]
    rw [inner_X_mul.1, pderiv_mul, pderiv_X_of_ne hcd, zero_mul, zero_add, inner_X_mul.2,
      u_comm b]
  -- `N 1 a b` is a sum of squared norms for `a = b`, and one squared norm by
  -- `polarisation_one_eq_of_lt` otherwise.
  have N_nonneg (a b : R) (hb : b ∈ univ.filter (ε · = ε a)) : 0 ≤ N 1 a b := by
    have hab : ε a = ε b := (mem_filter.1 hb).2.symm
    obtain h_lt | h_eq | h_gt := lt_trichotomy (l b) (l a)
    · rw [← inner_pol 1 hab, polarisation_one_eq_of_lt h_prim hab h_lt]
      exact CStarModule.inner_self_nonneg
    · obtain rfl : b = a := hl h_eq
      exact sum_nonneg fun d _ ↦ sum_nonneg fun c _ ↦ CStarModule.inner_self_nonneg
    · rw [← N_neg, ← inner_pol (-1) hab, neg_neg, polarisation_one_eq_of_lt h_prim hab.symm h_gt]
      exact CStarModule.inner_self_nonneg
  -- Summing `u b c d` over the block of `a` gives a Laplacian of `P`, up to sign.
  have N_sum (a : R) : ∑ b with ε b = ε a, N 1 a b = 0 := by
    simp only [N]
    refine sum_comm.trans <| sum_eq_zero fun d hd ↦ sum_comm.trans <| sum_eq_zero fun c hc ↦ ?_
    have sign_c {b : R} (hb : ε b = ε a) : T.varSign (b, c) = 1 := by
      simpa only [pairSign, hb] using (mem_filter.1 hc).2
    have sign_d {b : R} (hb : ε b = ε a) : T.varSign (b, d) = -1 := by
      simpa only [pairSign, hb] using (mem_filter.1 hd).2
    have hcd : ε' c ≠ ε' d := by grind [pairSign, neg_units_ne_self]
    have block (b : R) : T.swap.varSign (c, b) = -1 ↔ ε b = ε a := by
      have sign_a : T.globalSign * ε' c * ε a = 1 := (mul_right_comm ..).trans (sign_c rfl)
      simp only [pairSign, neg_mul, neg_inj]
      rw [← sign_a, _root_.mul_right_inj]
    have laplacian : T.swap.fockLaplacian c d P = -∑ b with ε b = ε a, u b c d := by
      rw [fockLaplacian, LinearMap.sum_apply, filter_congr fun b _ ↦ block b, ← sum_neg_distrib]
      refine sum_congr rfl fun b hb ↦ ?_
      have swap_d : T.swap.varSign (d, b) = 1 := by
        simpa [mul_right_comm T.globalSign, neg_eq_iff_eq_neg, pairSign] using sign_d
          (mem_filter.1 hb).2
      simp [u, (block b).2 (mem_filter.1 hb).2, swap_d, glOp, raiseOp, lowerOp]
    rw [← inner_sum, neg_eq_zero.1 (laplacian.symm.trans (h_harm c d hcd)), inner_zero_right]
  have N_zero : N 1 a b = 0 :=
    (sum_eq_zero_iff_of_nonneg (N_nonneg a)).1 (N_sum a) b (mem_filter.2 ⟨mem_univ b, hab.symm⟩)
  rw [inner_pol s hab]
  obtain rfl | rfl := units_eq_one_or s <;> simp only [N_neg, N_zero]

/-- Let the entries of `l` be distinct, let `P` be killed by the compact raising operators of the
rows for `l` and by the Laplacians of the columns. If the rows `a`, `b` have equal sign and
`s * l b < s * l a`, then the polarisation `∑ X_ac ∂_bc P` over the columns `c` where `(b, c)` has
sign `s` is zero. -/
theorem DiscreteSeries.polarisation_eq_zero_of_isCompactPrimitive [DecidableEq R] [DecidableEq C]
    {P : MvPolynomial ι ℂ} (hl : l.Injective) (h_prim : T.oscRows.IsCompactPrimitive l P)
    (h_harm : T.swap.IsLaplaceHarmonic P) {s : ℤˣ} {a b : R} (hab : ε a = ε b)
    (h_lt : s * l b < s * l a) :
    T.polarisation P a b s = 0 := by
  -- The two parts of a raising operator are equal on `P`, and they are orthogonal.
  have pol_eq : T.polarisation P b a (-s) = T.polarisation P a b s := by
    obtain rfl | rfl := units_eq_one_or s
    · exact (polarisation_one_eq_of_lt h_prim hab (by simpa using h_lt)).symm
    · exact polarisation_one_eq_of_lt h_prim hab.symm (by simpa using h_lt)
  rw [← inner_self_eq_zero (𝕜 := ℂ)]
  simpa only [pol_eq] using inner_polarisation_eq_zero hl h_prim h_harm s hab

/-- Let the entries of `l` be distinct, let `P` be killed by the compact raising operators of the
rows for `l` and by the Laplacians of the columns, and let `E a a` act on it by the entry `Λ_a` of
the lowest `K`-type. Put `k = s * (Λ_a - v)`, where `v` is the weight of the vacuum in row `a`. If
`k ≥ 0`, then `P` has degree `k` in the variables of sign `s` of row `a`, and it does not depend on
the variables of sign `-s` of that row. -/
theorem DiscreteSeries.polarisation_self_eq_smul_of_isCompactPrimitive [DecidableEq R]
    [DecidableEq C] [Fintype ι] {P : MvPolynomial ι ℂ}
    (hl : l.Injective) (h_prim : T.oscRows.IsCompactPrimitive l P)
    (h_harm : T.swap.IsLaplaceHarmonic P) {s : ℤˣ} {a : R}
    (h_wt : T.oscRows.E a a P = (l.lowestKType a : ℂ) • P) (h_nonneg : 0 ≤ s * T.relWeight l a) :
    T.polarisation P a a s = ((s * T.relWeight l a : ℤ) : ℂ) • P ∧
      ∀ c : C, T.varSign (a, c) = -s → pderiv (T.varEquiv (a, c)) P = 0 := by
  set k : ℤ := s * T.relWeight l a with hk
  have pol_diag : T.polarisation P a a s = T.polarisation P a a (-s) + (k : ℂ) • P := by
    have h_E : T.oscRows.E a a P = T.polarisation P a a 1 - T.polarisation P a a (-1) +
        (T.vacuumWeight (ε a) : ℂ) • P := by simp [oscRows_E_eq_polarisation_sub]
    obtain rfl | rfl := units_eq_one_or s <;> simp [hk, sub_smul, ← h_wt, h_E]
  -- Orthogonality reads `‖Q‖ ^ 2 + k * ⟪Q, P⟫ = 0` for `Q = polarisation P a a (-s)`, and `⟪Q, P⟫`
  -- is the sum of the squared norms of the derivatives in question.
  have inner_eq : ⟪T.polarisation P a a (-s), P⟫_ℂ = ∑ c with T.varSign (a, c) = -s,
      ⟪pderiv (T.varEquiv (a, c)) P, pderiv (T.varEquiv (a, c)) P⟫_ℂ := by
    simp only [polarisation, sum_inner, inner_X_mul.1]
  have inner_nonneg : 0 ≤ (k : ℂ) * ⟪T.polarisation P a a (-s), P⟫_ℂ := by
    rw [inner_eq]
    exact mul_nonneg (mod_cast h_nonneg) (sum_nonneg fun c _ ↦ CStarModule.inner_self_nonneg)
  have orth : ⟪T.polarisation P a a (-s), T.polarisation P a a (-s)⟫_ℂ +
      (k : ℂ) * ⟪T.polarisation P a a (-s), P⟫_ℂ = 0 := by
    rw [← inner_smul_right, ← inner_add_right, ← pol_diag]
    exact inner_polarisation_eq_zero hl h_prim h_harm s rfl
  have pol_zero : T.polarisation P a a (-s) = 0 := inner_self_eq_zero.1
    ((add_eq_zero_iff_of_nonneg CStarModule.inner_self_nonneg inner_nonneg).1 orth).1
  refine ⟨by rw [pol_diag, pol_zero, zero_add], fun c hc ↦ ?_⟩
  rw [pol_zero, inner_zero_left] at inner_eq
  exact inner_self_eq_zero.1
    ((sum_eq_zero_iff_of_nonneg fun c _ ↦ CStarModule.inner_self_nonneg).1 inner_eq.symm c
      (mem_filter.2 ⟨mem_univ c, hc⟩))

/-- Let the entries of `l` be distinct, and let `P` be killed by the compact raising operators of
the rows and by the Laplacians of the columns. Fix a row `a` and a sign `s`. The polarisation
`∑ c, X_ac ∂P/∂X_bc` over the variables `X_bc` of sign `s` vanishes if `ε a = ε b` and
`s * l b < s * l a`. If `E a a` acts on `P` by the entry of the lowest `K`-type, and the weight
`T.relWeight l a` relative to the vacuum has sign `s` or is zero, then `P` is homogeneous of degree
`s * T.relWeight l a` in the variables of sign `s` of row `a` and free of those of sign `-s`. -/
theorem DiscreteSeries.polarisation_eq_of_isCompactPrimitive [DecidableEq R] [DecidableEq C]
    [Fintype ι] {P : MvPolynomial ι ℂ}
    (hl : l.Injective) (h_prim : T.oscRows.IsCompactPrimitive l P)
    (h_harm : T.swap.IsLaplaceHarmonic P) (a : R) (s : ℤˣ) :
    (∀ b : R, ε a = ε b → s * l b < s * l a → T.polarisation P a b s = 0) ∧
      (T.oscRows.E a a P = (l.lowestKType a : ℂ) • P → 0 ≤ s * T.relWeight l a →
        T.polarisation P a a s = ((s * T.relWeight l a : ℤ) : ℂ) • P ∧
          ∀ c : C, T.varSign (a, c) = -s → pderiv (T.varEquiv (a, c)) P = 0) :=
  ⟨fun _ ↦ polarisation_eq_zero_of_isCompactPrimitive hl h_prim h_harm,
    polarisation_self_eq_smul_of_isCompactPrimitive hl h_prim h_harm⟩

omit [Fintype R] in
/-- If each mixed derivative `∂_ac ∂_bc Φ` with `ε a ≠ ε b` vanishes, then the Laplacians of the
rows, which are sums of such derivatives up to sign, kill `Φ`. -/
theorem FockDualPair.IsTermwiseHarmonic.isLaplaceHarmonic {Φ : MvPolynomial ι ℂ}
    (hΦ : T.IsTermwiseHarmonic Φ) : T.IsLaplaceHarmonic Φ := by
  intro a b hab
  rw [fockLaplacian, LinearMap.sum_apply]
  refine sum_eq_zero fun c hc ↦ ?_
  have sign_a : T.varSign (a, c) = -1 := (mem_filter.1 hc).2
  have sign_b : T.varSign (b, c) = 1 := by
    simpa [pairSign, units_ne_iff_eq_neg.1 hab] using sign_a
  simp [glOp, raiseOp, lowerOp, sign_a, sign_b, hΦ a b c hab]

/-- Let `Φ ≠ 0` be termwise harmonic along rows and columns and `K`-highest for both actions, with
the lowest `K`-type of `l` as weight for the row action and any weight `ν` for the column action.
Then `Φ` is a pre-joint harmonic: nonzero, killed by the compact raising operators of the columns
and by the Laplacians of both sides, and highest of weight `l.lowestKType` for the rows. -/
lemma FockDualPair.IsJointHighest.isPreJointHarmonic [DecidableEq R] [DecidableEq C] [Fintype ι]
    {Φ : MvPolynomial ι ℂ} {ν : C → ℤ} (hΦ : T.IsJointHighest l l' Φ l.lowestKType ν) :
    T.IsPreJointHarmonic l l' Φ := by
  obtain ⟨-, raise_col⟩ := hΦ.isKHighest_cols
  exact ⟨hΦ.ne_zero, raise_col, hΦ.isTermwiseHarmonic.isLaplaceHarmonic, hΦ.isKHighest_rows,
    hΦ.isTermwiseHarmonic_swap.isLaplaceHarmonic⟩

/-- A combination `P - c • Q` of pre-joint harmonics (nonzero polynomials killed by the Laplacians
and the compact raising operators of both sides, of weight `l.lowestKType` for the rows) is again
one, unless it is zero. -/
theorem FockDualPair.IsPreJointHarmonic.sub_smul [DecidableEq R] [DecidableEq C] [Fintype ι]
    {P Q : MvPolynomial ι ℂ} {c : ℂ}
    (hP : T.IsPreJointHarmonic l l' P) (hQ : T.IsPreJointHarmonic l l' Q) (h_ne : P ≠ c • Q) :
    T.IsPreJointHarmonic l l' (P - c • Q) := by
  obtain ⟨-, P_raise_col, P_harm_row, ⟨P_weight, P_raise_row⟩, P_harm_col⟩ := hP
  obtain ⟨-, Q_raise_col, Q_harm_row, ⟨Q_weight, Q_raise_row⟩, Q_harm_col⟩ := hQ
  refine ⟨sub_ne_zero.2 h_ne, fun a b hab h_lt ↦ ?_, fun a b hab ↦ ?_,
    ⟨fun a ↦ ?_, fun a b hab h_lt ↦ ?_⟩, fun a b hab ↦ ?_⟩
  · simp [P_raise_col a b hab h_lt, Q_raise_col a b hab h_lt]
  · simp [P_harm_row a b hab, Q_harm_row a b hab]
  · simp [P_weight a, Q_weight a, smul_sub, smul_comm c]
  · simp [P_raise_row a b hab h_lt, Q_raise_row a b hab h_lt]
  · simp [P_harm_col a b hab, Q_harm_col a b hab]

/-! ### The value at the matrix of the matching -/

/-- The 0-1 matrix of the matching, as a point of `ι → ℂ`: the coordinate of the variable `(r, c)`
is `1` if row `r` is matched with column `c`, and `0` if not. -/
noncomputable def FockDualPair.matchingPoint (T : FockDualPair ε ε' ι) (l : HCParam ε)
    (l' : HCParam ε') (i : ι) : ℂ :=
  if T.IsMatchedPair l l' (T.varEquiv.symm i).1 (T.varEquiv.symm i).2 then 1 else 0

/-- The coordinate `(r, c)` of the 0-1 matrix of the matching is nonzero exactly when row `r` is
matched with column `c`. -/
theorem FockDualPair.matchingPoint_ne_zero_iff (r : R) (c : C) :
    T.matchingPoint l l' (T.varEquiv (r, c)) ≠ 0 ↔ T.IsMatchedPair l l' r c := by
  rw [matchingPoint, Equiv.symm_apply_apply, ite_ne_right_iff, and_iff_left one_ne_zero]

/-- The variable `i` is an eigendirection of `F` at the point `x` if `F` is an eigenvector of a
linear vector field `∑ k ∈ S, X (a k) * ∂ (b k)` of which exactly one term, a multiple of `∂ i`,
is nonzero at `x`. -/
inductive DiscreteSeries.IsEigenDirection (F : MvPolynomial ι ℂ) (x : ι → ℂ) (i : ι) : Prop
  /-- The vector field has the terms `X (a k) * ∂ (b k)` for `k ∈ S` and the eigenvalue `μ` on
  `F`. Its term of index `j` differentiates in `i`, and `X (a k)` is nonzero at `x` only for
  `k = j`. -/
  | intro (κ : Type) (S : Finset κ) (a b : κ → ι) (j : κ) (μ : ℂ)
      (mem : j ∈ S) (direction_eq : b j = i) (ne_zero_iff : ∀ k : κ, x (a k) ≠ 0 ↔ k = j)
      (eigen : ∑ k ∈ S, X (a k) * pderiv (b k) F = μ • F) : DiscreteSeries.IsEigenDirection F x i

/-- The translation `G ↦ G (X + x)` commutes with partial derivatives. -/
theorem DiscreteSeries.bind₁_X_add_C_pderiv {τ : Type*} (x : τ → ℂ) (G : MvPolynomial τ ℂ) (i : τ) :
    bind₁ (fun j : τ ↦ X j + MvPolynomial.C (x j)) (pderiv i G) =
      pderiv i (bind₁ (fun j : τ ↦ X j + MvPolynomial.C (x j)) G) := by
  induction G using induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    obtain rfl | h_ne := eq_or_ne n i <;> simp [*]

/-- The constant coefficient of `G (X + x)` is the value of `G` at `x`. -/
theorem DiscreteSeries.coeff_zero_bind₁_X_add_C {τ : Type*} (x : τ → ℂ) (G : MvPolynomial τ ℂ) :
    (bind₁ (fun j : τ ↦ X j + MvPolynomial.C (x j)) G).coeff 0 = eval x G := by
  rw [← constantCoeff_eq]
  induction G using induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp [hp]

/-- A nonzero polynomial `F` that vanishes at `x` depends on a variable `i` that is not an
eigendirection at `x`: `F` is an eigenvector of no linear vector field `∑ k, X (a k) * ∂ (b k)`
whose only nonzero term at `x` is a multiple of `∂ i`. -/
theorem DiscreteSeries.exists_not_isEigenDirection {F : MvPolynomial ι ℂ} {x : ι → ℂ}
    (hF : F ≠ 0) (hx : eval x F = 0) :
    ∃ i : ι, pderiv i F ≠ 0 ∧ ¬IsEigenDirection F x i := by
  classical
  -- Take a monomial of least degree in the Taylor series `H = F (X + x)`. It is not constant, so
  -- its exponent is `t + single i 1` for some variable `i`. Compare the coefficients of `t`.
  let shift (y : ι → ℂ) : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ :=
    bind₁ fun i ↦ X i + MvPolynomial.C (y i)
  have shift_pderiv (G : MvPolynomial ι ℂ) (i : ι) : shift x (pderiv i G) = pderiv i (shift x G) :=
    bind₁_X_add_C_pderiv x G i
  set H : MvPolynomial ι ℂ := shift x F with hH
  have shift_back : shift (-x) H = F := by simp [hH, shift, bind₁_bind₁]
  have H_ne : H ≠ 0 := fun h_zero ↦ hF (by rw [← shift_back, h_zero, map_zero])
  obtain ⟨n, n_mem, n_min⟩ := H.support.exists_min_image Finsupp.degree (support_nonempty.2 H_ne)
  have n_ne : n ≠ 0 := by
    rintro rfl
    exact mem_support_iff.1 n_mem ((coeff_zero_bind₁_X_add_C x F).trans hx)
  obtain ⟨i, hi⟩ : ∃ i : ι, n i ≠ 0 := Finsupp.ne_iff.1 n_ne
  obtain ⟨t, rfl⟩ : ∃ t : ι →₀ ℕ, n = t + Finsupp.single i 1 :=
    le_iff_exists_add'.1 (Finsupp.single_le_iff.2 hi.pos)
  have coeff_low (m : ι →₀ ℕ) (h_le : m.degree ≤ t.degree) : H.coeff m = 0 := by
    by_contra h_ne
    grind [n_min m (mem_support_iff.2 h_ne), Finsupp.degree_single]
  have coeff_pderiv_ne : (pderiv i H).coeff t ≠ 0 := by
    simpa [coeff_pderiv, Nat.cast_add_one_ne_zero] using mem_support_iff.1 n_mem
  refine ⟨i, fun h_zero ↦ coeff_pderiv_ne (by simp [hH, ← shift_pderiv, h_zero]), ?_⟩
  rintro ⟨κ, S, a, b, j, μ, hj, rfl, only_j, eigen⟩
  -- The operators `X u * ∂ v` keep the degree, so they do not contribute to the coefficient of `t`.
  have coeff_X_mul_pderiv (u v : ι) : (X u * pderiv v H).coeff t = 0 := by
    rw [coeff_X_mul']
    refine ite_eq_right_iff.2 fun hu ↦ ?_
    have h_deg : (t - Finsupp.single u 1 + Finsupp.single v 1).degree = t.degree := by
      conv_rhs => rw [← t.sub_add_single_one_cancel (Finsupp.mem_support_iff.1 hu)]
      simp only [map_add, Finsupp.degree_single]
    rw [coeff_pderiv, coeff_low _ h_deg.le, zero_mul]
  refine mul_ne_zero ((only_j j).2 rfl) coeff_pderiv_ne ?_
  calc x (a j) * (pderiv (b j) H).coeff t
      = ∑ k ∈ S, x (a k) * (pderiv (b k) H).coeff t := by
        symm
        refine sum_eq_single_of_mem j hj fun k _ hk ↦ ?_
        rw [of_not_not (mt (only_j k).1 hk), zero_mul]
    _ = (shift x (∑ k ∈ S, X (a k) * pderiv (b k) F)).coeff t := by
        simp only [map_sum, map_mul, shift_pderiv, ← hH, coeff_sum]
        simp [shift, add_mul, coeff_X_mul_pderiv]
    _ = 0 := by simp [eigen, ← hH, coeff_low t le_rfl]

/-- Let `l`, `l'` match and let `s` be the sign of the variable `(r, c)`. Call an integer large if
it exceeds `card C - card R`, and let `ξ = l r - 2γ + card C`, with `γ = T.rowShift` the constant of
the row action, be the centred parameter of row `r`. Either `-s * ξ` is large, or one of three pairs
is matched: `(r, c)` itself, with `s * ξ` large; a pair `(r, d)` with `ε' d = ε' c` and
`s * l' d < s * l' c`; or a pair `(a, c)` with `ε a = ε r` and `s * l r < s * l a`. -/
theorem IsMatch.lt_or_exists_isMatchedPair (hm : IsMatch T l l') (r : R) (c : C) {s : ℤˣ}
    (hs : T.varSign (r, c) = s) :
    card C - card R < -(s : ℤ) * T.centredParam l r ∨
      (card C - card R < (s : ℤ) * T.centredParam l r ∧ T.IsMatchedPair l l' r c) ∨
      (∃ d : C, ε' d = ε' c ∧ s * l' d < s * l' c ∧ T.IsMatchedPair l l' r d) ∨
      ∃ a : R, ε a = ε r ∧ s * l r < s * l a ∧ T.IsMatchedPair l l' a c := by
  refine or_iff_not_imp_left.2 fun h_small ↦ ?_
  -- Row `r` is matched with a column `d`, and the variable `(r, d)` has the sign `s`.
  have r_not_free : ¬|T.centredParam l r| < card R - card C := by grind [Units.val_neg]
  obtain ⟨d, hrd⟩ : ∃ d : C, T.IsMatchedPair l l' r d := (hm.left r).resolve_right r_not_free
  have sign_rd : T.varSign (r, d) = s := by grind [Units.val_neg, Units.ext_iff]
  have block_d : ε' d = ε' c := mul_left_cancel (sign_rd.trans hs.symm)
  have r_large : |(card R - card C : ℤ)| < s * T.centredParam l r := by
    simpa only [sign_rd] using hrd.2
  obtain h_lt | h_eq | h_gt := lt_trichotomy (s * l' d) (s * l' c)
  · exact .inr (.inl ⟨d, block_d, h_lt, hrd⟩)
  · obtain rfl : d = c := hm.hasGap_column.injective (mul_left_cancel₀ s.ne_zero h_eq)
    exact .inl ⟨((le_abs_self _).trans_eq (abs_sub_comm _ _)).trans_lt r_large, hrd⟩
  · -- The parameter of column `c` is further out than that of `d`, so `c` is matched too.
    have param_rd : T.centredParam l r = -T.swap.centredParam l' d := hrd.1
    have c_not_free : ¬|T.swap.centredParam l' c| < card C - card R := by grind
    obtain ⟨a, hac⟩ : ∃ a : R, T.IsMatchedPair l l' a c := (hm.right c).resolve_right c_not_free
    have a_above : s * l r < s * l a := by grind
    have sign_ac : T.varSign (a, c) = s := by grind [Units.ext_iff]
    have block_a : ε a = ε r := mul_left_cancel (mul_right_cancel (sign_ac.trans hs.symm))
    exact .inr (.inr ⟨a, block_a, a_above, hac⟩)

/-- Let `l`, `l'` match and let row `a` be matched with column `c`. If `F` is an eigenvector of the
polarisation `∑ X_ad ∂_rd` from row `r` to row `a`, summed over the columns `d` where `(r, d)` has
the sign of `(r, c)`, then `(r, c)` is an eigendirection of `F` at the 0-1 matrix of the
matching. -/
theorem IsMatch.isEigenDirection_of_polarisation (hm : IsMatch T l l') {F : MvPolynomial ι ℂ}
    {a r : R} {c : C} {μ : ℂ} (hac : T.IsMatchedPair l l' a c)
    (h_eigen : T.polarisation F a r (T.varSign (r, c)) = μ • F) :
    IsEigenDirection F (T.matchingPoint l l') (T.varEquiv (r, c)) := by
  have only_c (d : C) : T.matchingPoint l l' (T.varEquiv (a, d)) ≠ 0 ↔ d = c := by
    grind [matchingPoint_ne_zero_iff, hm.col_eq_of_isMatchedPair]
  have field : ∑ d with T.varSign (r, d) = T.varSign (r, c),
      X (T.varEquiv (a, d)) * pderiv (T.varEquiv (r, d)) F = μ • F := h_eigen
  exact ⟨C, _, fun d ↦ T.varEquiv (a, d), fun d ↦ T.varEquiv (r, d), c, μ, by simp, rfl, only_c,
    field⟩

/-- Let `l`, `l'` match and let row `r` be matched with column `d`. If `F` is an eigenvector of the
polarisation from column `c` to column `d` over the variables with the sign of `(r, c)`, then
`(r, c)` is an eigendirection of `F` at the 0-1 matrix of the matching. -/
theorem IsMatch.isEigenDirection_of_swap_polarisation (hm : IsMatch T l l') {F : MvPolynomial ι ℂ}
    {r : R} {c d : C} {μ : ℂ} (hrd : T.IsMatchedPair l l' r d)
    (h_eigen : T.swap.polarisation F d c (T.swap.varSign (c, r)) = μ • F) :
    IsEigenDirection F (T.matchingPoint l l') (T.varEquiv (r, c)) := by
  have only_r (a : R) : T.matchingPoint l l' (T.varEquiv (a, d)) ≠ 0 ↔ a = r := by
    grind [matchingPoint_ne_zero_iff, hm.row_eq_of_isMatchedPair]
  have field : ∑ a with T.swap.varSign (c, a) = T.swap.varSign (c, r),
      X (T.varEquiv (a, d)) * pderiv (T.varEquiv (a, c)) F = μ • F := h_eigen
  exact ⟨R, _, fun a ↦ T.varEquiv (a, d), fun a ↦ T.varEquiv (a, c), r, μ, by simp, rfl, only_r,
    field⟩

variable [DecidableEq R] [DecidableEq C] [Fintype ι]

/-- Let `l`, `l'` match. A pre-joint harmonic `F` (nonzero, killed by the Laplacians and the compact
raising operators of both sides, of weight `l.lowestKType` for the rows) does not vanish at the
point `T.matchingPoint l l'`, the 0-1 matrix of the matching. -/
theorem IsMatch.eval_matchingPoint_ne_zero (hm : IsMatch T l l') {F : MvPolynomial ι ℂ}
    (hF : T.IsPreJointHarmonic l l' F) :
    eval (T.matchingPoint l l') F ≠ 0 := by
  -- Otherwise `F` depends on a variable `(r, c)` that is not an eigendirection at the point. In
  -- each case of `lt_or_exists_isMatchedPair` a polarisation contradicts this.
  intro value_zero
  obtain ⟨F_ne, raise_col, harm_row, ⟨weight, raise_row⟩, harm_col⟩ := hF
  replace harm_row : T.swap.swap.IsLaplaceHarmonic F := by rwa [swap_swap]
  obtain ⟨i, pderiv_ne, not_eigen⟩ := exists_not_isEigenDirection F_ne value_zero
  obtain ⟨⟨r, c⟩, rfl⟩ := T.varEquiv.surjective i
  let s : ℤˣ := T.varSign (r, c)
  -- If `u` times the centred parameter of row `r` exceeds `card C - card R`, then of the variables
  -- of row `r`, `F` contains only those of sign `u`, and it is an eigenvector of Euler's field on
  -- them.
  have pure (u : ℤˣ) (hu : card C - card R < (u : ℤ) * T.centredParam l r) :
      T.polarisation F r r u = ((u * T.relWeight l r : ℤ) : ℂ) • F ∧
        ∀ d : C, T.varSign (r, d) = -u → pderiv (T.varEquiv (r, d)) F = 0 :=
    polarisation_self_eq_smul_of_isCompactPrimitive hm.hasGap_row.injective raise_row harm_col
      (weight r)
      (hm.sign_mul_relWeight_nonneg r u hu)
  obtain h_large | ⟨h_large, hrc⟩ | ⟨d, block_d, h_lt, hrd⟩ | ⟨a, block_a, h_lt, hac⟩ :=
    hm.lt_or_exists_isMatchedPair r c (s := s) rfl
  · exact pderiv_ne ((pure (-s) h_large).2 c (neg_neg s).symm)
  · exact not_eigen (hm.isEigenDirection_of_polarisation hrc (pure s h_large).1)
  · -- The part of sign `s` of a raising operator of the columns kills `F`.
    have kill : T.swap.polarisation F d c (T.swap.varSign (c, r)) = (0 : ℂ) • F := by
      rw [zero_smul, show T.swap.varSign (c, r) = -s by
        simp [s, mul_right_comm T.globalSign, pairSign]]
      exact polarisation_eq_zero_of_isCompactPrimitive hm.hasGap_column.injective raise_col harm_row
        block_d
        (by simpa using h_lt)
    exact not_eigen (hm.isEigenDirection_of_swap_polarisation hrd kill)
  · -- So does the part of sign `s` of a raising operator of the rows.
    have kill : T.polarisation F a r s = (0 : ℂ) • F := by
      rw [zero_smul]
      exact polarisation_eq_zero_of_isCompactPrimitive hm.hasGap_row.injective raise_row harm_col
        block_a
        h_lt
    exact not_eigen (hm.isEigenDirection_of_polarisation hac kill)

/-- Uniqueness of the joint harmonic up to a scalar. If the parameters `l` of the rows and `l'` of
the columns match, then any two pre-joint harmonics of `T` (nonzero polynomials killed by the
Laplacians and the compact raising operators of both sides, of weight `l.lowestKType` for the rows)
are proportional.

This proves the case of the multiplicity one part of Howe's (GL, GL)-duality that is used. -/
theorem IsMatch.unique (hm : IsMatch T l l') {P Q : MvPolynomial ι ℂ}
    (hP : T.IsPreJointHarmonic l l' P) (hQ : T.IsPreJointHarmonic l l' Q) :
    ∃ c : ℂ, P = c • Q := by
  -- Let `x` be the 0-1 matrix of the matching. The polynomial `P - (P x / Q x) • Q` vanishes at
  -- `x`. If it were not zero, it would be a pre-joint harmonic, and these do not vanish at `x`.
  let x : ι → ℂ := T.matchingPoint l l'
  let c : ℂ := eval x P / eval x Q
  have value_zero : eval x (P - c • Q) = 0 := by
    rw [map_sub, smul_eval, div_mul_cancel₀ _ (hm.eval_matchingPoint_ne_zero hQ), sub_self]
  exact ⟨c, by_contra fun h_ne ↦ hm.eval_matchingPoint_ne_zero (hP.sub_smul hQ h_ne) value_zero⟩

/-- Let `Φ` be a joint harmonic for `T`, `l`, `l'`: a nonzero polynomial, with `l` and `l'`
matching, that is `K`-highest for the row and column actions with the weights of the two lowest
`K`-types, and termwise harmonic for `T` and `T.swap`. Termwise harmonic means no monomial contains
two variables of one column from rows of opposite signs, or two variables of one row from columns of
opposite signs. Then every polynomial `P` that is termwise harmonic in both ways, is `K`-highest of
weight `l.lowestKType` for the row action `T.oscRows`, and is killed by the compact raising
operators for `l'` of the column action `T.swap.oscRows` is a scalar multiple `c • Φ`. -/
theorem IsJointHarmonic.exists_eq_smul_of_row_weight {Φ P : MvPolynomial ι ℂ}
    (hΦ : IsJointHarmonic T l l' Φ) (h_harmonic : T.IsTermwiseHarmonic P)
    (h_harmonic_swap : T.swap.IsTermwiseHarmonic P)
    (h_rows : l.IsKHighest T.oscRows l.lowestKType P)
    (h_cols : T.swap.oscRows.IsCompactPrimitive l' P) :
    ∃ c : ℂ, P = c • Φ := by
  obtain rfl | h_ne := eq_or_ne P 0
  · exact ⟨0, (zero_smul ℂ Φ).symm⟩
  · have hP : T.IsPreJointHarmonic l l' P := ⟨h_ne, h_cols, h_harmonic.isLaplaceHarmonic, h_rows,
      h_harmonic_swap.isLaplaceHarmonic⟩
    exact hΦ.unique hP hΦ.isJointHighest.isPreJointHarmonic

/-- Let `T` be a dual pair in Fock space, whose variables in `ι` are indexed by rows `R` and columns
`C`, and let `Φ` be a joint harmonic for matching `l`, `l'`. That is, `Φ ≠ 0` is `K`-highest, of the
weights of the lowest `K`-types, for the row action `T.oscRows` and the column action
`T.swap.oscRows`, and it is termwise harmonic for `T` and `T.swap`: no monomial has two variables of
one column from rows of opposite signs, or two variables of one row from columns of opposite signs.
Then every polynomial `P` satisfying both termwise harmonic conditions, killed by the compact
raising operators of the row action for `l`, and `K`-highest of weight `l'.lowestKType` for the
column action, is a scalar multiple of `Φ`. -/
theorem IsJointHarmonic.exists_eq_smul_of_column_weight {Φ P : MvPolynomial ι ℂ}
    (hΦ : IsJointHarmonic T l l' Φ) (h_harmonic : T.IsTermwiseHarmonic P)
    (h_harmonic_swap : T.swap.IsTermwiseHarmonic P)
    (h_rows : T.oscRows.IsCompactPrimitive l P)
    (h_cols : l'.IsKHighest T.swap.oscRows l'.lowestKType P) :
    ∃ c : ℂ, P = c • Φ :=
  hΦ.swap.exists_eq_smul_of_row_weight h_harmonic_swap (by rwa [swap_swap]) h_cols
    (by rwa [swap_swap])

end New

end JointHarmonicUnique

end
