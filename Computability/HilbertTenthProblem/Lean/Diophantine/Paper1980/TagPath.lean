import Diophantine.Paper1980.TagProjector

/-!
# The length path of the tag certificate

`EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md`, §4 (12)–(14).  With the marker words
`M₀, M₁` (Boolean, below `R^t`), the initial marker `3^ℓ₀` (`β ≤ ℓ₀`, `ℓ₀ + 2β < m`) and the
endpoint `3q = 3^(mt+1)`, the row form of the length equation

    M₀ + M₁ + 3^(mt+1) = 3^ℓ₀ + 3^(m−β+1) M₀ + 3^(m−β+a) M₁

has digit coefficients at most two on both sides, hence holds digit by digit
(`path_digits`).  Reading it row by row: if row `i` carries exactly one marker, at the
offset `ℓ ≥ β`, then (with `s` the channel of that marker) the successor offset is
`ℓ' = ℓ − β + 1` (zero edge, `s = 0`) or `ℓ − β + a` (one edge, `s = 1`); every marker of
row `i + 1` at a short offset (`< β`) is the successor, so when `ℓ' ≥ β` row `i + 1` again
carries exactly the single marker `ℓ'`; and if `i + 1 = t` the endpoint forces `ℓ' = 1`
(`row_step`).  The one-edge constraint `ℓ + a + β < m` comes from the projector
(`M₁`-markers are at most `A`) and the compiler constant `C > 3K·3^a`.
-/

namespace Jones1980

namespace Ternary

/-- The marker coefficient `dg M₀ p + dg M₁ p`. -/
def coef (M0 M1 p : ℕ) : ℕ := dg M0 p + dg M1 p

section Path

variable {M0 M1 m t β a ℓ₀ : ℕ} (hm : 1 ≤ m) (ht : 1 ≤ t) (hβ : 2 ≤ β) (ha : 2 ≤ a)
  (hβm : 3 * β < m)
  (hM0 : Bool3 M0) (hM1 : Bool3 M1) (hM0lt : M0 < 3 ^ (m * t)) (hM1lt : M1 < 3 ^ (m * t))
  (hℓ₀ : β ≤ ℓ₀) (hℓ₀m : ℓ₀ + 2 * β < m)
  (hM1α : ∀ p, dg M1 p = 1 → p % m + a + β < m)
  (heq : M0 + M1 + 3 ^ (m * t + 1) =
    3 ^ ℓ₀ + 3 ^ (m - (β - 1)) * M0 + 3 ^ (m - (β - 1) + (a - 1)) * M1)

include hm ht hβ ha hβm hM0 hM1 hM0lt hM1lt hℓ₀ hℓ₀m hM1α heq

omit hm ht hβ ha hβm hM1 hM1lt hℓ₀ hℓ₀m hM1α heq in
theorem dg_M0_top {p : ℕ} (hp : m * t ≤ p) : dg M0 p = 0 :=
  dg_eq_zero_of_lt (lt_of_lt_of_le hM0lt (Nat.pow_le_pow_right (by norm_num) hp))

omit hm ht hβ ha hβm hM0 hM0lt hℓ₀ hℓ₀m hM1α heq in
theorem dg_M1_top {p : ℕ} (hp : m * t ≤ p) : dg M1 p = 0 :=
  dg_eq_zero_of_lt (lt_of_lt_of_le hM1lt (Nat.pow_le_pow_right (by norm_num) hp))

omit hm ht hβ ha hβm hℓ₀ hℓ₀m hM1α heq in
theorem coef_top {p : ℕ} (hp : m * t ≤ p) : coef M0 M1 p = 0 := by
  unfold coef; rw [dg_M0_top hM0 hM0lt hp, dg_M1_top hM1 hM1lt hp]

/-- The length equation holds digit by digit. -/
theorem path_digits (p : ℕ) :
    coef M0 M1 p + (if p = m * t + 1 then 1 else 0) =
      (if p = ℓ₀ then 1 else 0) + dg (3 ^ (m - (β - 1)) * M0) p +
        dg (3 ^ (m - (β - 1) + (a - 1)) * M1) p := by
  -- both sides have digit coefficients at most two
  have hL : ∀ p, dg M0 p + dg M1 p + dg (3 ^ (m * t + 1)) p ≤ 2 := by
    intro p
    rw [dg_pow]
    split_ifs with h
    · subst h
      rw [dg_M0_top hM0 hM0lt (by omega), dg_M1_top hM1 hM1lt (by omega)]
      omega
    · have := hM0 p; have := hM1 p; omega
  have hR : ∀ p, dg (3 ^ ℓ₀) p + dg (3 ^ (m - (β - 1)) * M0) p +
      dg (3 ^ (m - (β - 1) + (a - 1)) * M1) p ≤ 2 := by
    intro p
    rw [dg_pow]
    have h1 := (hM0.mul_pow (m - (β - 1))) p
    have h2 := (hM1.mul_pow (m - (β - 1) + (a - 1))) p
    split_ifs with h
    · subst h
      rw [dg_mul_pow_of_lt (s := m - (β - 1)) M0 (by omega),
        dg_mul_pow_of_lt (s := m - (β - 1) + (a - 1)) M1 (by omega)]
      omega
    · omega
  have e1 := dg_add3_of_le_two hL p
  have e2 := dg_add3_of_le_two hR p
  rw [heq] at e1
  rw [e2] at e1
  unfold coef
  rw [dg_pow, dg_pow] at *
  omega

omit ht hM0lt hM1lt heq in
/-- The shifted `M₀` at a position of row `i + 1` reads `M₀` at row `i`, offset `k + β − 1`. -/
theorem dg_shift_M0 {i k : ℕ} :
    dg (3 ^ (m - (β - 1)) * M0) (m * (i + 1) + k) = dg M0 (m * i + (k + (β - 1))) := by
  have e : m * (i + 1) + k = (m - (β - 1)) + (m * i + (k + (β - 1))) := by
    rw [Nat.mul_succ]; omega
  rw [e, dg_mul_pow_add]

omit ht hM0lt hM1lt heq in
/-- The shifted `M₁` at a position of row `i + 1`. -/
theorem dg_shift_M1 {i k : ℕ} (hk : a ≤ m * i + k + β) :
    dg (3 ^ (m - (β - 1) + (a - 1)) * M1) (m * (i + 1) + k) =
      dg M1 (m * i + k + β - a) := by
  have e : m * (i + 1) + k = (m - (β - 1) + (a - 1)) + (m * i + k + β - a) := by
    rw [Nat.mul_succ]; omega
  rw [e, dg_mul_pow_add]

omit ht hM0lt hM1lt heq in
theorem dg_shift_M1_zero {i k : ℕ} (hk : m * i + k + β < a) :
    dg (3 ^ (m - (β - 1) + (a - 1)) * M1) (m * (i + 1) + k) = 0 := by
  apply dg_mul_pow_of_lt
  rw [Nat.mul_succ]; omega

omit hm ht hβ ha hβm hM0 hM0lt hM1lt hℓ₀ hℓ₀m heq in
/-- The offset constraint of the `M₁`-markers, in row form. -/
theorem M1_offset {i k : ℕ} (hk : k < m) (h : dg M1 (m * i + k) = 1) : k + a + β < m := by
  have := hM1α _ h
  rwa [Nat.mul_add_mod, Nat.mod_eq_of_lt hk] at this

/-- Row `0` carries exactly the initial marker. -/
theorem row_zero_marker : ∀ k, k < m → coef M0 M1 k = if k = ℓ₀ then 1 else 0 := by
  have hmt : m ≤ m * t := Nat.le_mul_of_pos_right _ ht
  -- a marker of row `0` at a short offset would have to be the initial marker
  have hshort : ∀ k, k < β - 1 → coef M0 M1 k = 0 := by
    intro k hk
    have h := path_digits hm ht hβ ha hβm hM0 hM1 hM0lt hM1lt hℓ₀ hℓ₀m hM1α heq k
    rw [if_neg (show ¬ k = m * t + 1 by omega), if_neg (show ¬ k = ℓ₀ by omega),
      dg_mul_pow_of_lt (s := m - (β - 1)) M0 (by omega),
      dg_mul_pow_of_lt (s := m - (β - 1) + (a - 1)) M1 (by omega)] at h
    omega
  intro k hk
  have h := path_digits hm ht hβ ha hβm hM0 hM1 hM0lt hM1lt hℓ₀ hℓ₀m hM1α heq k
  rw [if_neg (show ¬ k = m * t + 1 by omega)] at h
  -- the shifted words vanish on row `0`
  have h0 : dg (3 ^ (m - (β - 1)) * M0) k = 0 := by
    rcases Nat.lt_or_ge k (m - (β - 1)) with hlt | hge
    · exact dg_mul_pow_of_lt M0 hlt
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hge
      rw [dg_mul_pow_add]
      have := hshort k' (by omega)
      unfold coef at this
      omega
  have h1 : dg (3 ^ (m - (β - 1) + (a - 1)) * M1) k = 0 := by
    rcases Nat.lt_or_ge k (m - (β - 1) + (a - 1)) with hlt | hge
    · exact dg_mul_pow_of_lt M1 hlt
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hge
      rw [dg_mul_pow_add]
      have := hshort k' (by omega)
      unfold coef at this
      omega
  rw [h0, h1] at h
  omega

/-- The row step.  If row `i` carries exactly one marker, at the offset `ℓ` with `β ≤ ℓ` and
`ℓ + 2β < m`, let `s` be its channel and `ℓ'` the successor offset.  Then `ℓ' + 2β < m`;
every short marker of row `i + 1` is the successor; if `ℓ' ≥ β` row `i + 1` carries exactly
the marker `ℓ'`; and if `i + 1 = t` then `ℓ' = 1`. -/
theorem row_step {i ℓ s ℓ' : ℕ} (hit : i + 1 ≤ t) (hℓ : β ≤ ℓ) (hℓm : ℓ + 2 * β < m)
    (hrow : ∀ k, k < m → coef M0 M1 (m * i + k) = if k = ℓ then 1 else 0)
    (hs : s = dg M1 (m * i + ℓ)) (hℓ' : ℓ' = ℓ - β + (if s = 1 then a else 1)) :
    ℓ' + 2 * β < m ∧
    (i + 1 < t → ∀ k, k < β → coef M0 M1 (m * (i + 1) + k) = 1 → k = ℓ') ∧
    (i + 1 < t → β ≤ ℓ' → ∀ k, k < m → coef M0 M1 (m * (i + 1) + k) = if k = ℓ' then 1 else 0) ∧
    (i + 1 = t → ℓ' = 1) := by
  have hs1 : s ≤ 1 := by rw [hs]; exact hM1 _
  have hℓ'0 : s = 0 → ℓ' = ℓ - β + 1 := fun h => by rw [hℓ', if_neg (by omega)]
  have hℓ'1 : s = 1 → ℓ' = ℓ - β + a := fun h => by rw [hℓ', if_pos h]
  -- the marker of row `i` is in exactly one channel
  have hcoefℓ : coef M0 M1 (m * i + ℓ) = 1 := by rw [hrow ℓ (by omega), if_pos rfl]
  have hM0ℓ : dg M0 (m * i + ℓ) + s = 1 := by unfold coef at hcoefℓ; rw [hs]; exact hcoefℓ
  have hsa : s = 1 → ℓ + a + β < m := fun h1 => M1_offset hM1 hM1α (by omega) (hs ▸ h1)
  have hℓ'm : ℓ' + 2 * β < m := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [hℓ'0 h0]; omega
    · have h1 : s = 1 := by omega
      rw [hℓ'1 h1]; have := hsa h1; omega
  have hmi1 : m * (i + 1) = m * i + m := Nat.mul_add_one m i
  have hne2 : ∀ k, m * (i + 1) + k ≠ ℓ₀ := fun k h => by omega
  have hne1 : i + 1 < t → ∀ k, k < m → m * (i + 1) + k ≠ m * t + 1 := by
    intro hit' k hk h
    have : m * (i + 1) + m ≤ m * t := by
      rw [← Nat.mul_add_one]; exact Nat.mul_le_mul_left _ hit'
    omega
  -- (A) the `M₀` shift read on row `i`
  have hA : ∀ k, k + (β - 1) < m →
      dg (3 ^ (m - (β - 1)) * M0) (m * (i + 1) + k) =
        if k + (β - 1) = ℓ ∧ s = 0 then 1 else 0 := by
    intro k hkm
    rw [dg_shift_M0 hm hβ ha hβm hM0 hM1 hℓ₀ hℓ₀m hM1α]
    have hc := hrow (k + (β - 1)) hkm
    unfold coef at hc
    have h0 := hM0 (m * i + (k + (β - 1)))
    have h1 := hM1 (m * i + (k + (β - 1)))
    by_cases he : k + (β - 1) = ℓ
    · rw [he] at hc ⊢ h0 h1
      rw [if_pos rfl] at hc
      by_cases hs0 : s = 0
      · rw [if_pos ⟨rfl, hs0⟩]; omega
      · rw [if_neg (fun h => hs0 h.2)]; omega
    · rw [if_neg he] at hc
      rw [if_neg (fun h => he h.1)]
      omega
  -- (A') the `M₀` shift read on a short offset of row `i + 1`
  have hA' : ∀ k, k < m → m ≤ k + (β - 1) →
      dg (3 ^ (m - (β - 1)) * M0) (m * (i + 1) + k) =
        dg M0 (m * (i + 1) + (k + (β - 1) - m)) := by
    intro k hk hkm
    rw [dg_shift_M0 hm hβ ha hβm hM0 hM1 hℓ₀ hℓ₀m hM1α]
    congr 1; omega
  -- (C) the `M₁` shift, read on row `i` or below
  have hC : ∀ k, k < m → m * i + k + β - a < m * (i + 1) →
      dg (3 ^ (m - (β - 1) + (a - 1)) * M1) (m * (i + 1) + k) =
        if a ≤ m * i + k + β ∧ m * i + k + β - a = m * i + ℓ ∧ s = 1 then 1 else 0 := by
    intro k hk hkm
    rcases Nat.lt_or_ge (m * i + k + β) a with hlt | hge
    · rw [dg_shift_M1_zero hm hβ ha hβm hM0 hM1 hℓ₀ hℓ₀m hM1α hlt, if_neg (fun h => by omega)]
    rw [dg_shift_M1 hm hβ ha hβm hM0 hM1 hℓ₀ hℓ₀m hM1α hge]
    rcases Nat.lt_or_ge (m * i + k + β - a) (m * i) with hlo | hhi
    · -- an earlier row: an `M₁`-marker there would violate the offset bound
      rw [if_neg (fun h => by omega)]
      by_contra hne
      have h1 : dg M1 (m * i + k + β - a) = 1 := by have := hM1 (m * i + k + β - a); omega
      have hα := hM1α _ h1
      have ham : a < m := by omega
      have hi1 : 1 ≤ i := by
        by_contra h0; push Not at h0
        have : i = 0 := by omega
        subst this; simp at hlo
      have hmi : m * (i - 1) + m = m * i := by
        have e : i = (i - 1) + 1 := by omega
        conv_rhs => rw [e]
        rw [Nat.mul_add_one]
      have hP : m * i + k + β - a = m * (i - 1) + (m + k + β - a) := by omega
      have hoff : m + k + β - a < m := by omega
      rw [hP, Nat.mul_add_mod, Nat.mod_eq_of_lt hoff] at hα
      omega
    · -- a position of row `i`
      obtain ⟨k', hk'⟩ : ∃ k', m * i + k + β - a = m * i + k' :=
        ⟨m * i + k + β - a - m * i, by omega⟩
      have hk'm : k' < m := by omega
      rw [hk']
      have hc := hrow k' hk'm
      unfold coef at hc
      have h0 := hM0 (m * i + k'); have h1 := hM1 (m * i + k')
      by_cases he : k' = ℓ
      · subst he
        rw [if_pos rfl] at hc
        by_cases hs1' : s = 1
        · rw [if_pos ⟨hge, rfl, hs1'⟩]; omega
        · rw [if_neg (fun h => hs1' h.2.2)]; omega
      · rw [if_neg he] at hc
        rw [if_neg (fun h => he (by omega))]
        omega
  -- (C') the `M₁` shift read on a short offset of row `i + 1`
  have hC' : ∀ k, k < m → a ≤ m * i + k + β → m * (i + 1) ≤ m * i + k + β - a →
      dg (3 ^ (m - (β - 1) + (a - 1)) * M1) (m * (i + 1) + k) =
        dg M1 (m * (i + 1) + (m * i + k + β - a - m * (i + 1))) := by
    intro k hk hge hhi
    rw [dg_shift_M1 hm hβ ha hβm hM0 hM1 hℓ₀ hℓ₀m hM1α hge]
    congr 1; omega
  -- the short-marker argument
  have hshortsucc : i + 1 < t → ∀ k, k < β → coef M0 M1 (m * (i + 1) + k) = 1 → k = ℓ' := by
    intro hit' k hk hc
    have h := path_digits hm ht hβ ha hβm hM0 hM1 hM0lt hM1lt hℓ₀ hℓ₀m hM1α heq (m * (i + 1) + k)
    rw [if_neg (hne1 hit' k (by omega)), if_neg (hne2 k), hc, hA k (by omega),
      hC k (by omega) (by omega)] at h
    by_cases h1 : k + (β - 1) = ℓ ∧ s = 0
    · rw [hℓ'0 h1.2]; omega
    · rw [if_neg h1] at h
      by_cases h2 : a ≤ m * i + k + β ∧ m * i + k + β - a = m * i + ℓ ∧ s = 1
      · rw [hℓ'1 h2.2.2]; omega
      · rw [if_neg h2] at h; omega
  refine ⟨hℓ'm, hshortsucc, ?_, ?_⟩
  · -- when the successor is not short, row `i + 1` carries exactly the successor
    intro hit' hℓ'β k hk
    have hshort : ∀ k', k' < β → coef M0 M1 (m * (i + 1) + k') = 0 := by
      intro k' hk'
      by_contra hne
      -- the coefficient is at most one at a short offset: the digit equation caps it
      have h := path_digits hm ht hβ ha hβm hM0 hM1 hM0lt hM1lt hℓ₀ hℓ₀m hM1α heq (m * (i + 1) + k')
      rw [if_neg (hne1 hit' k' (by omega)), if_neg (hne2 k'), hA k' (by omega),
        hC k' (by omega) (by omega)] at h
      have h1 : coef M0 M1 (m * (i + 1) + k') = 1 := by
        split_ifs at h <;> omega
      have := hshortsucc hit' k' hk' h1
      omega
    have h := path_digits hm ht hβ ha hβm hM0 hM1 hM0lt hM1lt hℓ₀ hℓ₀m hM1α heq (m * (i + 1) + k)
    rw [if_neg (hne1 hit' k hk), if_neg (hne2 k)] at h
    -- the `M₀` contribution
    have hAk : dg (3 ^ (m - (β - 1)) * M0) (m * (i + 1) + k) =
        if k + (β - 1) = ℓ ∧ s = 0 then 1 else 0 := by
      rcases Nat.lt_or_ge (k + (β - 1)) m with hkm | hkm
      · exact hA k hkm
      · rw [hA' k hk hkm]
        have := hshort (k + (β - 1) - m) (by omega)
        unfold coef at this
        rw [if_neg (fun h => by omega)]
        omega
    -- the `M₁` contribution
    have hCk : dg (3 ^ (m - (β - 1) + (a - 1)) * M1) (m * (i + 1) + k) =
        if a ≤ m * i + k + β ∧ m * i + k + β - a = m * i + ℓ ∧ s = 1 then 1 else 0 := by
      rcases Nat.lt_or_ge (m * i + k + β - a) (m * (i + 1)) with hkm | hkm
      · exact hC k hk hkm
      · have hge : a ≤ m * i + k + β := by omega
        rw [hC' k hk hge hkm]
        have := hshort (m * i + k + β - a - m * (i + 1)) (by omega)
        unfold coef at this
        rw [if_neg (fun h => by omega)]
        omega
    rw [hAk, hCk] at h
    by_cases h1 : k + (β - 1) = ℓ ∧ s = 0
    · rw [if_pos h1] at h
      rw [if_neg (fun h2 => by omega)] at h
      rw [if_pos (by rw [hℓ'0 h1.2]; omega)]
      omega
    · rw [if_neg h1] at h
      by_cases h2 : a ≤ m * i + k + β ∧ m * i + k + β - a = m * i + ℓ ∧ s = 1
      · rw [if_pos h2] at h
        rw [if_pos (by rw [hℓ'1 h2.2.2]; omega)]
        omega
      · rw [if_neg h2] at h
        rw [if_neg (fun h3 => ?_)]
        · omega
        · -- `k = ℓ'` would make one of the two contributions fire
          rcases Nat.eq_zero_or_pos s with hs0 | hs0
          · exact h1 ⟨by rw [hℓ'0 hs0] at h3; omega, hs0⟩
          · have hs1' : s = 1 := by omega
            exact h2 ⟨by rw [hℓ'1 hs1'] at h3; omega, by rw [hℓ'1 hs1'] at h3; omega, hs1'⟩
  · -- the endpoint forces the successor offset `1`
    intro hit'
    subst hit'
    have hℓ'lt : ℓ' < m := by omega
    have h := path_digits hm ht hβ ha hβm hM0 hM1 hM0lt hM1lt hℓ₀ hℓ₀m hM1α heq (m * (i + 1) + ℓ')
    rw [coef_top hM0 hM1 hM0lt hM1lt (Nat.le_add_right _ _), if_neg (hne2 ℓ'),
      hA ℓ' (by omega), hC ℓ' hℓ'lt (by omega)] at h
    -- the successor position carries a `1` on the right
    have hone : (if ℓ' + (β - 1) = ℓ ∧ s = 0 then 1 else 0) +
        (if a ≤ m * i + ℓ' + β ∧ m * i + ℓ' + β - a = m * i + ℓ ∧ s = 1 then 1 else 0) = 1 := by
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · rw [if_pos ⟨by rw [hℓ'0 hs0]; omega, hs0⟩, if_neg (fun h => by omega)]
      · have hs1' : s = 1 := by omega
        have hsa' := hsa hs1'
        rw [if_neg (fun h => by omega), if_pos ⟨by rw [hℓ'1 hs1']; omega,
          by rw [hℓ'1 hs1']; omega, hs1'⟩]
    simp only [zero_add] at h
    rw [hone] at h
    split_ifs at h <;> omega

end Path

end Ternary

end Jones1980
