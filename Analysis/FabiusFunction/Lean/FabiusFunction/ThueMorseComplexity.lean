import FabiusFunction.ThueMorseRecurrence
import FabiusFunction.ThueMorseAperiodicity
import FabiusFunction.ThueMorseBinomialLog
import Mathlib.Data.Set.Card

/-!
# Linear factor complexity of the Thue–Morse word

The number `p(ℓ)` of distinct length-`ℓ` factors of the Thue–Morse word
satisfies `ℓ + 1 ≤ p(ℓ)` for every `ℓ`, and `p(ℓ) ≤ 6ℓ - 4` once
`ℓ ≥ 1` — the atlas's elementary linear bound, here in a sharpened form.
The side condition is not cosmetic: `p(0) = 1`, whereas `6·0 - 4` is `0`
in truncated `ℕ` subtraction.  This module proves both halves.

* `thueMorseWindow` / `thueMorseFactorSet` / `thueMorseComplexity` — the
  window at position `i`, the set of factors of length `ℓ`, and its
  (finite) cardinality.
* `thueMorseWindow_eq_reconstruct` — a window of length `ℓ ≤ 2^k` is
  determined by its offset `i % 2^k` in the aligned level-`k` block
  together with the two adjacent block bits, and the *second* block bit
  is consulted only when `i % 2^k + j ≥ 2^k`.
* `card_image_thueMorseWindow_le'` — **sharpened upper bound**: an
  offset with `i % 2^k + ℓ ≤ 2^k` keeps the whole window inside one
  block, so it needs only one block bit (`2` windows per offset); only
  the `ℓ - 1` offsets in `[2^k - ℓ + 1, 2^k)` straddle a boundary and
  need both bits (`4` windows per offset).  Splitting the image
  accordingly gives at most `2·2^k + 2·(ℓ - 1)` distinct windows, hence
  `p(ℓ) ≤ 2·2^k + 2·(ℓ - 1)` (`thueMorseComplexity_le'`) and, with
  `2^k < 2ℓ` minimal, `p(ℓ) ≤ 6ℓ - 4` for `ℓ ≥ 1`
  (`thueMorseComplexity_le_six_mul_sub_four`).
* `card_image_thueMorseWindow_le` / `thueMorseComplexity_le` /
  `thueMorseComplexity_lt` — the earlier, weaker bounds `4·2^k` and
  `p(ℓ) < 8ℓ` (the latter again only for `ℓ ≥ 1`), kept as corollaries.
* `thueMorseComplexity_lt_succ` — **strict growth**, the Morse–Hedlund
  argument: if some length had no more factors than the previous one,
  every factor would extend uniquely to the right; the finitely many
  windows would then evolve deterministically, the pigeonhole principle
  would force two equal windows, and the word would be eventually
  periodic — contradicting `thueMorseSign_not_eventually_periodic`.
  The final step, from two equal windows at positions `a < b` to
  eventual periodicity, is isolated in a private lemma so that both
  orderings of the pigeonhole pair share one proof.
* `le_thueMorseComplexity` — **lower bound** `ℓ + 1 ≤ p(ℓ)`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The length-`ℓ` window of the Thue–Morse word at position `i`. -/
def thueMorseWindow (ℓ i : ℕ) : Fin ℓ → ℕ := fun j => thueMorseBit (i + j)

/-- Evaluating a Thue–Morse window at offset `j` reads the bit at position
`i+j`. -/
@[simp] theorem thueMorseWindow_apply (ℓ i : ℕ) (j : Fin ℓ) :
    thueMorseWindow ℓ i j = thueMorseBit (i + j) := rfl

/-- The set of length-`ℓ` factors of the Thue–Morse word. -/
def thueMorseFactorSet (ℓ : ℕ) : Set (Fin ℓ → ℕ) :=
  Set.range (thueMorseWindow ℓ)

/-- The factor complexity `p(ℓ)`. -/
noncomputable def thueMorseComplexity (ℓ : ℕ) : ℕ :=
  (thueMorseFactorSet ℓ).ncard

/-! ### The upper bound -/

/-- A window of length `ℓ ≤ 2^k` is determined by its offset in the
aligned level-`k` block and the two adjacent block bits. -/
theorem thueMorseWindow_eq_reconstruct (k ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ k)
    (i : ℕ) :
    thueMorseWindow ℓ i = fun j : Fin ℓ =>
      if i % 2 ^ k + j < 2 ^ k
      then (thueMorseBit (i / 2 ^ k) + thueMorseBit (i % 2 ^ k + j)) % 2
      else (thueMorseBit (i / 2 ^ k + 1) +
        thueMorseBit (i % 2 ^ k + j - 2 ^ k)) % 2 := by
  funext j
  have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdm := Nat.div_add_mod i (2 ^ k)
  have hmod : i % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpow
  have hj : (j : ℕ) < ℓ := j.isLt
  by_cases hcase : i % 2 ^ k + j < 2 ^ k
  · rw [thueMorseWindow_apply, if_pos hcase]
    have hi : i + j = (i / 2 ^ k) * 2 ^ k + (i % 2 ^ k + j) := by
      have h : (i / 2 ^ k) * 2 ^ k = 2 ^ k * (i / 2 ^ k) := by ring
      omega
    rw [hi, thueMorseBit_block_concat k _ _ hcase]
  · rw [thueMorseWindow_apply, if_neg hcase]
    have hlt : i % 2 ^ k + j - 2 ^ k < 2 ^ k := by omega
    have hi : i + j = (i / 2 ^ k + 1) * 2 ^ k +
        (i % 2 ^ k + j - 2 ^ k) := by
      have h : (i / 2 ^ k + 1) * 2 ^ k = 2 ^ k * (i / 2 ^ k) + 2 ^ k := by
        ring
      omega
    rw [hi, thueMorseBit_block_concat k _ _ hlt]

/-- **The sharpened window count**: at most `2·2^k + 2·(ℓ - 1)` distinct
windows of length `ℓ ≤ 2^k`, over any finite set of starting positions.

The offsets `r = i % 2^k` split in two.  If `r < 2^k - (ℓ - 1)` the whole
window lies inside the aligned level-`k` block, so it is a function of
the pair `(r, t(i / 2^k))` alone — at most `2·(2^k - (ℓ - 1))` windows.
Otherwise `r` is one of the `ℓ - 1` offsets in `[2^k - ℓ + 1, 2^k)` and
the window is a function of the triple `(r, t(i / 2^k), t(i / 2^k + 1))`
— at most `4·(ℓ - 1)` windows.  The two counts add to
`2·2^k + 2·(ℓ - 1)`. -/
theorem card_image_thueMorseWindow_le' (k ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ k)
    (s : Finset ℕ) :
    (s.image (thueMorseWindow ℓ)).card ≤ 2 * 2 ^ k + 2 * (ℓ - 1) := by
  classical
  have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
  rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓ0
  · -- length `0`: the empty window is the only one
    subst hℓ0
    refine le_trans (Finset.card_le_one.mpr ?_) ?_
    · intro a _ b _
      funext j
      exact absurd j.isLt (Nat.not_lt_zero _)
    · omega
  · obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 := ⟨ℓ - 1, by omega⟩
    -- windows that stay inside one block: offset plus one block bit
    set recon₁ : ℕ × ℕ → (Fin (d + 1) → ℕ) := fun p =>
      fun j : Fin (d + 1) =>
        (p.2 + thueMorseBit (p.1 + j)) % 2 with hrecon₁
    -- windows that straddle a boundary: offset plus both block bits
    set recon₂ : ℕ × ℕ × ℕ → (Fin (d + 1) → ℕ) := fun p =>
      fun j : Fin (d + 1) =>
        if p.1 + j < 2 ^ k
        then (p.2.1 + thueMorseBit (p.1 + j)) % 2
        else (p.2.2 + thueMorseBit (p.1 + j - 2 ^ k)) % 2 with hrecon₂
    have hsub : s.image (thueMorseWindow (d + 1)) ⊆
        ((range (2 ^ k - d)) ×ˢ (range 2)).image recon₁ ∪
          ((Finset.Ico (2 ^ k - d) (2 ^ k)) ×ˢ (range 2) ×ˢ
            (range 2)).image recon₂ := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      have hmod : i % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpow
      have ha : thueMorseBit (i / 2 ^ k) < 2 := by
        have := thueMorseBit_le_one (i / 2 ^ k)
        omega
      have hb : thueMorseBit (i / 2 ^ k + 1) < 2 := by
        have := thueMorseBit_le_one (i / 2 ^ k + 1)
        omega
      by_cases hcase : i % 2 ^ k < 2 ^ k - d
      · -- the whole window sits inside one level-`k` block
        refine Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨(i % 2 ^ k, thueMorseBit (i / 2 ^ k)), ?_, ?_⟩)
        · refine Finset.mem_product.mpr ⟨?_, ?_⟩
          · show i % 2 ^ k ∈ range (2 ^ k - d)
            exact Finset.mem_range.mpr hcase
          · show thueMorseBit (i / 2 ^ k) ∈ range 2
            exact Finset.mem_range.mpr ha
        · have hval : thueMorseWindow (d + 1) i =
              fun j : Fin (d + 1) =>
                (thueMorseBit (i / 2 ^ k) +
                  thueMorseBit (i % 2 ^ k + j)) % 2 := by
            funext j
            have hj : (j : ℕ) < d + 1 := j.isLt
            have hlt : i % 2 ^ k + (j : ℕ) < 2 ^ k := by omega
            have hdm := Nat.div_add_mod i (2 ^ k)
            have hi : i + (j : ℕ) =
                (i / 2 ^ k) * 2 ^ k + (i % 2 ^ k + (j : ℕ)) := by
              have h : (i / 2 ^ k) * 2 ^ k = 2 ^ k * (i / 2 ^ k) := by
                ring
              omega
            show thueMorseBit (i + (j : ℕ)) =
              (thueMorseBit (i / 2 ^ k) +
                thueMorseBit (i % 2 ^ k + (j : ℕ))) % 2
            rw [hi, thueMorseBit_block_concat k _ _ hlt]
          exact hval.symm
      · -- the window straddles a block boundary
        refine Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(i % 2 ^ k, thueMorseBit (i / 2 ^ k),
            thueMorseBit (i / 2 ^ k + 1)), ?_, ?_⟩)
        · refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
          · show i % 2 ^ k ∈ Finset.Ico (2 ^ k - d) (2 ^ k)
            exact Finset.mem_Ico.mpr ⟨by omega, hmod⟩
          · show thueMorseBit (i / 2 ^ k) ∈ range 2
            exact Finset.mem_range.mpr ha
          · show thueMorseBit (i / 2 ^ k + 1) ∈ range 2
            exact Finset.mem_range.mpr hb
        · exact (thueMorseWindow_eq_reconstruct k (d + 1) hℓ i).symm
    have hcardA :
        (((range (2 ^ k - d)) ×ˢ (range 2)).image recon₁).card
          ≤ (2 ^ k - d) * 2 := by
      calc (((range (2 ^ k - d)) ×ˢ (range 2)).image recon₁).card
          ≤ ((range (2 ^ k - d)) ×ˢ (range 2)).card := Finset.card_image_le
        _ = (2 ^ k - d) * 2 := by
            rw [Finset.card_product, Finset.card_range, Finset.card_range]
    have hIco : (Finset.Ico (2 ^ k - d) (2 ^ k)).card = d := by
      rw [Nat.card_Ico]
      omega
    have hcardB :
        (((Finset.Ico (2 ^ k - d) (2 ^ k)) ×ˢ (range 2) ×ˢ
          (range 2)).image recon₂).card ≤ 4 * d := by
      calc (((Finset.Ico (2 ^ k - d) (2 ^ k)) ×ˢ (range 2) ×ˢ
              (range 2)).image recon₂).card
          ≤ ((Finset.Ico (2 ^ k - d) (2 ^ k)) ×ˢ (range 2) ×ˢ
              (range 2)).card := Finset.card_image_le
        _ = 4 * d := by
            rw [Finset.card_product, Finset.card_product,
              Finset.card_range, hIco]
            ring
    refine le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_union_le _ _)
        (le_trans (Nat.add_le_add hcardA hcardB) ?_))
    omega

/-- **At most `4·2^k` distinct windows** of length `ℓ ≤ 2^k`, over any
finite set of starting positions.  A weaker corollary of
`card_image_thueMorseWindow_le'`, kept for compatibility. -/
theorem card_image_thueMorseWindow_le (k ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ k)
    (s : Finset ℕ) :
    (s.image (thueMorseWindow ℓ)).card ≤ 4 * 2 ^ k := by
  have h := card_image_thueMorseWindow_le' k ℓ hℓ s
  omega

/-- Every factor occurs among the first `15·2^k + 1` windows, so the
factor set is that finite image. -/
theorem thueMorseFactorSet_eq_image (k ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ k) :
    thueMorseFactorSet ℓ =
      ↑((range (15 * 2 ^ k + 1)).image (thueMorseWindow ℓ)) := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨i', _, h2, h3⟩ :=
      thueMorseBit_uniformly_recurrent k ℓ i 0 hℓ
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i', ?_, ?_⟩)
    · exact Finset.mem_range.mpr (by omega)
    · funext j
      exact h3 j j.isLt
  · rintro hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
    exact ⟨i, rfl⟩

/-- The factor set is finite. -/
theorem thueMorseFactorSet_finite (ℓ : ℕ) :
    (thueMorseFactorSet ℓ).Finite := by
  rw [thueMorseFactorSet_eq_image ℓ ℓ (Nat.lt_two_pow_self).le]
  exact Finset.finite_toSet _

/-- **Sharpened upper bound at every covering level**:
`p(ℓ) ≤ 2·2^k + 2·(ℓ - 1)` for `ℓ ≤ 2^k`. -/
theorem thueMorseComplexity_le' (k ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ k) :
    thueMorseComplexity ℓ ≤ 2 * 2 ^ k + 2 * (ℓ - 1) := by
  rw [thueMorseComplexity, thueMorseFactorSet_eq_image k ℓ hℓ,
    Set.ncard_coe_finset]
  exact card_image_thueMorseWindow_le' k ℓ hℓ _

/-- Upper bound at every covering level: `p(ℓ) ≤ 4·2^k` for `ℓ ≤ 2^k`.
A weaker corollary of `thueMorseComplexity_le'`. -/
theorem thueMorseComplexity_le (k ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ k) :
    thueMorseComplexity ℓ ≤ 4 * 2 ^ k := by
  have h := thueMorseComplexity_le' k ℓ hℓ
  omega

/-- The minimal covering level is efficient: `2 ^ ⌈log₂ ℓ⌉ < 2ℓ` for
`ℓ ≥ 1`. -/
private theorem two_pow_clog_lt (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    2 ^ Nat.clog 2 ℓ < 2 * ℓ := by
  rcases Nat.lt_or_ge ℓ 2 with hℓ2 | hℓ2
  · have hℓ1 : ℓ = 1 := by omega
    subst hℓ1
    simp [Nat.clog]
  · have hk : 0 < Nat.clog 2 ℓ :=
      Nat.clog_pos (by omega) (by omega : 1 < ℓ)
    have hmin : 2 ^ (Nat.clog 2 ℓ - 1) < ℓ :=
      Nat.pow_pred_clog_lt_self (by omega : 1 < 2) (by omega : 1 < ℓ)
    have hsplit : 2 ^ Nat.clog 2 ℓ = 2 * 2 ^ (Nat.clog 2 ℓ - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

/-- **The sharpened linear upper bound**: `p(ℓ) ≤ 6ℓ - 4` for `ℓ ≥ 1`.

Take `k = ⌈log₂ ℓ⌉`, so that `ℓ ≤ 2^k ≤ 2ℓ - 1`; then
`thueMorseComplexity_le'` gives
`p(ℓ) ≤ 2(2ℓ - 1) + 2(ℓ - 1) = 6ℓ - 4`.  The conclusion is non-strict —
the strict bound `p(ℓ) < 8ℓ` is `thueMorseComplexity_lt`. -/
theorem thueMorseComplexity_le_six_mul_sub_four (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    thueMorseComplexity ℓ ≤ 6 * ℓ - 4 := by
  have h1 : ℓ ≤ 2 ^ Nat.clog 2 ℓ := Nat.le_pow_clog (by omega) ℓ
  have h2 : 2 ^ Nat.clog 2 ℓ < 2 * ℓ := two_pow_clog_lt ℓ hℓ
  have h3 := thueMorseComplexity_le' (Nat.clog 2 ℓ) ℓ h1
  omega

/-- **The linear upper bound**: `p(ℓ) < 8ℓ` for `ℓ ≥ 1`.
A weaker corollary of `thueMorseComplexity_le_six_mul_sub_four`. -/
theorem thueMorseComplexity_lt (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    thueMorseComplexity ℓ < 8 * ℓ := by
  have h := thueMorseComplexity_le_six_mul_sub_four ℓ hℓ
  omega

/-! ### Strict growth and the lower bound -/

/-- Restriction of a longer window is the shorter window. -/
private theorem window_restrict (ℓ i : ℕ) :
    (fun j : Fin ℓ => thueMorseWindow (ℓ + 1) i j.castSucc) =
      thueMorseWindow ℓ i := by
  funext j
  simp [thueMorseWindow]

/-- Complexity is monotone: every factor extends. -/
theorem thueMorseComplexity_mono (ℓ : ℕ) :
    thueMorseComplexity ℓ ≤ thueMorseComplexity (ℓ + 1) := by
  have himg : thueMorseFactorSet ℓ =
      (fun w : Fin (ℓ + 1) → ℕ => fun j : Fin ℓ => w j.castSucc) ''
        thueMorseFactorSet (ℓ + 1) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨thueMorseWindow (ℓ + 1) i, ⟨i, rfl⟩, window_restrict ℓ i⟩
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (window_restrict ℓ i).symm⟩
  rw [thueMorseComplexity, thueMorseComplexity, himg]
  exact Set.ncard_image_le (thueMorseFactorSet_finite (ℓ + 1))

/-- The contradiction step of the Morse–Hedlund argument, isolated.
If right extensions are unique (`hdet`), then two equal length-`ℓ`
windows at positions `a < b` evolve in lockstep forever, so the bit
sequence is periodic with period `b - a` from `a` on — contradicting
`thueMorseSign_not_eventually_periodic`.  Both orderings of the
pigeonhole pair in `thueMorseComplexity_lt_succ` reduce to this one
statement. -/
private theorem false_of_window_eq_of_lt (ℓ : ℕ)
    (hdet : ∀ i i' : ℕ,
      (∀ j, j < ℓ →
        thueMorseBit (i + j) = thueMorseBit (i' + j)) →
      thueMorseBit (i + ℓ) = thueMorseBit (i' + ℓ))
    {a b : ℕ} (hlt : a < b)
    (hWab : thueMorseWindow ℓ a = thueMorseWindow ℓ b) : False := by
  -- deterministic evolution propagates window equality
  have hprop : ∀ i i' : ℕ,
      (∀ j, j < ℓ → thueMorseBit (i + j) = thueMorseBit (i' + j)) →
      ∀ d j, j < ℓ → thueMorseBit (i + d + j) = thueMorseBit (i' + d + j) := by
    intro i i' h0 d
    induction d with
    | zero => exact h0
    | succ d ih =>
        intro j hj
        rcases Nat.lt_or_ge (j + 1) ℓ with hlt | hge
        · have := ih (j + 1) hlt
          rwa [show i + d + (j + 1) = i + (d + 1) + j by ring,
            show i' + d + (j + 1) = i' + (d + 1) + j by ring] at this
        · have hjeq : j + 1 = ℓ := by omega
          have hd := hdet (i + d) (i' + d) ih
          rwa [show i + d + ℓ = i + (d + 1) + j by omega,
            show i' + d + ℓ = i' + (d + 1) + j by omega] at hd
  have hper : ∀ n, a ≤ n → thueMorseBit (n + (b - a)) = thueMorseBit n := by
    intro n hn
    have hagree : ∀ j, j < ℓ → thueMorseBit (a + j) =
        thueMorseBit (b + j) := by
      intro j hj
      have := congrArg (fun w => w ⟨j, hj⟩) hWab
      simpa using this
    rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓ0
    · -- ℓ = 0: determinism alone forces a constant word
      subst hℓ0
      have h1 := hdet n (n + (b - a)) (fun j hj => absurd hj (Nat.not_lt_zero j))
      simpa using h1.symm
    · have := hprop a b hagree (n - a) 0 hℓ0
      rw [show a + (n - a) + 0 = n by omega,
        show b + (n - a) + 0 = n + (b - a) by omega] at this
      exact this.symm
  -- transport to signs and contradict aperiodicity
  apply thueMorseSign_not_eventually_periodic
  refine ⟨b - a, a, by omega, fun n hn => ?_⟩
  exact (thueMorseBit_eq_iff_thueMorseSign_eq _ _).mp (hper n hn)

/-- **Strict growth** (Morse–Hedlund): `p(ℓ) < p(ℓ+1)`. -/
theorem thueMorseComplexity_lt_succ (ℓ : ℕ) :
    thueMorseComplexity ℓ < thueMorseComplexity (ℓ + 1) := by
  classical
  by_contra hcon
  have heq : thueMorseComplexity (ℓ + 1) = thueMorseComplexity ℓ := by
    have := thueMorseComplexity_mono ℓ
    omega
  -- move to finsets
  set S := (thueMorseFactorSet_finite (ℓ + 1)).toFinset with hS
  set T := (thueMorseFactorSet_finite ℓ).toFinset with hT
  set res : (Fin (ℓ + 1) → ℕ) → (Fin ℓ → ℕ) :=
    fun w => fun j : Fin ℓ => w j.castSucc with hres
  have himgTS : T = S.image res := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    rw [Set.Finite.coe_toFinset, Set.Finite.coe_toFinset]
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨thueMorseWindow (ℓ + 1) i, ⟨i, rfl⟩, window_restrict ℓ i⟩
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (window_restrict ℓ i).symm⟩
  have hcards : (S.image res).card = S.card := by
    have h1 : (S.image res).card = T.card := by rw [← himgTS]
    have h2 : T.card = thueMorseComplexity ℓ := by
      rw [hT]
      exact (Set.ncard_eq_toFinset_card _ (thueMorseFactorSet_finite ℓ)).symm
    have h3 : S.card = thueMorseComplexity (ℓ + 1) := by
      rw [hS]
      exact (Set.ncard_eq_toFinset_card _
        (thueMorseFactorSet_finite (ℓ + 1))).symm
    omega
  have hinj : Set.InjOn res ↑S := Finset.card_image_iff.mp hcards
  -- unique right extension: determinism
  have hdet : ∀ i i' : ℕ, (∀ j, j < ℓ → thueMorseBit (i + j) =
      thueMorseBit (i' + j)) → thueMorseBit (i + ℓ) = thueMorseBit (i' + ℓ) := by
    intro i i' hagree
    have hmem : thueMorseWindow (ℓ + 1) i ∈ (S : Set _) := by
      rw [hS, Set.Finite.coe_toFinset]
      exact ⟨i, rfl⟩
    have hmem' : thueMorseWindow (ℓ + 1) i' ∈ (S : Set _) := by
      rw [hS, Set.Finite.coe_toFinset]
      exact ⟨i', rfl⟩
    have hreseq : res (thueMorseWindow (ℓ + 1) i) =
        res (thueMorseWindow (ℓ + 1) i') := by
      funext j
      simp only [hres, thueMorseWindow_apply, Fin.val_castSucc]
      exact hagree j j.isLt
    have := hinj hmem hmem' hreseq
    have hlast := congrArg (fun w => w (Fin.last ℓ)) this
    simpa [thueMorseWindow, Fin.val_last] using hlast
  -- pigeonhole: two equal windows
  have hmaps : ∀ a ∈ range (T.card + 1), thueMorseWindow ℓ a ∈ T := by
    intro a _
    rw [hT, Set.Finite.mem_toFinset]
    exact ⟨a, rfl⟩
  have hpigeon := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t := T) (by rw [Finset.card_range]; omega) hmaps
  obtain ⟨a, _, b, _, hab, hWab⟩ := hpigeon
  -- either ordering of the pair reduces to the `a < b` step
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact false_of_window_eq_of_lt ℓ hdet hlt hWab
  · exact false_of_window_eq_of_lt ℓ hdet (by omega : b < a)
      hWab.symm

/-- The empty factor is unique: `p(0) = 1`. -/
theorem thueMorseComplexity_zero : thueMorseComplexity 0 = 1 := by
  rw [thueMorseComplexity]
  refine Set.ncard_eq_one.mpr ⟨thueMorseWindow 0 0, ?_⟩
  ext w
  simp only [Set.mem_singleton_iff, thueMorseFactorSet, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    funext j
    exact absurd j.isLt (by omega)
  · rintro rfl
    exact ⟨0, rfl⟩

/-- **The Morse–Hedlund lower bound**: `ℓ + 1 ≤ p(ℓ)`. -/
theorem le_thueMorseComplexity (ℓ : ℕ) :
    ℓ + 1 ≤ thueMorseComplexity ℓ := by
  induction ℓ with
  | zero => rw [thueMorseComplexity_zero]
  | succ ℓ ih =>
      have := thueMorseComplexity_lt_succ ℓ
      omega

end Fabius
