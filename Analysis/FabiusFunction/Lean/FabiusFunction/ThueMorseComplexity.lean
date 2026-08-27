import FabiusFunction.ThueMorseRecurrence
import FabiusFunction.ThueMorseAperiodicity
import FabiusFunction.ThueMorseBinomialLog
import Mathlib.Data.Set.Card

/-!
# Linear factor complexity of the Thue–Morse word

The number `p(ℓ)` of distinct length-`ℓ` factors of the Thue–Morse word
satisfies `ℓ + 1 ≤ p(ℓ) < 8ℓ` — the atlas's elementary linear bound.
This module proves both halves.

* `thueMorseWindow` / `thueMorseFactorSet` / `thueMorseComplexity` — the
  window at position `i`, the set of factors of length `ℓ`, and its
  (finite) cardinality.
* `card_image_thueMorseWindow_le` — **upper bound**: any collection of
  windows of length `ℓ ≤ 2^k` contains at most `4·2^k` distinct ones,
  because a window is determined by its offset in an aligned block and
  the two adjacent block bits (`thueMorseWindow_eq_reconstruct`);
  with `2^k < 2ℓ` minimal this gives `p(ℓ) < 8ℓ`
  (`thueMorseComplexity_lt`).
* `thueMorseComplexity_lt_succ` — **strict growth**, the Morse–Hedlund
  argument: if some length had no more factors than the previous one,
  every factor would extend uniquely to the right; the finitely many
  windows would then evolve deterministically, the pigeonhole principle
  would force two equal windows, and the word would be eventually
  periodic — contradicting `thueMorseSign_not_eventually_periodic`.
* `le_thueMorseComplexity` — **lower bound** `ℓ + 1 ≤ p(ℓ)`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The length-`ℓ` window of the Thue–Morse word at position `i`. -/
def thueMorseWindow (ℓ i : ℕ) : Fin ℓ → ℕ := fun j => thueMorseBit (i + j)

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

/-- **At most `4·2^k` distinct windows** of length `ℓ ≤ 2^k`, over any
finite set of starting positions. -/
theorem card_image_thueMorseWindow_le (k ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ k)
    (s : Finset ℕ) :
    (s.image (thueMorseWindow ℓ)).card ≤ 4 * 2 ^ k := by
  classical
  set recon : ℕ × ℕ × ℕ → (Fin ℓ → ℕ) := fun p => fun j : Fin ℓ =>
    if p.1 + j < 2 ^ k
    then (p.2.1 + thueMorseBit (p.1 + j)) % 2
    else (p.2.2 + thueMorseBit (p.1 + j - 2 ^ k)) % 2 with hrecon
  have hsub : s.image (thueMorseWindow ℓ) ⊆
      ((range (2 ^ k)) ×ˢ (range 2) ×ˢ (range 2)).image recon := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_image.mpr
      ⟨(i % 2 ^ k, thueMorseBit (i / 2 ^ k),
        thueMorseBit (i / 2 ^ k + 1)), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · show i % 2 ^ k ∈ range (2 ^ k)
        exact Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos k))
      · show thueMorseBit (i / 2 ^ k) ∈ range 2
        exact Finset.mem_range.mpr
          (by have := thueMorseBit_le_one (i / 2 ^ k); omega)
      · show thueMorseBit (i / 2 ^ k + 1) ∈ range 2
        exact Finset.mem_range.mpr
          (by have := thueMorseBit_le_one (i / 2 ^ k + 1); omega)
    · exact (thueMorseWindow_eq_reconstruct k ℓ hℓ i).symm
  calc (s.image (thueMorseWindow ℓ)).card
      ≤ (((range (2 ^ k)) ×ˢ (range 2) ×ˢ (range 2)).image recon).card :=
        Finset.card_le_card hsub
    _ ≤ ((range (2 ^ k)) ×ˢ (range 2) ×ˢ (range 2)).card :=
        Finset.card_image_le
    _ = 4 * 2 ^ k := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range,
          Finset.card_range]
        ring

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

/-- Upper bound at every covering level: `p(ℓ) ≤ 4·2^k` for `ℓ ≤ 2^k`. -/
theorem thueMorseComplexity_le (k ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ k) :
    thueMorseComplexity ℓ ≤ 4 * 2 ^ k := by
  rw [thueMorseComplexity, thueMorseFactorSet_eq_image k ℓ hℓ,
    Set.ncard_coe_finset]
  exact card_image_thueMorseWindow_le k ℓ hℓ _

/-- **The linear upper bound**: `p(ℓ) < 8ℓ` for `ℓ ≥ 1`. -/
theorem thueMorseComplexity_lt (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    thueMorseComplexity ℓ < 8 * ℓ := by
  have h1 : ℓ ≤ 2 ^ Nat.clog 2 ℓ := Nat.le_pow_clog (by omega) ℓ
  have h2 : 2 ^ Nat.clog 2 ℓ < 2 * ℓ := by
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
  calc thueMorseComplexity ℓ ≤ 4 * 2 ^ Nat.clog 2 ℓ :=
        thueMorseComplexity_le _ ℓ h1
    _ < 8 * ℓ := by omega

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
  -- pigeonhole: two equal windows
  have hmaps : ∀ a ∈ range (T.card + 1), thueMorseWindow ℓ a ∈ T := by
    intro a _
    rw [hT, Set.Finite.mem_toFinset]
    exact ⟨a, rfl⟩
  have hpigeon := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t := T) (by rw [Finset.card_range]; omega) hmaps
  obtain ⟨a, _, b, _, hab, hWab⟩ := hpigeon
  -- normalize to a < b
  rcases Nat.lt_or_ge a b with hlt | hge
  · have hper : ∀ n, a ≤ n → thueMorseBit (n + (b - a)) = thueMorseBit n := by
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
    have hb := hper n hn
    have h1 := thueMorseSign_eq_one_sub_two_mul_bit (n + (b - a))
    have h2 := thueMorseSign_eq_one_sub_two_mul_bit n
    omega
  · have hlt' : b < a := by omega
    have hper : ∀ n, b ≤ n → thueMorseBit (n + (a - b)) = thueMorseBit n := by
      intro n hn
      have hagree : ∀ j, j < ℓ → thueMorseBit (b + j) =
          thueMorseBit (a + j) := by
        intro j hj
        have := congrArg (fun w => w ⟨j, hj⟩) hWab
        simpa using this.symm
      rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓ0
      · subst hℓ0
        have h1 := hdet n (n + (a - b)) (fun j hj => absurd hj (Nat.not_lt_zero j))
        simpa using h1.symm
      · have := hprop b a hagree (n - b) 0 hℓ0
        rw [show b + (n - b) + 0 = n by omega,
          show a + (n - b) + 0 = n + (a - b) by omega] at this
        exact this.symm
    apply thueMorseSign_not_eventually_periodic
    refine ⟨a - b, b, by omega, fun n hn => ?_⟩
    have hb := hper n hn
    have h1 := thueMorseSign_eq_one_sub_two_mul_bit (n + (a - b))
    have h2 := thueMorseSign_eq_one_sub_two_mul_bit n
    omega

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
