import New.UpperBound.Kernels.JetConjugatesAndBounds

/-!
# Weights of regular parameters and bounds on boxes

A weight is a pair `(κ, e)`: `κ w h` is the number of columns of height `h` at the place `w`, and
`e w` is the power of the determinant. `New.IsHCParam κ e l` says that `l w` lists twice the
Harish-Chandra parameter of `(κ, e)` in some order. This file finds a weight for each regular
parameter `l = 2λ` (`New.HCParam.HasGap`). It also bounds a weight by its parameter: the number of
boxes and the power of the determinant.

## Main definitions and results

* `New.Exchange.boxes_le_card_mul_of_isHCParam`, `New.Exchange.natAbs_le_of_isHCParam`: a bound `β`
  on the entries of `l` bounds the number of boxes and, for nonempty `n`, the determinant power.
* `New.Exchange.exists_isHCParam_of_hasGap`: every regular parameter comes from a weight;
  `New.Exchange.exists_isHCParam_of_le` adds control of the determinant power from below.

Notions from other files:
* `New.boxes κ N`: the number of boxes in the columns of height below `N`, over all places.
-/

noncomputable section

section WeightsOfParameters

open Finset Fintype

namespace New.Exchange

variable {Φ n : Type} [Fintype Φ] [Fintype n]

/-- If `l` is twice the Harish-Chandra parameter of the weight `(κ, e)` and `|l w i| ≤ β` for all
`i`, then `|hcParameter κ e (card n) w p| ≤ β` at every position `p < card n`. Here
`hcParameter κ e N w p` is the entry at the position `p`, counted from `0`, of twice the
Harish-Chandra parameter of `(κ, e)` at `w` in rank `N`. -/
lemma abs_hcParameter_le_of_isHCParam {κ : Φ → ℕ → ℕ} {e : Φ → ℤ} {l : Φ → n → ℤ}
    (hl : IsHCParam κ e l) {β : ℕ} {w : Φ} (hβ : ∀ i : n, |l w i| ≤ β) {p : ℕ}
    (hp : p < Fintype.card n) : |hcParameter κ e (Fintype.card n) w p| ≤ β := by
  classical
  obtain ⟨i, -, hi, -⟩ := hl.exists_decreasingPosition_eq w hp
  simpa [← hi] using hβ i

/-- Let `hcParameter κ e N w p` be the entry at the position `p`, counted from `0`, of twice the
Harish-Chandra parameter of the weight `(κ, e)` at `w` in rank `N`. For `0 < N` its last entry, at
the position `N - 1`, is `2 e w + 1 - N`. -/
lemma hcParameter_sub_one (κ : Φ → ℕ → ℕ) (e : Φ → ℤ) {N : ℕ} (hN : 0 < N) (w : Φ) :
    hcParameter κ e N w (N - 1) = 2 * e w + 1 - N := by
  have h_empty : Ioo (N - 1) N = ∅ := by grind
  rw [hcParameter, diagramWeight_apply, h_empty, Finset.sum_empty]
  omega

/-- If `l` lists twice the Harish-Chandra parameter of the weight `(κ, e)` (`IsHCParam`), where
`κ w h` is the number of columns of height `h` at the place `w : Φ`, and `|l w i| ≤ β` for all `w`
and `i`, then `κ` has at most `card Φ * card n * β` boxes in columns of height below `card n`. -/
lemma boxes_le_card_mul_of_isHCParam {κ : Φ → ℕ → ℕ} {e : Φ → ℤ} {l : Φ → n → ℤ}
    (hl : IsHCParam κ e l) {β : ℕ} (hβ : ∀ (w : Φ) (i : n), |l w i| ≤ β) :
    boxes κ (Fintype.card n) ≤ Fintype.card Φ * Fintype.card n * β := by
  classical
  -- The boxes are counted by rows. A row length is at most half the difference between an entry
  -- of `l w` and the smallest entry `2 e w + 1 - card n`, so at most `β`.
  have h_row (w : Φ) (i : Fin (card n)) : diagramWeight (rankAt fun _ ↦ n) κ (w, i) ≤ β := by
    have h_entry :
        |2 * (e w + diagramWeight (rankAt fun _ ↦ n) κ (w, i)) + card n - 1 - 2 * (i : ℕ)| ≤ β :=
      abs_hcParameter_le_of_isHCParam hl (hβ w) i.isLt
    have h_last : |2 * e w + 1 - card n| ≤ β := by
      simpa [hcParameter_sub_one κ e i.pos w] using
        abs_hcParameter_le_of_isHCParam hl (hβ w) (Nat.sub_one_lt_of_lt i.isLt)
    grind [abs_le]
  calc boxes κ (card n)
      = ∑ x : Φ × Fin (card n), diagramWeight (rankAt fun _ ↦ n) κ (x.1, x.2) :=
        FitsRanks.refl.sum_diagramWeight_eq_boxes.symm
    _ ≤ ∑ _x : Φ × Fin (card n), β := sum_le_sum fun x _ ↦ h_row x.1 x.2
    _ = card Φ * card n * β := by simp

/-- Let `n` be nonempty. If `l` is twice the Harish-Chandra parameter of the weight `(κ, e)` and
`|l w i| ≤ β` for all `i`, then the power of the determinant at `w` satisfies `|e w| ≤ β`. -/
lemma natAbs_le_of_isHCParam [Nonempty n] {κ : Φ → ℕ → ℕ} {e : Φ → ℤ} {l : Φ → n → ℤ}
    (hl : IsHCParam κ e l) {β : ℕ} {w : Φ} (hβ : ∀ i : n, |l w i| ≤ β) : (e w).natAbs ≤ β := by
  -- The largest entry of `l w` is at least `2 e w + card n - 1`, and the smallest is
  -- `2 e w + 1 - card n`.
  have h_first :
      |2 * (e w + diagramWeight (fun _ ↦ card n) κ (w, 0)) + card n - 1 - 2 * (0 : ℕ)| ≤ β :=
    abs_hcParameter_le_of_isHCParam hl hβ card_pos
  have h_last : |2 * e w + 1 - card n| ≤ β := by
    simpa [hcParameter_sub_one κ e card_pos w] using
      abs_hcParameter_le_of_isHCParam hl hβ (Nat.sub_one_lt card_ne_zero)
  grind [abs_le, Fintype.card_pos (α := n)]

/-- Let `v` be injective and `g ≤ v i` on a finite set `S`. There are column multiplicities `κ`,
equal to a given `f` above the height `#S`, such that each `v i` with `i ∈ S` is
`g + (κ (p + 1) + ⋯ + κ #S) + #S - 1 - p` for a position `p < #S`. -/
lemma exists_eq_add_card_add_sum_Ioc {ι : Type} {v : ι → ℤ} (hv : v.Injective) (S : Finset ι)
    (g : ℤ) (f : ℕ → ℕ) (hg : ∀ i ∈ S, g ≤ v i) :
    ∃ κ : ℕ → ℕ, (∀ k > #S, κ k = f k) ∧
      ∀ i ∈ S, ∃ p < #S, v i + p + 1 = g + (#S + ∑ k ∈ Ioc p #S, κ k : ℕ) := by
  classical
  -- The numbers `κ 1, …, κ (#S - 1)` are the gaps between consecutive values of `v`, less one, and
  -- `κ #S` is the gap between the smallest value and `g`.
  induction S using induction_on_min_value v generalizing g f with
  | empty => exact ⟨f, fun _ _ ↦ rfl, by simp⟩
  | insert a S ha h_min ih =>
    -- The index `a` of the smallest value takes the last position.
    have h_gap (i : ι) (hi : i ∈ S) : v a + 1 ≤ v i :=
      (h_min i hi).lt_of_ne (hv.ne (ne_of_mem_of_not_mem hi ha).symm)
    have h_le : g ≤ v a := hg a (mem_insert_self a S)
    obtain ⟨κ, h_high, h_position⟩ :=
      ih (v a + 1) (Function.update f (#S + 1) (v a - g).toNat) h_gap
    have h_new : (κ (#S + 1) : ℤ) = v a - g := by simp [h_high, Int.toNat_sub_of_le h_le]
    simp only [card_insert_of_notMem ha, forall_mem_insert]
    refine ⟨κ, fun k hk ↦ ?_, ⟨#S, Nat.lt_succ_self _, ?_⟩, fun i hi ↦ ?_⟩
    · rw [h_high k (by omega), Function.update_of_ne hk.ne']
    · simp
      omega
    · obtain ⟨p, hp_lt, hp_eq⟩ := h_position i hi
      exact ⟨p, by omega, by grind [sum_Ioc_succ_top]⟩

/-- Let each `l w` be a parameter of gap `c` for the signs `s`, and let
`e w ≤ l w i / 2 + card n / 2` for all `i` (integer divisions). Then `l` is twice the Harish-Chandra
parameter of a weight with column multiplicities `f` and determinant power `e w + f w (card n)`. The
parameter sees only the columns of height below `card n` and the determinant power, so above that
height `f` can be prescribed, as `κ`. -/
lemma exists_isHCParam_of_le {s : n → ℤˣ} (κ : Φ → ℕ → ℕ) {e : Φ → ℤ} {c : ℕ} {l : Φ → n → ℤ}
    (hc : ∀ w : Φ, (toHCParam s (l w)).HasGap c)
    (he_le : ∀ (w : Φ) (i : n), e w ≤ l w i / 2 + Fintype.card n / 2) :
    ∃ f : Φ → ℕ → ℕ,
      IsHCParam f (fun w : Φ ↦ e w + f w (Fintype.card n)) l ∧
      ∀ w : Φ, ∀ k > Fintype.card n, f w k = κ w k := by
  classical
  -- By parity `l w i` is determined by its half, so the halves are distinct; apply
  -- `exists_eq_add_card_add_sum_Ioc` to them.
  have h_parity (w : Φ) (i : n) : (l w i + Fintype.card n - 1) % 2 = 0 :=
    Int.even_iff.1 ((hc w).parity i)
  have h_half (w : Φ) : Function.Injective fun i : n ↦ l w i / 2 := fun i j _ ↦
    (hc w).injective (by grind [h_parity w i, h_parity w j])
  have h_exists (w : Φ) : ∃ κ' : ℕ → ℕ, (∀ k > Fintype.card n, κ' k = κ w k) ∧
      ∀ i : n, ∃ p < Fintype.card n, l w i / 2 + p + 1 = e w - Fintype.card n / 2 +
        (Fintype.card n + ∑ k ∈ Ioc p (Fintype.card n), κ' k : ℕ) := by
    simpa using exists_eq_add_card_add_sum_Ioc (h_half w) univ (e w - Fintype.card n / 2) (κ w)
      fun i _ ↦ sub_le_iff_le_add.2 (he_le w i)
  choose f h_high h_position using h_exists
  refine ⟨f, fun w ↦ ⟨(hc w).injective, fun i ↦ ?_⟩, h_high⟩
  obtain ⟨p, hp_lt, hp_eq⟩ := h_position w i
  refine ⟨p, hp_lt, ?_⟩
  have h_split : (Ioo p (Fintype.card n)).sum (f w) + f w (Fintype.card n) =
      ∑ k ∈ Ioc p (Fintype.card n), f w k := sum_Ioo_add_eq_sum_Ioc hp_lt
  rw [hcParameter, diagramWeight_apply]
  grind [h_parity w i]

/-- If every `l w` is a parameter of gap `c` for the signs `s` (in particular, its entries are
distinct and have the parity of `card n - 1`), then `l` is twice the Harish-Chandra parameter of
some weight `(κ, e)`. -/
lemma exists_isHCParam_of_hasGap {s : n → ℤˣ} {c : ℕ} {l : Φ → n → ℤ}
    (hc : ∀ w : Φ, (toHCParam s (l w)).HasGap c) :
    ∃ (κ : Φ → ℕ → ℕ) (e : Φ → ℤ), IsHCParam κ e l := by
  choose e he_le using fun w : Φ ↦
    (Finite.exists_ge fun i : n ↦ l w i / 2 + Fintype.card n / 2)
  obtain ⟨f, hf, -⟩ := exists_isHCParam_of_le 0 hc he_le
  exact ⟨f, _, hf⟩

end New.Exchange

end WeightsOfParameters

end
