import GowersSzemeredi.Proofs05SimultaneousDirichlet

/-! Carry-free windows for slowly moving brackets.

This is step 3 of the proposed route for the readout (R) in research
notes J.2. Bracket-linear maps become exactly affine on sub-progressions
whose step makes every bracket frequency small. The combinatorial core is
stated here.

* `floor_single_cut`: if `|δ| * M ≤ 1`, the sequence `j ↦ ⌊β + j δ⌋` on
  `[0, M)` is constant before some cut `c` and constant from `c` on.
* `exists_common_constant_window`: for `r` such sequences there is a block
  `[k L, (k+1) L)` with `L = M / (r+1)` on which all of them are constant.
  Pigeonhole: `r` cuts lie strictly inside at most `r` of the `r+1`
  blocks.

The window length `M / (r+1)` is polynomial in the number `r` of brackets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- On the window, a slowly moving bracket stays within one of its start. -/
theorem floor_window_bounds (β δ : Real) (M : Nat) (hδ : |δ| * M ≤ 1) (j : Nat) (hj : j < M) :
    ⌊β⌋ - 1 ≤ ⌊β + j * δ⌋ ∧ ⌊β + j * δ⌋ ≤ ⌊β⌋ + 1 := by
  have hjd : |(j : Real) * δ| < 1 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
    have hjM : (j : Real) < M := by exact_mod_cast hj
    rcases (abs_nonneg δ).lt_or_eq with hpos | hzero
    · calc (j : Real) * |δ| < M * |δ| := mul_lt_mul_of_pos_right hjM hpos
        _ = |δ| * M := mul_comm _ _
        _ ≤ 1 := hδ
    · rw [← hzero]; simp
  have hlo := (abs_lt.mp hjd).1
  have hhi := (abs_lt.mp hjd).2
  have hf1 := Int.floor_le β
  have hf2 := Int.lt_floor_add_one β
  constructor
  · rw [Int.le_floor]; push_cast; linarith
  · have : ⌊β + j * δ⌋ < ⌊β⌋ + 2 := by
      rw [Int.floor_lt]; push_cast; linarith
    omega

/-- A bracket moving by at most `1/M` per step changes at most once on
`[0, M)`. -/
theorem floor_single_cut (β δ : Real) (M : Nat) (hδ : |δ| * M ≤ 1) :
    ∃ c : Nat, c ≤ M ∧
      (∀ j : Nat, j < c → ⌊β + j * δ⌋ = ⌊β⌋) ∧
      (∀ j₁ j₂ : Nat, c ≤ j₁ → c ≤ j₂ → j₁ < M → j₂ < M →
        ⌊β + j₁ * δ⌋ = ⌊β + j₂ * δ⌋) := by
  classical
  by_cases hall : ∀ j : Nat, j < M → ⌊β + j * δ⌋ = ⌊β⌋
  · exact ⟨M, le_rfl, fun j hj => hall j hj, fun j₁ j₂ h1 _ h1M _ => by omega⟩
  push_neg at hall
  have hex : ∃ j, j < M ∧ ⌊β + j * δ⌋ ≠ ⌊β⌋ := hall
  set c := Nat.find hex with hcdef
  have hc : c < M ∧ ⌊β + c * δ⌋ ≠ ⌊β⌋ := Nat.find_spec hex
  have hmin : ∀ j, j < c → ¬ (j < M ∧ ⌊β + j * δ⌋ ≠ ⌊β⌋) := fun j hj => Nat.find_min hex hj
  have hbefore : ∀ j : Nat, j < c → ⌊β + j * δ⌋ = ⌊β⌋ := by
    intro j hj
    by_contra hne
    exact hmin j hj ⟨lt_trans hj hc.1, hne⟩
  refine ⟨c, hc.1.le, hbefore, ?_⟩
  -- after the cut every floor equals the floor at the cut
  have hafter : ∀ j : Nat, c ≤ j → j < M → ⌊β + j * δ⌋ = ⌊β + c * δ⌋ := by
    intro j hcj hj
    have hb := floor_window_bounds β δ M hδ j hj
    have hbc := floor_window_bounds β δ M hδ c hc.1
    have hcR : (c : Real) ≤ j := by exact_mod_cast hcj
    have hcR0 : (0 : Real) ≤ c := Nat.cast_nonneg c
    rcases le_total 0 δ with hδ0 | hδ0
    · have hm : ⌊β + c * δ⌋ ≤ ⌊β + j * δ⌋ := Int.floor_le_floor (by nlinarith)
      have h0 : ⌊β⌋ ≤ ⌊β + c * δ⌋ := Int.floor_le_floor (by nlinarith)
      have := hc.2
      omega
    · have hm : ⌊β + j * δ⌋ ≤ ⌊β + c * δ⌋ := Int.floor_le_floor (by nlinarith)
      have h0 : ⌊β + c * δ⌋ ≤ ⌊β⌋ := Int.floor_le_floor (by nlinarith)
      have := hc.2
      omega
  intro j₁ j₂ h1 h2 h1M h2M
  rw [hafter j₁ h1 h1M, hafter j₂ h2 h2M]

/-- **A common carry-free window.** For `r` slowly moving brackets there is
a block of length `M / (r+1)` on which all of them are constant. -/
theorem exists_common_constant_window {r : Nat} (β δ : Fin r → Real) (M : Nat)
    (hδ : ∀ i, |δ i| * M ≤ 1) :
    ∃ a : Nat, a + M / (r + 1) ≤ M ∧
      ∀ i (j₁ j₂ : Nat), a ≤ j₁ → a ≤ j₂ → j₁ < a + M / (r + 1) → j₂ < a + M / (r + 1) →
        ⌊β i + j₁ * δ i⌋ = ⌊β i + j₂ * δ i⌋ := by
  classical
  set L := M / (r + 1) with hL
  have hcut : ∀ i, ∃ c : Nat, c ≤ M ∧
      (∀ j : Nat, j < c → ⌊β i + j * δ i⌋ = ⌊β i⌋) ∧
      (∀ j₁ j₂ : Nat, c ≤ j₁ → c ≤ j₂ → j₁ < M → j₂ < M →
        ⌊β i + j₁ * δ i⌋ = ⌊β i + j₂ * δ i⌋) :=
    fun i => floor_single_cut (β i) (δ i) M (hδ i)
  choose c hcM hbefore hafter using hcut
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · refine ⟨0, by omega, ?_⟩
    intro i j₁ j₂ _ _ h1 _
    omega
  -- block `k` is spoiled by cut `i` when `c i / L = k` and `c i` is not its left end
  let spoiled : Finset Nat := Finset.univ.image fun i : Fin r => c i / L
  have hcard : spoiled.card < (Finset.range (r + 1)).card := by
    calc spoiled.card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
      _ = r := by simp
      _ < r + 1 := Nat.lt_succ_self r
      _ = (Finset.range (r + 1)).card := by simp
  obtain ⟨k, hk, hks⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hkr : k < r + 1 := Finset.mem_range.mp hk
  have hfit : k * L + L ≤ M := by
    have h1 : (k + 1) * L ≤ (r + 1) * L := Nat.mul_le_mul_right L hkr
    have h2 : (r + 1) * L ≤ M := by rw [hL, mul_comm]; exact Nat.div_mul_le_self M (r + 1)
    nlinarith
  refine ⟨k * L, hfit, ?_⟩
  intro i j₁ j₂ h1 h2 h1L h2L
  have hnot : c i / L ≠ k := by
    intro heq
    exact hks (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩)
  have hj1M : j₁ < M := by omega
  have hj2M : j₂ < M := by omega
  rcases le_or_gt (c i) (k * L) with hlow | hhigh
  · exact hafter i j₁ j₂ (by omega) (by omega) hj1M hj2M
  · have hge : (k + 1) * L ≤ c i := by
      by_contra hlt
      push_neg at hlt
      exact hnot (Nat.div_eq_of_lt_le hhigh.le hlt)
    have hk1 : k * L + L = (k + 1) * L := by ring
    rw [hbefore i j₁ (by omega), hbefore i j₂ (by omega)]

end LeanProofs.GowersSzemeredi
