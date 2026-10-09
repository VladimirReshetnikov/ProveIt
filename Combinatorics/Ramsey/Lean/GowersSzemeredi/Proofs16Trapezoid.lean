import GowersSzemeredi.Proofs16DirichletBound

/-! The discrete trapezoid sandwich: brick A of [49]'s Proposition 26.

On `ℤ/N`, let `I_a = {t : |t| ≤ a}` (centered absolute value) and let

  `g(t) = |{s ∈ I_a : |t − s| ≤ c}| / |I_c|`,

the convolution of two intervals, normalized. Then
* `trapezoid_eq_one`: `g(t) = 1` when `|t| + c ≤ a`;
* `trapezoid_eq_zero`: `g(t) = 0` when `a + c < |t|`;
* `trapezoid_nonneg`, `trapezoid_le_one`: `0 ≤ g ≤ 1`.

Hence, for frequencies `K`, the product `Π_{γ∈K} g(γx)` lies in `[0,1]`. It
equals `1` on `B(K; (a−c)/N)` and vanishes off `B(K; (a+c)/N)`
(`trapezoid_product_sandwich`). This is how [49] Proposition 26 compares a
Bohr indicator with a function whose Fourier coefficients decay like `1/ξ²`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The centered interval `{t : |t| ≤ a}`. -/
def centeredBall (N : Nat) [NeZero N] (a : Nat) : Finset (ZMod N) :=
  Finset.univ.filter fun t => centeredAbs t ≤ a

/-- The discrete trapezoid. -/
def trapezoid {N : Nat} [NeZero N] (a c : Nat) (t : ZMod N) : Real :=
  ((centeredBall N a).filter fun s => centeredAbs (t - s) ≤ c).card /
    (centeredBall N c).card

theorem trapezoid_nonneg {N : Nat} [NeZero N] (a c : Nat) (t : ZMod N) : 0 ≤ trapezoid a c t := by
  unfold trapezoid; positivity

/-- The fibre of the trapezoid at `t` injects into `I_c` via `s ↦ t − s`. -/
theorem trapezoid_fibre_card_le {N : Nat} [NeZero N] (a c : Nat) (t : ZMod N) :
    ((centeredBall N a).filter fun s => centeredAbs (t - s) ≤ c).card ≤
      (centeredBall N c).card := by
  apply Finset.card_le_card_of_injOn (fun s => t - s)
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩
  · intro s _ s' _ h
    simpa using h

theorem trapezoid_le_one {N : Nat} [NeZero N] (a c : Nat) (t : ZMod N) : trapezoid a c t ≤ 1 := by
  unfold trapezoid
  by_cases h0 : (centeredBall N c).card = 0
  · rw [h0, Nat.cast_zero, div_zero]; norm_num
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h0)]
    exact_mod_cast trapezoid_fibre_card_le a c t

/-- **Full on the inner interval.** -/
theorem trapezoid_eq_one {N : Nat} [NeZero N] (a c : Nat) (t : ZMod N)
    (ht : centeredAbs t + c ≤ a) : trapezoid a c t = 1 := by
  unfold trapezoid
  have hcpos : 0 < (centeredBall N c).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [centeredAbs]⟩⟩
  -- the fibre is the image of `I_c` under `u ↦ t − u`
  have heq : ((centeredBall N a).filter fun s => centeredAbs (t - s) ≤ c).card =
      (centeredBall N c).card := by
    apply le_antisymm (trapezoid_fibre_card_le a c t)
    apply Finset.card_le_card_of_injOn (fun u => t - u)
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · show centeredAbs (t - u) ≤ a
        have := centeredAbs_add_le t (-u)
        rw [centeredAbs_neg, ← sub_eq_add_neg] at this
        omega
      · simpa using hu'
    · intro u _ u' _ h
      simpa using h
  rw [heq, div_self (by exact_mod_cast hcpos.ne')]

/-- **Empty beyond the outer interval.** -/
theorem trapezoid_eq_zero {N : Nat} [NeZero N] (a c : Nat) (t : ZMod N)
    (ht : a + c < centeredAbs t) : trapezoid a c t = 0 := by
  unfold trapezoid
  have : ((centeredBall N a).filter fun s => centeredAbs (t - s) ≤ c) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs hts
    have hs' := (Finset.mem_filter.mp hs).2
    have := centeredAbs_add_le s (t - s)
    rw [add_sub_cancel] at this
    omega
  rw [this, Finset.card_empty, Nat.cast_zero, zero_div]

/-- **The product sandwich.** -/
theorem trapezoid_product_sandwich {N : Nat} [NeZero N] (K : Finset (ZMod N)) (a c : Nat)
    (x : ZMod N) :
    (x ∈ bohr K (((a - c : Nat) : Real) / N) → c ≤ a → ∏ γ ∈ K, trapezoid a c (γ * x) = 1) ∧
      (x ∉ bohr K (((a + c : Nat) : Real) / N) → ∏ γ ∈ K, trapezoid a c (γ * x) = 0) ∧
      0 ≤ ∏ γ ∈ K, trapezoid a c (γ * x) ∧ ∏ γ ∈ K, trapezoid a c (γ * x) ≤ 1 := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hband : ∀ (r : Nat) (y : ZMod N), (y ∈ bohr K ((r : Real) / N)) ↔ ∀ γ ∈ K, centeredAbs (γ * y) ≤ r := by
    intro r y
    unfold bohr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall₂_congr
    intro γ _
    rw [div_mul_cancel₀ _ hNR.ne']
    exact_mod_cast Iff.rfl
  refine ⟨fun hx hca => ?_, fun hx => ?_, Finset.prod_nonneg fun γ _ => trapezoid_nonneg a c _,
    Finset.prod_le_one (fun γ _ => trapezoid_nonneg a c _) fun γ _ => trapezoid_le_one a c _⟩
  · rw [hband] at hx
    exact Finset.prod_eq_one fun γ hγ => trapezoid_eq_one a c _ (by have := hx γ hγ; omega)
  · rw [hband] at hx
    push Not at hx
    obtain ⟨γ, hγ, hlt⟩ := hx
    exact Finset.prod_eq_zero hγ (trapezoid_eq_zero a c _ hlt)

end LeanProofs.GowersSzemeredi
