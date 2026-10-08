import GowersSzemeredi.Proofs02Roth
import GowersSzemeredi.Proofs18Consequences
import GowersSzemeredi.Proofs18FiveTermSourceThreshold

/-! Theorem 18.2 and Corollary 18.7 at every length up to five.

The catalogue entries `theorem_18_2` and `corollary_18_7` quantify over all
lengths `k`. This module names the statements at one length
(`Theorem182At`, `Corollary187At`), records that the catalogue entries are
exactly the conjunctions over all positive lengths, and proves every length
`k ≤ 5` with the source's exact displayed thresholds:

* `k ≤ 3`: from Roth's theorem with its explicit constant
  (`roth_explicit_threshold`). For `delta ≤ 1/2` and every `k`,
  `exp(exp(10^12/delta)) ≤ szemerediThreshold delta k`, because with
  `u = 1/delta ≥ 2` one has `1 + 2*10^12*u ≤ u^42 ≤ u^(2^(2^(k+9)))`. A
  three-term progression contains the shorter ones.
* `k = 4, 5`: the existing `theorem_18_2_four_holds` and
  `theorem_18_2_five_holds`.

Corollary 18.7 at each such length follows from Theorem 18.2 at density one
half (`corollary_18_7_at_of_half_density`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Theorem 18.2 at a single length `k`. -/
def Theorem182At (k : Nat) : Prop :=
  ∀ (delta : Real) (N : Nat), 0 < delta → delta ≤ 1 / 2 →
    szemerediThreshold delta k ≤ N →
    ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card → HasNatAP A k

/-- Corollary 18.7 at a single length `k`. -/
def Corollary187At (k : Nat) : Prop :=
  ∀ N : Nat, twoColorThreshold k ≤ N → ∀ color : Nat → Fin 2, HasMonochromaticAP N 2 color k

theorem theorem_18_2_iff_forall_length :
    theorem_18_2 ↔ ∀ k, 0 < k → Theorem182At k := by
  constructor
  · intro h k hk delta N hδ hδ2 hN A hA hc
    exact h delta k N hδ hδ2 hk hN A hA hc
  · intro h delta k N hδ hδ2 hk hN A hA hc
    exact h k hk delta N hδ hδ2 hN A hA hc

theorem corollary_18_7_iff_forall_length :
    corollary_18_7 ↔ ∀ k, 0 < k → Corollary187At k := by
  constructor
  · intro h k hk N hN color
    exact h k N hk hN color
  · intro h k N hk hN color
    exact h k hk N hN color

/-- Theorem 18.2 at a length gives Corollary 18.7 at that length. -/
theorem Theorem182At.corollary_18_7 {k : Nat} (h : Theorem182At k) : Corollary187At k :=
  corollary_18_7_at_of_half_density fun N hN A hA hc =>
    h (1 / 2) N (by norm_num) le_rfl hN A hA hc

/-- Roth's explicit threshold lies below the source threshold at every length. -/
theorem roth_threshold_le_szemerediThreshold (k : Nat) {delta : Real}
    (hδ : 0 < delta) (hδ2 : delta ≤ 1 / 2) :
    Real.exp (Real.exp (1000000000000 * delta⁻¹)) ≤ szemerediThreshold delta k := by
  have hu : (2 : Real) ≤ delta⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hδ).mpr (by linarith)
  have hu1 : (1 : Real) ≤ delta⁻¹ := by linarith
  have hu0 : (0 : Real) ≤ delta⁻¹ := by linarith
  -- The exponent of `delta⁻¹` in the source threshold is at least 42.
  have hx : (6 : Real) ≤ (2 : Real) ^ (k + 9 : Nat) := by
    have h9 : (2 : Real) ^ (9 : Nat) ≤ (2 : Real) ^ (k + 9 : Nat) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h512 : (6 : Real) ≤ (2 : Real) ^ (9 : Nat) := by norm_num
    linarith
  have hE : (42 : Real) ≤ (2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat)) := by
    have h64 : (2 : Real) ^ (6 : Real) ≤ (2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
    have h64' : (2 : Real) ^ (6 : Real) = 64 := by
      rw [show (6 : Real) = ((6 : Nat) : Real) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  have hpow42 : delta⁻¹ ^ (42 : Nat) ≤
      delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat))) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by exact_mod_cast hE)
  have h41 : (2 : Real) ^ (41 : Nat) ≤ delta⁻¹ ^ (41 : Nat) :=
    pow_le_pow_left₀ (by norm_num) hu 41
  have hinner : 1 + 2 * (1000000000000 * delta⁻¹) ≤
      delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat))) := by
    have h41' : (2000000000001 : Real) ≤ delta⁻¹ ^ (41 : Nat) := by
      have : (2000000000001 : Real) ≤ (2 : Real) ^ (41 : Nat) := by norm_num
      linarith
    have h42 : delta⁻¹ ^ (42 : Nat) = delta⁻¹ * delta⁻¹ ^ (41 : Nat) := by ring
    nlinarith [mul_le_mul_of_nonneg_left h41' hu0, hpow42, h42, hu1]
  unfold szemerediThreshold
  apply (section18_exp_le_two_rpow (Real.exp_pos _).le).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    2 * Real.exp (1000000000000 * delta⁻¹) ≤
        2 * (2 : Real) ^ (2 * (1000000000000 * delta⁻¹)) :=
      mul_le_mul_of_nonneg_left (section18_exp_le_two_rpow (by positivity)) (by norm_num)
    _ = (2 : Real) ^ (1 + 2 * (1000000000000 * delta⁻¹)) := by
      rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner

/-- **Theorem 18.2 for lengths at most three**, from Roth's theorem. -/
theorem theorem_18_2_le_three {k : Nat} (hk : k ≤ 3) : Theorem182At k := by
  intro delta N hδ hδ2 hN A hA hc
  obtain ⟨a, d, hd, h⟩ := roth_explicit_threshold delta N hδ
    ((roth_threshold_le_szemerediThreshold k hδ hδ2).trans hN) A hA hc
  exact ⟨a, d, hd, fun i hi => h i (by omega)⟩

/-- **Theorem 18.2 at every length up to five**, with the source thresholds. -/
theorem theorem_18_2_le_five {k : Nat} (hk : k ≤ 5) : Theorem182At k := by
  rcases (by omega : k ≤ 3 ∨ k = 4 ∨ k = 5) with h | rfl | rfl
  · exact theorem_18_2_le_three h
  · exact fun delta N hδ hδ2 hN A hA hc => theorem_18_2_four_holds delta N hδ hδ2 hN A hA hc
  · exact fun delta N hδ hδ2 hN A hA hc => theorem_18_2_five_holds delta N hδ hδ2 hN A hA hc

/-- **Corollary 18.7 at every length up to five.** -/
theorem corollary_18_7_le_five {k : Nat} (hk : k ≤ 5) : Corollary187At k :=
  (theorem_18_2_le_five hk).corollary_18_7

end LeanProofs.GowersSzemeredi
