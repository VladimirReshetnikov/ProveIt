import GowersSzemeredi.Proofs13UniformDensityParameters

/-! Recurrence thresholds uniform over a positive density interval. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- Increasing density only relaxes the endpoint-deletion mass budget. -/
theorem section13_recurrence_scale_density_mono {a b : Real} {q L : Nat}
    (ha : 0 < a) (hab : a ≤ b) (h : Section13RecurrenceScale a q L) :
    Section13RecurrenceScale b q L := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hp := pow_le_pow_left₀ ha.le hab 32
  have hx := h.2.1
  have hm := h.2.2
  nlinarith only [hp, hx, hm]

/-- At each positive spectrum size, one threshold handles all actual
 densities above a fixed positive lower bound. -/
theorem section13_eventually_density_recurrence_scale {delta : Real}
    (hδ : 0 < delta) {q : Nat} (hq : 0 < q) :
    ∀ᶠ N : Nat in atTop, ∀ alpha : Real, delta ≤ alpha → ∀ p L : Nat,
      IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
        (64 * Real.pi) * (N : Real) ^
          (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) → Section13RecurrenceScale alpha q L := by
  let theta := section10Lambda (delta ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hθ₁ : 0 < section13ThetaOne theta := by unfold section13ThetaOne; positivity
  have hd : 0 < section13ThetaOne theta / (64 * Real.pi) :=
    div_pos hθ₁ (mul_pos (by norm_num) Real.pi_pos)
  have hu : 0 < section13ThetaOne theta ^ 2 / (16 * (q : Real)) :=
    div_pos (pow_pos hθ₁ _) (mul_pos (by norm_num) (by exact_mod_cast hq))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (section13_eventually_recurrence_scale hδ q)
  filter_upwards [eventually_nat_mul_rpow_le (C := (L₀ : Real) + 2) hu hd,
    eventually_ge_atTop (1 : Nat)] with N hN hNpos
  intro alpha hδα p L hp hL
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hNpos
  have ht := section13ThetaOne_mono hθ.le (section13_cutoff_mono hδ hδα)
  have hdle := div_le_div_of_nonneg_right ht (by positivity : (0 : Real) ≤ 64 * Real.pi)
  have hule := div_le_div_of_nonneg_right (pow_le_pow_left₀ hθ₁.le ht 2)
    (by positivity : (0 : Real) ≤ 16 * q)
  have hx : (L₀ : Real) + 2 ≤
      section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) *
        (N : Real) ^ (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 /
          (16 * (q : Real))) := by
    calc
      _ ≤ section13ThetaOne theta / (64 * Real.pi) *
          (N : Real) ^ (section13ThetaOne theta ^ 2 / (16 * (q : Real))) := by
        simpa only [Real.rpow_zero, mul_one] using hN
      _ ≤ _ := mul_le_mul hdle (Real.rpow_le_rpow_of_exponent_le hNreal hule)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hd.le.trans hdle)
  have hLL : L₀ ≤ L := by
    have hupp := hp.2
    have hreal : (L₀ : Real) ≤ L := by
      rcases hL with hL | hL
      · subst L
        linarith only [hupp, hx]
      · have hLc : (L : Real) + 1 = p := by exact_mod_cast hL
        linarith only [hupp, hx, hLc]
    exact_mod_cast hreal
  exact section13_recurrence_scale_density_mono hδ hδα (hL₀ L hLL)

/-- The recurrence threshold depends only on a lower density bound, uniformly
in the actual density, spectrum size, and progression data. -/
theorem section13_uniform_density_recurrence_scale {delta : Real} (hδ : 0 < delta) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ alpha : Real, delta ≤ alpha → ∀ q p L : Nat,
      0 < q → (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)) →
      IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
        (64 * Real.pi) * (N : Real) ^
          (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) → Section13RecurrenceScale alpha q L := by
  let B := section13QBound (section10Lambda (delta ^ 32 / 16))
  have hall : ∀ᶠ N : Nat in atTop, ∀ q ∈ Finset.range (Nat.floor B + 1),
      0 < q → ∀ alpha : Real, delta ≤ alpha → ∀ p L : Nat,
      IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
        (64 * Real.pi) * (N : Real) ^
          (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) → Section13RecurrenceScale alpha q L := by
    apply (eventually_all_finset _).mpr
    intro q _
    by_cases hq : 0 < q
    · filter_upwards [section13_eventually_density_recurrence_scale hδ hq] with N hN
      exact fun _ => hN
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hall
  refine ⟨N₀, fun N hN alpha hδα q p L hq hqB => ?_⟩
  have hθ : 0 < section10Lambda (delta ^ 32 / 16) := by unfold section10Lambda; positivity
  have hqfloor : q ≤ Nat.floor B := Nat.le_floor (hqB.trans
    (section13QBound_antitone hθ (section13_cutoff_mono hδ hδα)))
  exact hN₀ N hN q (Finset.mem_range.mpr (by omega)) hq alpha hδα p L

/-- Stage 13.5 constructed with a threshold depending only on a positive
lower bound for the context density. -/
theorem lemma_13_5_uniform_density {delta : Real} (hδ : 0 < delta) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N) (D : Stage134Data N),
      delta ≤ S.alpha → N₀ ≤ N →
      IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D →
      ∃ E : Stage135Data N, IsStage135Data S D E := by
  obtain ⟨N₀, hN₀⟩ := section13_uniform_density_recurrence_scale hδ
  refine ⟨max N₀ 3, fun N _ S D hS hN h134 => ?_⟩
  have hs := hN₀ N ((le_max_left _ _).trans hN) S.alpha hS D.q D.m D.P.length
    h134.1 h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1
  have hNthree : 3 ≤ N := (le_max_right _ _).trans hN
  exact lemma_13_5_with_scale (Fact.out : N.Prime) (bne_iff_ne.mpr (by omega))
    S D (section10Lambda (S.alpha ^ 32 / 16)) h134 hs.1 hs.2.1 hs.2.2

end LeanProofs.GowersSzemeredi
