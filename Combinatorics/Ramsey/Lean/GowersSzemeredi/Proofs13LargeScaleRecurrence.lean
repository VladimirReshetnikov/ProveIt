import GowersSzemeredi.Proofs13QuadraticPartition
import GowersSzemeredi.Proofs13LargeScaleBudgets

/-! The numerical hypotheses of quadratic recurrence hold uniformly at
large N. This constructs the preceding stages needed by bilinear extraction. -/

set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

/-- A floor, with a possible further loss of one, still eventually exceeds
any fixed integer when its underlying positive power tends to infinity. -/
theorem eventually_floor_progression_length_ge {d u : Real}
    (hd : 0 < d) (hu : 0 < u) (C : Nat) :
    ∀ᶠ N : Nat in atTop, ∀ p L : Nat,
      IsNatFloor (d * (N : Real) ^ u) p → (L = p ∨ L + 1 = p) → C ≤ L := by
  filter_upwards [eventually_nat_mul_rpow_le (C := (C : Real) + 2) hu hd] with N hN
  intro p L hp hL
  have hx : (C : Real) + 2 ≤ d * (N : Real) ^ u := by
    simpa only [Real.rpow_zero, mul_one] using hN
  have hupper := hp.2
  have hCL : (C : Real) ≤ L := by
    rcases hL with hL | hL
    · subst L
      linarith only [hx, hupper]
    · have hLc : (L : Real) + 1 = p := by exact_mod_cast hL
      linarith only [hx, hupper, hLc]
  exact_mod_cast hCL

/-- Sufficient progression-size conditions for the checked quadratic
recurrence and its endpoint deletion. -/
def Section13RecurrenceScale (alpha : Real) (q L : Nat) : Prop :=
  simultaneousPolynomialThreshold 2 q < L ∧
  8 ≤ (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) ∧
  160 + 2 * alpha ^ 32 ≤ alpha ^ 32 * (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q))

/-- At every fixed density and q, sufficiently long progressions meet all
the recurrence and endpoint-deletion size conditions. -/
theorem section13_eventually_recurrence_scale {alpha : Real} (hα : 0 < alpha) (q : Nat) :
    ∀ᶠ L : Nat in atTop, Section13RecurrenceScale alpha q L := by
  have he : (0 : Real) < (1 : Real) / (2 : Real) ^ (12 * q) := by positivity
  have ha : 0 < alpha ^ 32 := pow_pos hα _
  filter_upwards [eventually_ge_atTop (simultaneousPolynomialThreshold 2 q + 1),
    eventually_nat_mul_rpow_le (C := 8) (D := 1) he zero_lt_one,
    eventually_nat_mul_rpow_le (C := 160 + 2 * alpha ^ 32) he ha] with L hL hs hm
  refine ⟨by omega, ?_, ?_⟩
  · simpa only [Real.rpow_zero, mul_one, one_mul] using hs
  · simpa only [Real.rpow_zero, mul_one] using hm

/-- For each positive q, the Stage 13.4 floor length eventually satisfies
the recurrence conditions. -/
theorem section13_eventually_initial_recurrence_scale {alpha theta : Real}
    (hα : 0 < alpha) (hθ : 0 < theta) {q : Nat} (hq : 0 < q) :
    ∀ᶠ N : Nat in atTop, ∀ p L : Nat,
      IsNatFloor (section13ThetaOne theta / (64 * Real.pi) *
        (N : Real) ^ (section13ThetaOne theta ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) → Section13RecurrenceScale alpha q L := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (section13_eventually_recurrence_scale hα q)
  have hθ₁ : 0 < section13ThetaOne theta := by unfold section13ThetaOne; positivity
  have hd : 0 < section13ThetaOne theta / (64 * Real.pi) :=
    div_pos hθ₁ (mul_pos (by norm_num) Real.pi_pos)
  have hu : 0 < section13ThetaOne theta ^ 2 / (16 * (q : Real)) :=
    div_pos (pow_pos hθ₁ _) (mul_pos (by norm_num) (by exact_mod_cast hq))
  filter_upwards [eventually_floor_progression_length_ge hd hu L₀] with N hN
  intro p L hp hL
  exact hL₀ L (hN p L hp hL)

/-- One threshold depends only on the density and Fourier cutoff, uniformly
over all possible Stage 13.4 spectrum sizes and floor data. -/
theorem section13_uniform_recurrence_scale {alpha theta : Real}
    (hα : 0 < alpha) (hθ : 0 < theta) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ q p L : Nat,
      0 < q → (q : Real) ≤ section13QBound theta →
      IsNatFloor (section13ThetaOne theta / (64 * Real.pi) *
        (N : Real) ^ (section13ThetaOne theta ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) → Section13RecurrenceScale alpha q L := by
  have hall : ∀ᶠ N : Nat in atTop, ∀ q ∈ Finset.range (Nat.floor (section13QBound theta) + 1),
      0 < q → ∀ p L : Nat,
      IsNatFloor (section13ThetaOne theta / (64 * Real.pi) *
        (N : Real) ^ (section13ThetaOne theta ^ 2 / (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) → Section13RecurrenceScale alpha q L := by
    apply (eventually_all_finset _).mpr
    intro q _
    by_cases hq : 0 < q
    · filter_upwards [section13_eventually_initial_recurrence_scale hα hθ hq] with N hN
      exact fun _ => hN
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hall
  refine ⟨N₀, fun N hN q p L hq hqB => ?_⟩
  have hqfloor : q ≤ Nat.floor (section13QBound theta) := Nat.le_floor hqB
  exact hN₀ N hN q (Finset.mem_range.mpr (by omega)) hq p L

/-- Stage 13.5 follows from Stage 13.4 at sufficiently large prime N.
The threshold is uniform over the context and the preceding data. -/
theorem lemma_13_5_large_N {alpha theta : Real} (hα : 0 < alpha) (hθ : 0 < theta) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime]
      (S : Section13Context N) (D : Stage134Data N),
      S.alpha = alpha → N₀ ≤ N → IsStage134Data S theta D →
      ∃ E : Stage135Data N, IsStage135Data S D E := by
  obtain ⟨N₀, hN₀⟩ := section13_uniform_recurrence_scale hα hθ
  refine ⟨max N₀ 3, fun N _ S D hS hN h134 => ?_⟩
  have hs := hN₀ N ((le_max_left _ _).trans hN) D.q D.m D.P.length
    h134.1 h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1
  rw [← hS] at hs
  have hNthree : 3 ≤ N := (le_max_right _ _).trans hN
  exact lemma_13_5_with_scale (Fact.out : N.Prime) (bne_iff_ne.mpr (by omega))
    S D theta h134 hs.1 hs.2.1 hs.2.2

/-- The common edge Fourier cutoff is admissible for the proved initial
progression theorem. -/
theorem section13_lambda_le_initial_threshold {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section10Lambda (alpha ^ 32 / 16) ≤ alpha ^ 32 / 4 := by
  rw [section13_lambda_formula hα]
  have hp : alpha ^ 176 ≤ alpha ^ 32 := pow_le_pow_of_le_one hα.le hαone (by omega)
  have hc : (2 : Real) ^ (-(59 : Int)) ≤ 1 / 4 := by norm_num
  calc
    _ ≤ (1 / 4 : Real) * alpha ^ 32 :=
      mul_le_mul hc hp (pow_nonneg hα.le _) (by norm_num)
    _ = _ := by ring

/-- For every fixed density at most 1/6, all data in Stages 13.4--13.9 are
constructed directly from the original context for sufficiently large prime
moduli. No recurrence data, row models, partitions, or numerical budgets are
assumed. The later square-grid extraction is still a separate obligation. -/
theorem section13_bilinear_extraction_from_context {alpha : Real}
    (hα : 0 < alpha) (hαsixth : alpha ≤ 1 / 6) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N),
      S.alpha = alpha → N₀ ≤ N →
      ∃ D : Stage134Data N, ∃ E : Stage135Data N, ∃ F : Stage136Data N,
      ∃ G : Stage137Data N, ∃ H : Stage138Data N, ∃ J : Stage139Data N,
        IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D ∧
        IsStage135Data S D E ∧ IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length ∧
        IsStage137Data S D E F G ∧ IsStage138Data S D E G H ∧
        IsStage139Data S E G H J := by
  let theta := section10Lambda (alpha ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hθupper := section13_lambda_le_initial_threshold hα (hαsixth.trans (by norm_num))
  obtain ⟨N₁, hN₁⟩ := lemma_13_5_large_N hα hθ
  obtain ⟨N₂, hN₂⟩ := section13_bilinear_extraction_large_N hα hαsixth
  refine ⟨max N₁ N₂, fun N _ S hS hN => ?_⟩
  obtain ⟨D, hD⟩ := lemma_13_4_holds N S theta (Fact.out : N.Prime) hθ
    (by simpa only [hS] using hθupper)
  obtain ⟨E, hE⟩ := hN₁ N S D hS ((le_max_left _ _).trans hN) hD
  have hD' : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D := by
    simpa only [hS] using hD
  obtain ⟨F, G, H, J, hF, hFupper, hG, hH, hJ⟩ :=
    hN₂ N S D E hS ((le_max_right _ _).trans hN) hD' hE
  exact ⟨D, E, F, G, H, J, hD', hE, hF, hFupper, hG, hH, hJ⟩

end LeanProofs.GowersSzemeredi
