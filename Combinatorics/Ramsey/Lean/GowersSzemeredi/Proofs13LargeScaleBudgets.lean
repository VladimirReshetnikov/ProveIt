import GowersSzemeredi.Proofs13IntegerBudgets

/-! Large-N budgets for the Stage 13 extraction chain. The threshold is
uniform over the preceding data, but is not given as an explicit numeral. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- The numerical inputs to the assembled Stage 13.6--13.9 construction. -/
def Section13IntegerBudgets (alpha : Real) (N q P Q : Nat) : Prop :=
  ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
    section13Zeta alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤ m ∧
    (P : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * q))) ≤
      section10Zeta (alpha ^ 32 / 16) / m ∧
    (2 : Real) ^ 135 * alpha ^ (-(704 : Int)) ≤
      (section13Zeta alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha))) ^
          ((2 : Real) ^ (-(100 : Int)) * alpha ^ 448)

/-- For each permitted q, the floor and possible loss of one endpoint in
Stage 13.4 are absorbed while preserving the target exponent. -/
theorem section13_eventually_integer_budgets {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) {q : Nat} (hq : 0 < q)
    (hqBound : (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16))) :
    ∀ᶠ N : Nat in atTop, ∀ p L Q : Nat,
      IsNatFloor
        (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) *
          (N : Real) ^ (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 /
            (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) →
      (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) / 2 ≤ Q →
      Section13IntegerBudgets alpha N q L Q := by
  let theta := section10Lambda (alpha ^ 32 / 16)
  let c := section13Zeta alpha / 2
  let d := section13ThetaOne theta / (64 * Real.pi)
  let z := section10Zeta (alpha ^ 32 / 16)
  let e := (1 : Real) / (2 : Real) ^ (13 * section13Q alpha)
  let u := section13ThetaOne theta ^ 2 / (16 * (q : Real))
  let v := (1 : Real) / (2 : Real) ^ (12 * q)
  let w := (1 : Real) / (2 : Real) ^ (11 * q)
  let f := (2 : Real) ^ (-(100 : Int)) * alpha ^ 448
  have hqpos : (0 : Real) < q := by exact_mod_cast hq
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hθ₁ : 0 < section13ThetaOne theta := by unfold section13ThetaOne; positivity
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have hd : 0 < d := div_pos hθ₁ (mul_pos (by norm_num) Real.pi_pos)
  have ha : 0 < alpha ^ 32 / 16 := by positivity
  have hk : 0 < section10SpectrumParameter (alpha ^ 32 / 16) := by
    apply Nat.one_le_ceil_iff.mpr
    unfold section10SpectrumBound
    positivity
  have hz : 0 < z := by
    dsimp [z, section10Zeta]
    exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos ha _))
      (by exact_mod_cast hk)
  have he : 0 < e := by dsimp [e]; positivity
  have hu : 0 < u := div_pos (pow_pos hθ₁ _) (mul_pos (by norm_num) hqpos)
  have hv : 0 < v := by dsimp [v]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hf : 0 < f := mul_pos (zpow_pos (by norm_num) _) (pow_pos hα _)
  have hQ : 1 ≤ section13Q alpha := by
    have hqone : (1 : Real) ≤ q := by exact_mod_cast hq
    have hqQ := hqBound.trans (section13_qBound_le_half_Q hα hαone)
    linarith only [hqone, hqQ]
  have htwo : (2 : Real) < (2 : Real) ^ (13 * section13Q alpha) := by
    calc
      _ = (2 : Real) ^ (1 : Real) := (Real.rpow_one _).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith only [hQ])
  have hsquare : 2 * e < 1 := by
    dsimp [e]
    exact (by simpa only [div_eq_mul_inv, one_mul] using
      (div_lt_one (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) _)).mpr htwo)
  have hrec : e < u * v := section13_recurrence_exponent_margin hα hαone hq hqBound
  have hvw : v ≤ w := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega : 11 * q ≤ 12 * q)
  have hbohr : e < u * w := hrec.trans_le (mul_le_mul_of_nonneg_left hvw hu.le)
  obtain ⟨N₀, hN₀⟩ := eventually_rounded_power_budgets
    (d := d / 2) (W := (2 : Real) ^ 135 * alpha ^ (-(704 : Int))) hc
    (div_pos hd (by norm_num)) hz he hv hw hf hsquare hrec hbohr
  have hfloor := eventually_nat_mul_rpow_le (C := 4) (D := d) hu hd
  filter_upwards [eventually_ge_atTop N₀, hfloor] with N hN hfloor
  intro p L Q hp hL hQlen
  have hlarge : 4 ≤ d * (N : Real) ^ u := by
    simpa only [Real.rpow_zero, mul_one] using hfloor
  have hPlower : d / 2 * (N : Real) ^ u ≤ (L : Real) := by
    have hpupper := hp.2
    change d * (N : Real) ^ u < (p : Real) + 1 at hpupper
    rcases hL with hL | hL
    · subst L
      nlinarith only [hlarge, hpupper]
    · have hLc : (L : Real) + 1 = p := by exact_mod_cast hL
      nlinarith only [hlarge, hpupper, hLc]
  obtain ⟨m, hm, hmsq, hmQ, hmlower, hmbohr, hmwidth⟩ :=
    hN₀ N hN L Q hPlower hQlen
  refine ⟨m, hm, ?_, ?_, hmlower, hmbohr, hmwidth⟩
  · simpa only [pow_two] using hmsq
  · exact_mod_cast hmQ

/-- A single threshold works for all possible spectrum sizes and all
progression data satisfying the Stage 13.4--13.5 numerical conclusions. -/
theorem section13_uniform_integer_budgets {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ q p L Q : Nat,
      0 < q → (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)) →
      IsNatFloor
        (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) *
          (N : Real) ^ (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 /
            (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) →
      (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) / 2 ≤ Q →
      Section13IntegerBudgets alpha N q L Q := by
  let B := section13QBound (section10Lambda (alpha ^ 32 / 16))
  have hall : ∀ᶠ N : Nat in atTop, ∀ q ∈ Finset.range (Nat.floor B + 1),
      0 < q → (q : Real) ≤ B → ∀ p L Q : Nat,
      IsNatFloor
        (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) *
          (N : Real) ^ (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 /
            (16 * (q : Real)))) p →
      (L = p ∨ L + 1 = p) →
      (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) / 2 ≤ Q →
      Section13IntegerBudgets alpha N q L Q := by
    apply (eventually_all_finset _).mpr
    intro q _
    by_cases hq : 0 < q
    · by_cases hqB : (q : Real) ≤ B
      · filter_upwards [section13_eventually_integer_budgets hα hαone hq hqB] with N hN
        exact fun _ _ => hN
      · exact Eventually.of_forall (fun _ _ h => (hqB h).elim)
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hall
  refine ⟨N₀, fun N hN q p L Q hq hqB => ?_⟩
  have hqfloor : q ≤ Nat.floor B := Nat.le_floor hqB
  exact hN₀ N hN q (Finset.mem_range.mpr (by omega)) hq hqB p L Q

/-- For each fixed density at most 1/6, the Stage 13.6 construction works
uniformly for sufficiently large prime moduli, with no numerical-budget
hypotheses. The preceding Stage 13.4 and 13.5 data are still required. -/
theorem lemma_13_6_large_N {alpha : Real} (hα : 0 < alpha) (hαsixth : alpha ≤ 1 / 6) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime]
      (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N),
      S.alpha = alpha → N₀ ≤ N →
      IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D →
      IsStage135Data S D E →
      ∃ F : Stage136Data N, IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length := by
  obtain ⟨N₀, hN₀⟩ := section13_uniform_integer_budgets hα (hαsixth.trans (by norm_num))
  refine ⟨N₀, fun N _ S D E hS hN h134 h135 => ?_⟩
  have hb := hN₀ N hN D.q D.m D.P.length E.Q.length h134.1
    (by simpa only [hS] using h134.2.2.2.2.1)
    (by simpa only [hS] using h134.2.2.2.2.2.1)
    h134.2.2.2.2.2.2.1 h135.2.2.2.1
  rw [← hS] at hb
  obtain ⟨m, hm, hsize, hupper, hlower, hbudget, _⟩ := hb
  exact lemma_13_6_from_initial_stages S D E m (by simpa only [hS] using hαsixth)
    h134 h135 hm hsize hupper hlower hbudget

/-- The entire Stage 13.6--13.9 extraction follows at sufficiently large N
from the preceding data. The threshold depends only on alpha, and all six
numerical budgets have been proved. This does not construct Stage 13.5 or
supply the stronger square-grid geometry needed for Corollary 13.10. -/
theorem section13_bilinear_extraction_large_N {alpha : Real}
    (hα : 0 < alpha) (hαsixth : alpha ≤ 1 / 6) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime]
      (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N),
      S.alpha = alpha → N₀ ≤ N →
      IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D →
      IsStage135Data S D E →
      ∃ F : Stage136Data N, ∃ G : Stage137Data N, ∃ H : Stage138Data N, ∃ J : Stage139Data N,
        IsStage136Data S D E F ∧ F.R.length ≤ E.Q.length ∧
        IsStage137Data S D E F G ∧ IsStage138Data S D E G H ∧
        IsStage139Data S E G H J := by
  obtain ⟨N₀, hN₀⟩ := section13_uniform_integer_budgets hα (hαsixth.trans (by norm_num))
  refine ⟨N₀, fun N _ S D E hS hN h134 h135 => ?_⟩
  have hb := hN₀ N hN D.q D.m D.P.length E.Q.length h134.1
    (by simpa only [hS] using h134.2.2.2.2.1)
    (by simpa only [hS] using h134.2.2.2.2.2.1)
    h134.2.2.2.2.2.2.1 h135.2.2.2.1
  rw [← hS] at hb
  obtain ⟨m, hm, hsize, hupper, hlower, hbudget, hwidth⟩ := hb
  exact section13_bilinear_extraction_of_budgets S D E m (by simpa only [hS] using hαsixth)
    h134 h135 hm hsize hupper hlower hbudget hwidth

end LeanProofs.GowersSzemeredi
