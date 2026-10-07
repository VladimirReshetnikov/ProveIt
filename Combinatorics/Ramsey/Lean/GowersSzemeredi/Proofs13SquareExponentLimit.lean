import GowersSzemeredi.Proofs13ImprovedSquareExtraction
import GowersSzemeredi.Proofs13ConstructedWidth

/-! The fixed constants in square extraction cost an arbitrarily small
positive amount of the exponent, rather than a fixed factor of two. -/

set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

/-- Every positive exponent below the power before fixed floor and endpoint
losses survives those losses for sufficiently large moduli. -/
theorem eventually_square_power_lower_of_exponent_lt {c e f g beta : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g)
    (hb : 0 < beta) (hbeta : beta < e * f * g / 2) :
    ∀ᶠ N : Nat in atTop, (N : Real) ^ beta ≤
      ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ^ (g / 2) - 1 := by
  let C := (c ^ f / 4) ^ (g / 2)
  have hC : 0 < C := Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hc _) (by norm_num)) _
  have hef : 0 < e * f := mul_pos he hf
  have hfg : 0 < e * f * g := mul_pos hef hg
  have hgap : beta < e * f * (g / 2) := by nlinarith only [hbeta]
  filter_upwards [eventually_nat_mul_rpow_le (C := 4) (D := c ^ f) hef (Real.rpow_pos_of_pos hc _),
    eventually_nat_mul_rpow_le (C := 2) (D := C) hgap hC,
    eventually_ge_atTop (1 : Nat)] with N hfour hpower hN
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hfour' : 4 ≤ (c * (N : Real) ^ e) ^ f := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    simpa only [Real.rpow_zero, mul_one] using hfour
  have hquarter := quarter_le_floor_half hfour'
  have hpow : ((c * (N : Real) ^ e) ^ f / 4) ^ (g / 2) =
      C * (N : Real) ^ (e * f * (g / 2)) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg N),
      show c ^ f * (N : Real) ^ (e * f) / 4 = c ^ f / 4 * (N : Real) ^ (e * f) by ring,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hlarge : 2 * (N : Real) ^ beta ≤
      ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ^ (g / 2) := by
    calc
      _ ≤ C * (N : Real) ^ (e * f * (g / 2)) := hpower
      _ = _ := hpow.symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hquarter (by positivity)
  have hone : 1 ≤ (N : Real) ^ beta := Real.one_le_rpow hNreal (by positivity)
  linarith only [hlarge, hone]

/-- A fixed positive coefficient and a final subtraction of one cost any
chosen positive exponent gap, for sufficiently large natural arguments. -/
theorem eventually_power_sub_one_lower {c e beta : Real}
    (hc : 0 < c) (hb : 0 < beta) (hgap : beta < e) :
    ∀ᶠ N : Nat in atTop, (N : Real) ^ beta ≤ c * (N : Real) ^ e - 1 := by
  filter_upwards [eventually_nat_mul_rpow_le (C := 2) (D := c) hgap hc,
    eventually_ge_atTop (1 : Nat)] with N hpower hN
  have hone : 1 ≤ (N : Real) ^ beta :=
    Real.one_le_rpow (by exact_mod_cast hN) hb.le
  linarith only [hpower, hone]

/-- At each fixed density, every positive exponent below the pre-constant
limit is attained by the numbered extraction chain. Only the column width
needed by Lemma 13.8 and the fixed-coefficient power gap set the threshold. -/
theorem section13_complete_square_extraction_below_limit {alpha beta : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) (hbeta : 0 < beta)
    (hlimit : beta < 2 * section13ImprovedSquareExponent alpha) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N),
      S.alpha = alpha → N₀ ≤ N →
      ∃ V W : ModAP N, ∃ B : Finset (Pair N),
        V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
        (N : Real) ^ beta ≤ V.length ∧
        B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
        (2 : Real) ^ (-(137 : Int)) * alpha ^ 704 * V.length * W.length ≤ B.card ∧
        BilinearOn B S.phi := by
  let theta := section10Lambda (alpha ^ 32 / 16)
  let c := section13Zeta alpha / 2
  let e := (1 : Real) / (2 : Real) ^ (10 * section13Q alpha)
  let f := (2 : Real) ^ (-(100 : Int)) * alpha ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * alpha ^ 704) 1
  let W : Real := (2 : Real) ^ 135 * alpha ^ (-(704 : Int))
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := mul_pos (zpow_pos (by norm_num) _) (pow_pos hα _)
  have hg : 0 < g := by dsimp [g, cor711Exponent]; positivity
  have hfg : 0 < f * g / 2 := by positivity
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp
    (eventually_nat_mul_rpow_le (C := max 8 W) (D := c ^ f)
      (mul_pos he hf) (Real.rpow_pos_of_pos hc f))
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp
    (eventually_power_sub_one_lower (c := c ^ (f * g / 2)) (e := e * (f * g / 2))
      (Real.rpow_pos_of_pos hc _) hbeta (by
        dsimp [section13ImprovedSquareExponent, e, f, g] at hlimit ⊢
        linarith only [hlimit]))
  refine ⟨max N₃ N₄, fun N _ S hS hN => ?_⟩
  obtain ⟨D, hD⟩ := lemma_13_4_holds N S theta (Fact.out : N.Prime) hθ
    (by simpa only [hS] using section13_lambda_le_initial_threshold hα hαone)
  obtain ⟨E, hE⟩ := lemma_13_5_prime (Fact.out : N.Prime) S D theta hD
  have hD' : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D := by
    simpa only [hS] using hD
  obtain ⟨F, hF, hFlower, hFmax⟩ := lemma_13_6_improved_length (Fact.out : N.Prime) S D E hD' hE
  have hminimum : c * (N : Real) ^ e ≤ F.R.length := by
    simpa only [hS] using hFlower
  have hscale : max 8 W ≤ (c * (N : Real) ^ e) ^ f := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    simpa only [Real.rpow_zero, mul_one] using hN₃ N (by omega)
  have hscaleF : max 8 W ≤ (F.R.length : Real) ^ f := hscale.trans
    (Real.rpow_le_rpow (by positivity) hminimum hf.le)
  have hr : 8 ≤ (F.R.length : Real) ^ f := (le_max_left _ _).trans hscaleF
  have hw : W ≤ (F.R.length : Real) ^ f := (le_max_right _ _).trans hscaleF
  have hRtwo : 2 ≤ F.R.length := by
    by_contra hnot
    have hle : (F.R.length : Real) ≤ 1 := by exact_mod_cast (by omega : F.R.length ≤ 1)
    have hp := Real.rpow_le_one (Nat.cast_nonneg F.R.length) hle hf.le
    linarith only [hr, hp]
  have hFupper : F.R.length ≤ E.Q.length := by omega
  obtain ⟨V, W', B, hVs, hVW, hV, hW, hVl, hsize, hBA, hbox, hmass, hbil⟩ :=
    section13_square_extraction_of_width S D E F hE hF hFupper
      (by simpa only [hS] using hw)
  have hpower : (c * (N : Real) ^ e) ^ (f * g / 2) ≤
      (F.R.length : Real) ^ (f * g / 2) :=
    Real.rpow_le_rpow (by positivity) hminimum hfg.le
  have hNpower : (N : Real) ^ beta ≤ (c * (N : Real) ^ e) ^ (f * g / 2) - 1 := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    exact hN₄ N (by omega)
  have hsize' : (F.R.length : Real) ^ (f * g / 2) - 1 ≤ V.length := by
    simpa only [hS, f, g, stage139_partition_exponent] using hsize
  refine ⟨V, W', B, hVs, hVW, hV, hW, hVl, ?_, hBA, hbox, ?_, hbil⟩
  · linarith only [hNpower, hpower, hsize']
  · simpa only [hS] using hmass

set_option exponentiation.threshold 512 in
/-- The limiting exponent approached by the completed extraction. The
strict inequality in the extraction theorem is essential. -/
theorem section13_square_exponent_limit_formula (alpha : Real) :
    2 * section13ImprovedSquareExponent alpha =
      (2 : Real) ^ (-(385 : Int)) * alpha ^ 1856 /
        (2 : Real) ^ (10 * section13Q alpha) := by
  rw [section13ImprovedSquareExponent_formula]
  norm_num [zpow_neg]
  ring

/-- A concrete fifty-percent increase in the previously published exponent,
with the same density and full containment in the original domain. -/
theorem section13_complete_square_extraction_three_halves {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N),
      S.alpha = alpha → N₀ ≤ N →
      ∃ V W : ModAP N, ∃ B : Finset (Pair N),
        V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
        (N : Real) ^ ((3 / 2) * section13ImprovedSquareExponent alpha) ≤ V.length ∧
        B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
        (2 : Real) ^ (-(137 : Int)) * alpha ^ 704 * V.length * W.length ≤ B.card ∧
        BilinearOn B S.phi := by
  have hpos := section13ImprovedSquareExponent_pos hα
  exact section13_complete_square_extraction_below_limit hα hαone (by positivity) (by linarith)

end LeanProofs.GowersSzemeredi
