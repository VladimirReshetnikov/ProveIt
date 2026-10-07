import GowersSzemeredi.Proofs13SquareScale

/-! A direct large-N common-step bilinear square theorem from the original
Section 13 context, retaining an explicit positive power of N. -/

set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

/-- The explicit exponent retained by the complete square construction. -/
def section13SquareExponent (alpha : Real) : Real :=
  ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) *
    ((2 : Real) ^ (-(100 : Int)) * alpha ^ 448) *
    cor711Exponent ((2 : Real) ^ (-(135 : Int)) * alpha ^ 704) 1 / 4

theorem section13SquareExponent_pos {alpha : Real} (hα : 0 < alpha) :
    0 < section13SquareExponent alpha := by
  unfold section13SquareExponent cor711Exponent
  positivity

set_option exponentiation.threshold 512 in
/-- Closed form of the positive power retained after all floor and square
losses, with the corrected upstream coefficient exponents. -/
theorem section13SquareExponent_formula (alpha : Real) :
    section13SquareExponent alpha =
      (2 : Real) ^ (-(386 : Int)) * alpha ^ 1856 /
        (2 : Real) ^ (13 * section13Q alpha) := by
  unfold section13SquareExponent
  rw [stage139_partition_exponent]
  norm_num [zpow_neg]
  ring

/-- At each fixed density at most 1/6, sufficiently large prime moduli admit
a proper equal-length common-step square, a dense subset of the original
domain on that square, and a bilinear formula there. All intermediate data,
integer step geometry, partitions, and scale budgets are constructed. -/
theorem section13_complete_square_extraction {alpha : Real}
    (hα : 0 < alpha) (hαsixth : alpha ≤ 1 / 6) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N),
      S.alpha = alpha → N₀ ≤ N →
      ∃ V W : ModAP N, ∃ B : Finset (Pair N),
        V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
        (N : Real) ^ section13SquareExponent alpha ≤ V.length ∧
        B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
        (2 : Real) ^ (-(137 : Int)) * alpha ^ 704 * V.length * W.length ≤ B.card ∧
        BilinearOn B S.phi := by
  let theta := section10Lambda (alpha ^ 32 / 16)
  let c := section13Zeta alpha / 2
  let e := (1 : Real) / (2 : Real) ^ (13 * section13Q alpha)
  let f := (2 : Real) ^ (-(100 : Int)) * alpha ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * alpha ^ 704) 1
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := mul_pos (zpow_pos (by norm_num) _) (pow_pos hα _)
  have hg : 0 < g := by dsimp [g, cor711Exponent]; positivity
  obtain ⟨N₁, hN₁⟩ := lemma_13_5_large_N hα hθ
  obtain ⟨N₂, hN₂⟩ := lemma_13_6_large_N hα hαsixth
  obtain ⟨N₃, hN₃⟩ := square_scales_above_power_lower_bound
    (W := (2 : Real) ^ 135 * alpha ^ (-(704 : Int))) hc he hf hg
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp (eventually_square_power_lower hc he hf hg)
  refine ⟨max N₁ (max N₂ (max N₃ N₄)), fun N _ S hS hN => ?_⟩
  obtain ⟨D, hD⟩ := lemma_13_4_holds N S theta (Fact.out : N.Prime) hθ
    (by simpa only [hS] using section13_lambda_le_initial_threshold hα (hαsixth.trans (by norm_num)))
  obtain ⟨E, hE⟩ := hN₁ N S D hS (by omega) hD
  have hD' : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D := by
    simpa only [hS] using hD
  obtain ⟨F, hF, hFupper⟩ := hN₂ N S D E hS (by omega) hD' hE
  have hminimum : c * (N : Real) ^ e ≤ F.R.length := by
    simpa only [hS] using hF.2.2.2.1
  obtain ⟨hr, hw, hs⟩ := hN₃ N (by omega) F.R.length hminimum
  obtain ⟨V, W, B, hVs, hVW, hV, hW, hVl, hsize, hBA, hbox, hmass, hbil⟩ :=
    section13_square_extraction_of_scales S D E F hE hF hFupper
      (by simpa only [hS] using hr) (by simpa only [hS] using hw) (by simpa only [hS] using hs)
  have hsmall : (c * (N : Real) ^ e) ^ f ≤ (F.R.length : Real) ^ f :=
    Real.rpow_le_rpow (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hminimum hf.le
  have hfloor : Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 ≤
      Nat.floor ((F.R.length : Real) ^ f) / 2 := Nat.div_le_div_right (Nat.floor_mono hsmall)
  have hfloorR : ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ≤
      ((Nat.floor ((F.R.length : Real) ^ f) / 2 : Nat) : Real) := by exact_mod_cast hfloor
  have hpower := Real.rpow_le_rpow (Nat.cast_nonneg _) hfloorR (div_nonneg hg.le (by norm_num : (0 : Real) ≤ 2))
  have hNpower := hN₄ N (by omega)
  have hsize' : ((Nat.floor ((F.R.length : Real) ^ f) / 2 : Nat) : Real) ^ (g / 2) - 1 ≤ V.length := by
    simpa only [hS] using hsize
  refine ⟨V, W, B, hVs, hVW, hV, hW, hVl, ?_, hBA, hbox, ?_, hbil⟩
  · change (N : Real) ^ (e * f * g / 4) ≤ V.length
    linarith only [hNpower, hpower, hsize']
  · simpa only [hS] using hmass

end LeanProofs.GowersSzemeredi
