import GowersSzemeredi.Proofs18GenericEnvelopeBase
import GowersSzemeredi.Proofs16SinglePieceCoverGlobal
import GowersSzemeredi.Proofs16ClassStepBoundsFejer

/-! **The fixed parameters of the Section 18 step under the Fejér θ₁**
(Notes L.16d).

The Section 18 envelope bounds the fixed parameters of dimension `k` at
`X = 2/α` (`Proofs18GenericEnvelopeBase`, and `lemma156_gen_le` in
`Proofs18GenericEnvelopeBaseSide`). The Fejér
density is at least the printed one,
`section16ThetaOne α (α/2) k ≤ fejerThetaOne α (α/2) k`
(`section16ThetaOne_le_fejer`, from `fejerProductExponent k ≤ 2^(2^(k+5))`),
and the budget, `θ₂/2`, `δ` and the radius are monotone in it. So each
printed bound transfers, at the same exponent:
* `budget_gen_bounds_fejer`, `T2_gen_bounds_fejer`, `delta_gen_bounds_fejer`
  (`X^(2^fixDeg k)`);
* `zeta_gen_bounds_fejer`: `tightZeta(θ₁′/4) ≥ section16Zeta`, because the
  tight exponent `2^83/(θ₁′/4)^11` is at most `2^83/(θ₁/4)^11 ≤ multipleS`
  (`section16_radius_exponent_budget`);
* `lemma156_gen_le_fejer`: the Fejér Lemma 15.6 threshold is at most
  `X^(2·fejerStepP k) ≤ X^(2^(2^(k+4)+4k+13))`, the printed slot.
The first two items are in `Proofs18FejerEnvelopeBaseSide`, outside the final
route.

The envelope then changes only through the class degree (`uDeg23` in place
of `uDeg68`).

`fejerProductExponent_le_printed`, `fejer_theta_ge_printed`,
`lemma156_gen_le_fejer`, `section16Delta_mono`, `section16ThetaOne_le_fejer` and
`section16ThetaTwo_mono` are in `Proofs18FejerEnvelopeBaseSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem coverExpW_pos_le (Eb : Nat → Real → Real → Real → Real)
    (hEb : ∀ l g t s, 0 < Eb l g t s ∧ Eb l g t s ≤ 1) (t1 gamma : Real) (k : Nat) :
    0 < coverExpW Eb t1 gamma k ∧ coverExpW Eb t1 gamma k ≤ 1 := by
  unfold coverExpW
  have hf : ∀ e : Fin k → Bool,
      0 < Eb (section16VertexDirections e).card gamma (globalBudgetW t1 k)
          (coverPrecW t1 k) / 16 ^ (k + 1 - (section16VertexDirections e).card) ∧
        Eb (section16VertexDirections e).card gamma (globalBudgetW t1 k)
          (coverPrecW t1 k) / 16 ^ (k + 1 - (section16VertexDirections e).card) ≤ 1 := by
    intro e
    obtain ⟨h0, h1⟩ := hEb (section16VertexDirections e).card gamma (globalBudgetW t1 k)
      (coverPrecW t1 k)
    have h16 : (1 : Real) ≤ 16 ^ (k + 1 - (section16VertexDirections e).card) :=
      one_le_pow₀ (by norm_num)
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    linarith
  refine ⟨Finset.prod_pos fun e _ => (hf e).1, ?_⟩
  calc _ ≤ ∏ _e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true), (1 : Real) :=
        Finset.prod_le_prod (fun e _ => (hf e).1.le) fun e _ => (hf e).2
    _ = 1 := by simp

/-- The remainder width is `N^coverExpW`, with no threshold. -/
theorem coverRemWidthW_powerLB (Eb : Nat → Real → Real → Real → Real) (t1 gamma : Real)
    (k : Nat) :
    WidthPowerLB (fun L => coverRemWidthW Eb t1 gamma k L) (coverExpW Eb t1 gamma k) 1 :=
  fun _ _ => Nat.le_ceil _

section Fixed

variable {alpha : Real}

theorem fejer_alpha_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < fejerThetaOne alpha (alpha / 2) k / 4 ∧ fejerThetaOne alpha (alpha / 2) k / 4 ≤ 1 / 36 :=
  fejerThetaOne_bounds k ha (by linarith) (half_pos ha) (by linarith)

/-- The base slice density at the Fejér budget (`GenParams.baseC` with
`globalBudgetW` in place of `globalBudget`). -/
def baseCF (V : Real) (D k : Nat) (alpha : Real) : Real → Real :=
  fun s => s / 2 / uCount V D (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k) (s / 2)

end Fixed

end LeanProofs.GowersSzemeredi
