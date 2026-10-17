import GowersSzemeredi.Proofs16UniformCoverTwo
import GowersSzemeredi.Proofs18LengthSixExponents
import GowersSzemeredi.Proofs18LengthSixCountsSide
import GowersSzemeredi.Proofs18LengthSixExponentsSide

/-! Envelope controls for the uniform cover in dimension two (Notes L.5, D1).

The controls of `section16_uniform_cover_two` at `M` pieces are polynomial in
any base `w` with `2/(γθ) ≤ w`, `ρ⁻¹ ≤ w` and `M ≤ w^(2^84)`:
* `uniTwoCount_le_power : uniTwoCount θ γ M ρ ≤ w^(2^89)`;
* `uniTwoExp_inv_le_power : (uniTwoExp A Bq θ γ M ρ)⁻¹ ≤ w^(2^130)`, for
  `A = familyWidthPrefactor K₁` and `Bq = familyWidthDivisor 1 p₁` with
  `K₁, p₁ ≤ w³`;
* `uniTwoExp_pos`.

These are `polyTwoFamCount_le_power` and `polyTwoFamExp_inv_le_power` with the
piece count `polyTwoPieces γ θ` replaced by an arbitrary `M`, and the base
`2/(γθρ)` by an arbitrary `w`. A free base lets the family size and the
recurrence constants be absorbed into `w`, which gives envelopes monotone in
the family size. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem uniTwoExp_pos {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q)
    {theta gamma : Real} (M : Nat) {rho : Real} (hrho : 0 < rho) :
    0 < uniTwoExp A Bq theta gamma M rho := by
  unfold uniTwoExp
  exact famTwoCappedExponent_pos hB hrho

theorem uniTwoCount_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    {w : Real} (hvw : 2 / (gamma * theta) ≤ w) (hrw : rho⁻¹ ≤ w)
    {M : Nat} (hM : (M : Real) ≤ w ^ ((2 : Nat) ^ 84)) :
    uniTwoCount theta gamma M rho ≤ w ^ ((2 : Nat) ^ 89) := by
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := polyPieceFaceCount_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  clear_value v
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  -- both counts below `w^(2^84)`
  have hq' : (polyPieceFaceCount theta gamma : Real) ≤ w ^ ((2 : Nat) ^ 84) :=
    hq.trans (pow_le_pow_left₀ hv0 hvw _)
  unfold uniTwoCount
  exact le_pow_mono hw2 (by norm_num) (famTwoCount_le_power hw2 hr hrw hM hq')

theorem uniTwoExp_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    {w : Real} (hvw : 2 / (gamma * theta) ≤ w) (hrw : rho⁻¹ ≤ w)
    {M : Nat} (hM : (M : Real) ≤ w ^ ((2 : Nat) ^ 84))
    (hK : (K1 : Real) ≤ w ^ 3)
    (hp : (p1 : Real) ≤ w ^ 3) :
    (uniTwoExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) theta gamma M rho)⁻¹ ≤
      w ^ ((2 : Nat) ^ 130) := by
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hζ0, hζ1, hζi⟩ := section16Zeta_one_bounds hg ht
  have hqs := polyPieceSpecCount_le_power hg hg1 ht ht1
  have hqf := polyPieceFaceCount_le_power hg hg1 ht ht1
  unfold uniTwoExp
  dsimp only
  set ζ := section16Zeta theta gamma 1
  set m := M with hmM
  set qs := polyPieceSpecCount theta gamma
  set qf := polyPieceFaceCount theta gamma
  set v := 2 / (gamma * theta) with hv
  clear_value v ζ m qs qf
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hm' : (m : Real) ≤ w ^ ((2 : Nat) ^ 84) := hM
  have hqs' : (qs : Real) ≤ w ^ ((2 : Nat) ^ 84) := hqs.trans (pow_le_pow_left₀ hv0 hvw _)
  have hqf' : (qf : Real) ≤ w ^ ((2 : Nat) ^ 84) := hqf.trans (pow_le_pow_left₀ hv0 hvw _)
  have hζw : ζ⁻¹ ≤ Real.exp (w ^ ((2 : Nat) ^ 128)) :=
    hζi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hv0 hvw _))
  have h := famTwoWidth_inv_le_power hK1 hp1 hw2 hr hr1 hrw hm' hqs' hqf' hK hp hζ0 hζ1 hζw
  exact h.trans (pow_le_pow_right₀ hw1 (by norm_num))

end LeanProofs.GowersSzemeredi
