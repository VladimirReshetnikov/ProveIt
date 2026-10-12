"""Proofs18FejerSeedExponents: the dimension-two count and exponent bounds under the Fejér θ₁."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def block(path, start, end_marker):
    s = (GS / path).read_text(encoding='utf-8')
    i = s.index(start)
    j = s.index(end_marker, i + len(start))
    return s[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


T1 = 'fejerThetaOne theta gamma 1'
NAMES = [('polyTwoFamExp_pos', 'polyTwoFejerFamExp_pos'),
         ('polyTwoThreshold_le_power', 'polyTwoFejerThreshold_le_power'),
         ('polyTwoPieces_le_power', 'polyTwoFejerPieces_le_power'),
         ('polyPieceFaceCount_le_power', 'polyPieceFaceCountW_fejer_le_power'),
         ('polyPieceSpecCount_le_power', 'polyPieceSpecCountW_fejer_le_power'),
         ('polyTwoFamCount_le_power', 'polyTwoFejerFamCount_le_power'),
         ('polyTwoQb_le_power', 'polyTwoFejerQb_le_power'),
         ('polyTwoFamExp_inv_le_power', 'polyTwoFejerFamExp_inv_le_power'),
         ('polyTwoEb_inv_le_power', 'polyTwoFejerEb_inv_le_power'),
         ('polyTwoThreshold', 'polyTwoFejerThreshold'), ('polyTwoPieces', 'polyTwoFejerPieces'),
         ('polyTwoFamCount', 'polyTwoFejerFamCount'), ('polyTwoFamExp', 'polyTwoFejerFamExp'),
         ('polyTwoQb', 'polyTwoFejerQb'), ('polyTwoEb', 'polyTwoFejerEb')]


def common(t):
    t = t.replace('polyPieceFaceCount theta gamma', f'polyPieceFaceCountW ({T1}) gamma')
    t = t.replace('polyPieceSpecCount theta gamma', f'polyPieceSpecCountW ({T1})')
    for a, b in NAMES:
        t = re.sub(r'\b' + a + r'\b', b, t)
    return t


counts = block('Proofs18LengthSixCounts.lean', 'theorem polyTwoFamCount_le_power',
               '/-- **The counts of the length-six route are polynomial**')
counts = common(counts)
counts = sub(counts, [
    ('    polyTwoFejerFamCount theta gamma rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 89) := by',
     '    polyTwoFejerFamCount theta gamma rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 43) := by'),
    ('  -- both counts below `w^(2^84)`', '  -- both counts below `w^(2^38)`'),
    ('/-- `polyTwoFejerQb γ θ ρ ≤ (2/(γθρ))^(2^90)`. -/', '/-- `polyTwoFejerQb γ θ ρ ≤ (2/(γθρ))^(2^44)`. -/'),
    ('    polyTwoFejerQb gamma theta rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 90) := by',
     '    polyTwoFejerQb gamma theta rho ≤ (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 44) := by'),
    ('  have hthr\' : polyTwoFejerThreshold theta gamma ≤ w ^ ((2 : Nat) ^ 45) :=',
     '  have hthr\' : polyTwoFejerThreshold theta gamma ≤ w ^ ((2 : Nat) ^ 15) :='),
])
counts = counts.replace('(2 : Nat) ^ 84', '(2 : Nat) ^ 38')

exps = block('Proofs18LengthSixExponents.lean', '/-- The family-cover exponent of `PolyCoverAt 2` is polynomial:',
             '/-- **The width exponents of the length-six route are polynomial**')
exps = common(exps)
exps = sub(exps, [
    ('`polyTwoFejerFamExp ≥ (2/(γθρ))^(-2^130)`. -/', '`polyTwoFejerFamExp ≥ (2/(γθρ))^(-2^46)`. -/'),
    ('      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 130) := by',
     '      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 46) := by'),
    ('  obtain ⟨hζ0, hζ1, hζi⟩ := section16Zeta_one_bounds hg ht\n',
     '  obtain ⟨hζ0, hζ1, hζi⟩ := tightZeta_fejer_one_bounds hg hg1 ht ht1\n'),
    ('  set ζ := section16Zeta theta gamma 1\n', f'  set ζ := tightZeta ({T1} / 4)\n'),
    ('/-- The width exponent of `PolyCoverAt 2`: `polyTwoFejerEb ≥ (2/(γθρ))^(-2^132)`. -/',
     '/-- The width exponent of `PolyCoverAt 2`: `polyTwoFejerEb ≥ (2/(γθρ))^(-2^46)`. -/'),
    ('      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 132) := by',
     '      (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 46) := by'),
    ('  have hthr\' : polyTwoFejerThreshold theta gamma ≤ Real.exp (w ^ ((2 : Nat) ^ 45)) :=',
     '  have hthr\' : polyTwoFejerThreshold theta gamma ≤ Real.exp (w ^ ((2 : Nat) ^ 15)) :='),
])
exps = exps.replace('(2 : Nat) ^ 84', '(2 : Nat) ^ 38').replace('(2 : Nat) ^ 90', '(2 : Nat) ^ 44')
exps = exps.replace('(2 : Nat) ^ 128', '(2 : Nat) ^ 40')
bad = [l for l in (counts + exps).split('\n')
       if re.search(r'section16ThetaOne|section16Zeta|polyPieceBudget\b|polyPieceFaceCount\b|'
                    r'polyPieceSpecCount\b|lemma156|\^ 13[02]\b|\^ 8[49]\b|\^ 45\b', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs18FejerSeedCounts

/-! **The dimension-two cover's controls under the Fejér θ₁ and the tight
radius** (Notes L.16d).

The Fejér analogue of the length-six count and exponent bounds, in the base
`w = 2/(γθρ)`:
* `polyTwoFejerFamCount_le_power`: `≤ w^(2^43)` (printed `2^89`);
* `polyTwoFejerQb_le_power`: `≤ w^(2^44)` (printed `2^90`);
* `polyTwoFejerFamExp_inv_le_power`: `≤ w^(2^46)` (printed `2^130`);
* `polyTwoFejerEb_inv_le_power`: `≤ w^(2^46)` (printed `2^132`).

The printed width exponent was dominated by the Bohr radius
(`ζ⁻¹ ≤ exp(w^(2^128))`). Under the tight radius
(`tightZeta_fejer_one_bounds`: `ζ′⁻¹ ≤ exp(u^(2^40))`, from
`s′ ≤ u^(22E+105)`) the counts dominate. So the dimension-two seed of the
split-class recursion has degree about `2^46`, inside the `2^48` of
`split_pair_with_bounds_fourteen`.

The proofs are the corpus proofs with the new exponents, copied by a script
with a guard that no printed quantity survives. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The tight radius at the Fejér density: `0 < ζ′ ≤ 1` and
`ζ′⁻¹ ≤ exp(u^(2^40))`, `u = 2/(γθ)`. -/
theorem tightZeta_fejer_one_bounds {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < tightZeta (fejerThetaOne theta gamma 1 / 4) ∧ tightZeta (fejerThetaOne theta gamma 1 / 4) ≤ 1 ∧
      (tightZeta (fejerThetaOne theta gamma 1 / 4))⁻¹ ≤
        Real.exp ((2 / (gamma * theta)) ^ ((2 : Nat) ^ 40)) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨ha0, haS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨hz0, hzh⟩ := tightZeta_pos_le_half ha0 (by linarith)
  refine ⟨hz0, by linarith, ?_⟩
  have hs := fejer_tightRadiusExponent_le 1 ht ht1 hg hg1
  rw [mul_comm theta gamma] at hs
  set s := tightRadiusExponent (fejerThetaOne theta gamma 1 / 4) with hsdef
  set u := 2 / (gamma * theta) with hu
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hs0 : 0 ≤ s := by
    rw [hsdef]; unfold tightRadiusExponent
    exact div_nonneg (by norm_num) (pow_nonneg ha0.le 11)
  have hinv : (tightZeta (fejerThetaOne theta gamma 1 / 4))⁻¹ = (2 : Real) ^ s := by
    unfold tightZeta; rw [← hsdef, Real.rpow_neg (by norm_num), inv_inv]
  rw [hinv]
  have h2e : (2 : Real) ^ s ≤ Real.exp s := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have hl : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num); linarith
    nlinarith
  have hE : 22 * fejerProductExponent 1 + 105 ≤ (2 : Nat) ^ 40 := by
    rw [fejerProductExponent_one]; norm_num
  calc (2 : Real) ^ s ≤ Real.exp s := h2e
    _ ≤ Real.exp (u ^ (22 * fejerProductExponent 1 + 105)) := Real.exp_le_exp.mpr hs
    _ ≤ Real.exp (u ^ ((2 : Nat) ^ 40)) :=
        Real.exp_le_exp.mpr (pow_le_pow_right₀ hu1 hE)

'''
out = HEADER + counts + '\n' + exps + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs18FejerSeedExponents.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
