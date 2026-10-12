"""Proofs16PolyCoverTwoFejer: PolyCoverAt 2 with the Fejér θ₁ and the tight radius."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
src = (GS / 'Proofs16PolyCoverTwo.lean').read_text(encoding='utf-8')
i = src.index('/-! ### Parameters -/')
j = src.rindex('end LeanProofs.GowersSzemeredi')
body = src[i:j]
# drop the shared helper, which stays in the printed module
k0 = body.index('theorem two_rpow_neg_44')
k1 = body.index('/-! ### The extraction step and the large-modulus cover -/')
body = body[:k0] + body[k1:]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


T1 = 'fejerThetaOne theta gamma 1'
body = sub(body, [
    ('lemma156ExplicitThreshold 1 (theta / 2) gamma', 'fejerProductThreshold 1 (theta / 2) gamma'),
    ('/-- Lemma 15.6\'s modulus threshold at `β = θ/2`, and at least `3`. -/',
     '/-- The Fejér Lemma 15.6\'s modulus threshold at `β = θ/2`, and at least `3`. -/'),
    # the extraction step
    ('''  -- Lemma 15.6 at β = θ/2
''', '''  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  -- the Fejér Lemma 15.6 at β = θ/2
'''),
    ('  obtain ⟨B\', hB\'sub, harr1, harr2⟩ := lemma_15_6_of_density_lower_explicit 1 (theta / 2) gamma\n',
     '  obtain ⟨B\', hB\'sub, harr1, harr2⟩ := fejer_product_of_density_lower_explicit 1 (theta / 2) gamma\n'),
    ('''  have hθ1 : section16ThetaOne theta gamma 1 = (theta / 2 * gamma / 2) ^ (2 ^ (2 ^ (1 + 5))) := by
    unfold section16ThetaOne
    congr 1
    ring
''', '''  have hθ1 : fejerThetaOne theta gamma 1 = (theta / 2 * gamma / 2) ^ fejerProductExponent 1 := by
    unfold fejerThetaOne
    congr 1
    ring
'''),
    ('  have hBarr : section16ThetaOne theta gamma 1 * (N : Real) ^ (17 * 1 + 15) ≤\n',
     '  have hBarr : fejerThetaOne theta gamma 1 * (N : Real) ^ (17 * 1 + 15) ≤\n'),
    ('''  exact section16_poly_piece_two_data ht ht1 hg hg1 Delta B' phi hgraph hBarr
    (hprodB.mono hB'sub)''', '''  exact section16_poly_piece_two_data_with hfa0 hfaS (tightZeta_condition hfa0)
    (tightZeta_pos_le_half hfa0 (by linarith)).1 hg hg1 Delta B' phi hgraph hBarr
    (hprodB.mono hB'sub)'''),
    # the large-modulus cover
    ('''  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 1 ht ht1 hg hg1
  have hθ'pos : 0 < polyPieceBudget theta gamma := by
    unfold polyPieceBudget; positivity
''', '''  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
  have hθ'pos : 0 < polyPieceBudgetW (fejerThetaOne theta gamma 1) := by
    unfold polyPieceBudgetW; linarith
'''),
    ('  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1\n',
     '  obtain ⟨hz, hzHalf⟩ := tightZeta_pos_le_half hfa0 (by linarith)\n'),
    ('    rw [hmdef, polyTwoPieces]\n', '    rw [hmdef, polyTwoFejerPieces]\n'),
])
body = body.replace('polyPieceBudget theta gamma', f'polyPieceBudgetW ({T1})')
body = body.replace('polyPieceSpecCount theta gamma', f'polyPieceSpecCountW ({T1})')
body = body.replace('polyPieceFaceCount theta gamma', f'polyPieceFaceCountW ({T1}) gamma')
body = body.replace('section16Zeta theta gamma 1', f'tightZeta ({T1} / 4)')
for a, b in [('polyTwoFamExp_pos', 'polyTwoFejerFamExp_pos'), ('polyTwoThreshold', 'polyTwoFejerThreshold'),
             ('polyTwoPieces', 'polyTwoFejerPieces'), ('polyTwoFamCount', 'polyTwoFejerFamCount'),
             ('polyTwoFamExp', 'polyTwoFejerFamExp'), ('polyTwoQb', 'polyTwoFejerQb'),
             ('polyTwoEb', 'polyTwoFejerEb')]:
    body = re.sub(r'\b' + a + r'\b', b, body)
for a, b in [('section16_poly_piece_two_of_subrelation', 'section16_poly_piece_two_of_subrelation_fejer'),
             ('section16_poly_cover_two_large', 'section16_poly_cover_two_large_fejer'),
             ('polyCoverAt_two_of_family_lemma6', 'polyCoverAt_two_fejer_of_family_lemma6')]:
    body = re.sub(r'\b' + a + r'\b', b, body)
bad = [l for l in body.split('\n') if re.search(r'section16ThetaOne|section16Zeta|lemma156ExplicitThreshold|lemma_15_6_of', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs16PolyCoverTwo
import GowersSzemeredi.Proofs16PolyPieceTwoDataWith

/-! **`PolyCoverAt 2` with the Fejér θ₁ and the tight Bohr radius**
(Notes L.16d).

The dimension-two cover (`polyCoverAt_two_of_family_lemma6`) seeds the
split-class recursion. Here it is built with:
* the Fejér Lemma 15.6 at `k = 1` (`fejer_product_of_density_lower_explicit`)
  in place of the printed one, so the arrangement density is
  `fejerThetaOne θ γ 1 = (θγ/4)^(fejerProductExponent 1)`;
* the tight radius `tightZeta (θ₁′/4)` in place of `section16Zeta θ γ 1`;
* the pieces of `section16_poly_piece_two_data_with`.

Everything else (the greedy peeling, the padding to
`polyTwoFejerPieces = ⌊γ⁻²/(5θ′)⌋`, the simultaneous family cover, and the
coarse cover below the threshold) is the corpus proof, copied by a script.
The family Lemma 16.6 input is the generic `AbstractFamilyLemma166At 1`,
unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The Fejér arrangement density at dimension one lies in `(0, 1/36]` after
division by `4`. -/
theorem fejerThetaOne_one_bounds {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < fejerThetaOne theta gamma 1 / 4 ∧ fejerThetaOne theta gamma 1 / 4 ≤ 1 / 36 := by
  have hp : 0 < theta * gamma / 4 := by positivity
  have hp1 : theta * gamma / 4 ≤ 1 / 4 := by nlinarith
  have hE : 2 ≤ fejerProductExponent 1 := by
    unfold fejerProductExponent fejerSelectionExponent; norm_num
  refine ⟨by unfold fejerThetaOne; positivity, ?_⟩
  have h : fejerThetaOne theta gamma 1 ≤ (1 / 4 : Real) ^ 2 := by
    unfold fejerThetaOne
    calc (theta * gamma / 4) ^ fejerProductExponent 1
        ≤ (1 / 4 : Real) ^ fejerProductExponent 1 := pow_le_pow_left₀ hp.le hp1 _
      _ ≤ (1 / 4 : Real) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hE
  norm_num at h ⊢
  linarith

/-- The tight radius is positive and at most `1/2`. -/
theorem tightZeta_pos_le_half {a : Real} (ha : 0 < a) (ha1 : a ≤ 1) :
    0 < tightZeta a ∧ tightZeta a ≤ 1 / 2 := by
  unfold tightZeta
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  have hs : 1 ≤ tightRadiusExponent a := by
    unfold tightRadiusExponent
    rw [le_div_iff₀ (pow_pos ha 11)]
    have h1 : a ^ 11 ≤ 1 := pow_le_one₀ ha.le ha1
    have h2 : (1 : Real) ≤ 2 ^ (83 : Nat) := one_le_pow₀ (by norm_num)
    nlinarith
  calc (2 : Real) ^ (-tightRadiusExponent a) ≤ (2 : Real) ^ (-(1 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

'''
out = HEADER + body + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs16PolyCoverTwoFejer.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
