"""Proofs18SinglePieceCoverInverseFejer: the joint-cover inverse step under the Fejér θ₁ and the tight radius."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs18SinglePieceCoverInverse.lean').read_text(encoding='utf-8')
i = s.index('/-- The final density. -/')
j = s.rindex('end LeanProofs.GowersSzemeredi')
body = s[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


body = sub(body, [
    ('''  obtain ⟨hL4, hm1, hm, hpar⟩ := hscale
  exact single_piece_lift_global_cover hk ht ht1 hg hg1 hcov hQb hEb hEb1 eps thr hretile
    B phi hB hprodB hL4 m hm1 hm hpar
''', '''  obtain ⟨hL4, hm1, hm, hpar⟩ := hscale
  obtain ⟨ha0, haS⟩ := fejerThetaOne_bounds k ht ht1 hg hg1
  obtain ⟨hz0, hz2⟩ := tightZeta_pos_le_half ha0 (by linarith)
  exact single_piece_lift_global_cover_with hk ha0 haS (tightZeta_condition ha0) hz0 hz2 hg hg1
    hcov hQb hEb hEb1 eps thr hretile B phi hB hprodB hL4 m hm1 hm hpar
'''),
    ('''  obtain ⟨B', hB'B, harr1, harr2⟩ := lemma_15_6_of_density_lower_all_explicit k (alpha / 2)
    (alpha / 2) hg hg1 hg hg1 N hN (Fact.out : N.Prime) hodd B phi hBmass hprod
  have hθ1 : section16ThetaOne alpha (alpha / 2) k =
      (alpha / 2 * (alpha / 2) / 2) ^ (2 ^ (2 ^ (k + 5))) := by
    unfold section16ThetaOne
    congr 1
    ring
''', '''  obtain ⟨B', hB'B, harr1, harr2⟩ := fejer_product_of_density_lower_explicit k (alpha / 2)
    (alpha / 2) hk hg hg1 hg hg1 N hN (Fact.out : N.Prime) hodd B phi hBmass hprod
  have hθ1 := fejerThetaOne_half_eq alpha (alpha / 2) k
'''),
])
body = body.replace('''  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) k ha ha1 (by positivity)
    (by linarith)
''', '''  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_bounds k ha ha1 (show (0 : Real) < alpha / 2 by positivity)
    (show alpha / 2 ≤ 1 by linarith)
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
''')
body = body.replace('''coverRho1_pos_le Qb hQb alpha (alpha / 2) k ha ha1 (by positivity)
    (by linarith)''', 'coverRho1W_pos_le Qb hQb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k hfa0 hfaS')
body = body.replace('unfold globalTheta2;', 'unfold globalTheta2W;')
body = body.replace("single_piece_lift_global_cover'", 'single_piece_lift_global_cover_fejer')
body = body.replace('lemma156ExplicitThreshold', 'fejerProductThreshold')
for X, Y in [('theta', 'gamma'), ('alpha', '(alpha / 2)')]:
    T = f'fejerThetaOne {X} {Y} k'
    body = body.replace(f'globalBudget {X} {Y} k', f'globalBudgetW ({T}) k')
    body = body.replace(f'globalTheta2 {X} {Y} k', f'globalTheta2W ({T})')
    body = body.replace(f'coverRho1 Qb {X} {Y} k', f'coverRho1W Qb ({T}) {Y} k')
    body = body.replace(f'coverRemWidth Eb {X} {Y} k N', f'coverRemWidthW Eb ({T}) {Y} k N')
    body = body.replace(f'section16Zeta {X} {Y} k', f'tightZeta ({T} / 4)')
    body = body.replace(f'section16ThetaOne {X} {Y} k', T)
for a, b in [('singlePieceGlobalDensityC_pos', 'singlePieceGlobalDensityF_pos'),
             ('singlePieceGlobalDensityC_le_one', 'singlePieceGlobalDensityF_le_one'),
             ('singlePieceEtaC_pos', 'singlePieceEtaF_pos'),
             ('singlePieceGlobalDensityC', 'singlePieceGlobalDensityF'),
             ('singlePieceGlobalQmaxC', 'singlePieceGlobalQmaxF'),
             ('singlePieceGlobalWidthC', 'singlePieceGlobalWidthF'),
             ('SinglePieceGlobalScaleC', 'SinglePieceGlobalScaleF'),
             ('singlePieceEtaC', 'singlePieceEtaF'),
             ('SinglePieceModulusConditionsC', 'SinglePieceModulusConditionsF'),
             ('singlePieceGlobalC', 'singlePieceGlobalF'),
             ('single_piece_frequency_box_global_cover', 'single_piece_frequency_box_global_cover_fejer'),
             ('single_piece_localization_global_cover', 'single_piece_localization_global_cover_fejer'),
             ('single_piece_inverse_step_global_cover', 'single_piece_inverse_step_global_cover_fejer')]:
    body = re.sub(r'\b' + a + r'\b', b, body)
bad = [l for l in body.split('\n') if re.search(
    r'section16ThetaOne|section16Zeta|lemma156|lemma_15_6|\bglobalBudget\b|\bglobalTheta2\b|\bcoverRho1\b|'
    r'\bcoverRemWidth\b|singlePiece\w*C\b|SinglePiece\w*C\b|section16ThetaTwo_pos_le\b|coverRho1_pos_le|'
    r'2 \^ \(2 \^', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs18SinglePieceCoverInverse
import GowersSzemeredi.Proofs16SinglePieceCoverGlobalWith
import GowersSzemeredi.Proofs16ClassStepFejer

/-! **The joint-cover inverse step under the Fejér θ₁ and the tight radius**
(Notes L.16d).

The Fejér instance of `Proofs18SinglePieceCoverInverse`, generated from it
by a script with a guard that no printed parameter survives:
* the frequency box comes from the explicit Fejér Lemma 15.6
  (`fejer_product_of_density_lower_explicit`), so the arrangement density is
  `fejerThetaOne α (α/2) k` and the modulus threshold is
  `fejerProductThreshold k (α/2) (α/2)`;
* the lift is `single_piece_lift_global_cover_with` at that density and the
  tight radius `tightZeta (θ₁′/4)`;
* the definitions `singlePieceGlobalF`, `singlePieceGlobalDensityF`,
  `singlePieceGlobalQmaxF`, `singlePieceGlobalWidthF`,
  `SinglePieceGlobalScaleF`, `singlePieceEtaF` and
  `SinglePieceModulusConditionsF` are the corpus's `…C` with `globalBudgetW`,
  `coverRho1W`, `coverRemWidthW` at the Fejér density.

`single_piece_inverse_step_global_cover_fejer` is the inverse step the
Section 18 envelope consumes. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The slice control of the single-piece lift at the Fejér density. -/
def singlePieceGlobalF (Qb : Nat → Real → Real → Real → Real) (theta gamma : Real) (k : Nat) :
    Real → Real :=
  fun s => s / 2 / Qb k gamma (globalBudgetW (fejerThetaOne theta gamma k) k) (s / 2)

'''
out = HEADER + body + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs18SinglePieceCoverInverseFejer.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
