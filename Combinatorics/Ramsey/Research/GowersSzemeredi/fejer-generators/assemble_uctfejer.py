"""Proofs16UniformCoverTwoFejer: the dimension-two uniform class under the Fejér θ₁ and the tight radius."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(path):
    return (GS / path).read_text(encoding='utf-8')


def between(s, start, end_marker):
    i = s.index(start)
    j = s.index(end_marker, i + len(start))
    return s[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


T1 = 'fejerThetaOne theta gamma 1'
WORDS = [('PolyPieceTwo', 'PolyPieceTwoFejer'), ('polyPieceTwoGraphs', 'polyPieceTwoFejerGraphs'),
         ('uniTwoExp_pos', 'uniTwoFejerExp_pos'), ('uniTwoCount_le_power', 'uniTwoFejerCount_le_power'),
         ('uniTwoExp_inv_le_power', 'uniTwoFejerExp_inv_le_power'),
         ('uniTwoCount', 'uniTwoFejerCount'), ('uniTwoExp', 'uniTwoFejerExp'),
         ('section16_poly_piece_decomposition_two', 'section16_poly_piece_decomposition_two_fejer'),
         ('section16_poly_piece_two_family_cover', 'section16_poly_piece_two_family_cover_fejer'),
         ('section16_uniform_cover_two', 'section16_uniform_cover_two_fejer'),
         ('section16_poly_piece_two_of_subrelation', 'section16_poly_piece_two_of_subrelation_fejer'),
         ('polyTwoThreshold_le_power', 'polyTwoFejerThreshold_le_power'),
         ('polyTwoPieces_le_power', 'polyTwoFejerPieces_le_power'),
         ('polyPieceFaceCount_le_power', 'polyPieceFaceCountW_fejer_le_power'),
         ('polyPieceSpecCount_le_power', 'polyPieceSpecCountW_fejer_le_power'),
         ('polyTwoThreshold', 'polyTwoFejerThreshold'), ('polyTwoPieces', 'polyTwoFejerPieces'),
         ('nPieces_le_base', 'nPieces_le_base_fejer'), ('powerUniformClass_two', 'powerUniformClass_two_fejer')]


def common(t):
    t = t.replace('polyPieceBudget theta gamma', f'polyPieceBudgetW ({T1})')
    t = t.replace('polyPieceFaceCount theta gamma', f'polyPieceFaceCountW ({T1}) gamma')
    t = t.replace('polyPieceSpecCount theta gamma', f'polyPieceSpecCountW ({T1})')
    t = t.replace('section16Zeta theta gamma 1', f'tightZeta ({T1} / 4)')
    for a, b in WORDS:
        t = re.sub(r'\b' + a + r'\b', b, t)
    return t


THETA_BOUNDS = ('''  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 1 ht ht1 hg hg1
  have hθ'pos : 0 < polyPieceBudget theta gamma := by
    unfold polyPieceBudget; positivity
''', '''  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
  have hθ'pos : 0 < polyPieceBudget theta gamma := by
    unfold polyPieceBudgetW; linarith
''')
ZETA_HALF = ('  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1\n',
             '  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1\n'
             '  obtain ⟨hz, hzHalf⟩ := tightZeta_pos_le_half hfa0 (by linarith)\n')

# 1. the uniform cover
uc = between(text('Proofs16UniformCoverTwo.lean'), '/-- The class of dimension-two pieces at parameters `(θ, γ)`. -/',
             'end LeanProofs.GowersSzemeredi')
uc = sub(uc, [THETA_BOUNDS, ZETA_HALF, ('    rw [hmdef, polyTwoPieces]\n', '    rw [hmdef, polyTwoFejerPieces]\n')])
uc = common(uc)

# 2. the bounds
bd = text('Proofs16UniformCoverTwoBounds.lean')
bd = between(bd, 'theorem uniTwoExp_pos', 'end LeanProofs.GowersSzemeredi')
bd = sub(bd, [('  obtain ⟨hζ0, hζ1, hζi⟩ := section16Zeta_one_bounds hg ht\n',
               '  obtain ⟨hζ0, hζ1, hζi⟩ := tightZeta_fejer_one_bounds hg hg1 ht ht1\n')])
bd = common(bd)
for a, b in [('84', '38'), ('89', '43'), ('90', '44'), ('128', '40'), ('130', '46')]:
    bd = bd.replace(f'(2 : Nat) ^ {a}', f'(2 : Nat) ^ {b}')

# 3. nPieces_le_base and powerUniformClass_two
pu = text('Proofs16PowerUniformClass.lean')
np_ = between(pu, 'theorem nPieces_le_base', 'theorem powerUniformClass_two')
np_ = common(np_)
np_ = np_.replace('(2 : Nat) ^ 84', '(2 : Nat) ^ 38').replace('(2 : Nat) ^ 70', '(2 : Nat) ^ 24')
pw = between(pu, 'theorem powerUniformClass_two', 'end LeanProofs.GowersSzemeredi')
pw = common(pw)
pw = sub(pw, [('((2 : Nat) ^ 89) ((2 : Nat) ^ 130) ((2 : Nat) ^ 45)', '((2 : Nat) ^ 43) ((2 : Nat) ^ 46) ((2 : Nat) ^ 15)')])

body = uc + '\n' + bd + '\n' + np_ + '\n' + pw
bad = [l for l in body.split('\n') if re.search(
    r'section16ThetaOne|section16Zeta\b|polyPieceBudget theta|\bpolyPieceFaceCount\b|\bpolyPieceSpecCount\b|'
    r'\^ 13[02]\b|\^ 8[49]\b|\^ 45\b|\^ 70\b|\^ 128\b|lemma156|section16ThetaTwo_pos_le 1', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs18FejerSeedExponents
import GowersSzemeredi.Proofs16UniformCoverTwoBounds
import GowersSzemeredi.Proofs16SplitUniformClass

/-! **The dimension-two uniform class under the Fejér θ₁ and the tight
radius: the split-class seed** (Notes L.16d).

The Fejér analogues of `Proofs16UniformCoverTwo`,
`Proofs16UniformCoverTwoBounds` and the dimension-two part of
`Proofs16PowerUniformClass`, generated from them by a script with a guard
that no printed quantity survives:
* `PolyPieceTwoFejer N θ γ`: the dimension-two pieces at the tight radius
  with the Fejér counts;
* `section16_poly_piece_decomposition_two_fejer` and
  `section16_uniform_cover_two_fejer`;
* `uniTwoFejerCount_le_power` (`≤ w^(2^43)`, printed `2^89`) and
  `uniTwoFejerExp_inv_le_power` (`≤ w^(2^46)`, printed `2^130`);
* `powerUniformClass_two_fejer : PowerUniformClass 2 V (2^43) (2^46) (2^15)`
  (printed `(2^89, 2^130, 2^45)`);
* `splitUniformClass_two_fejer`: a split class at `a = D = 2^46`, the seed
  of the split-class recursion. This is inside the `2^48` of
  `split_pair_with_bounds_fourteen`, against the printed `2^132`. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

'''
TAIL = '''
/-- **The dimension-two split class under the Fejér θ₁**, at any
`d ≥ 2^46`. -/
theorem splitUniformClass_two_fejer {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) {d : Nat}
    (hd : (2 : Nat) ^ 46 ≤ d) :
    Nonempty (SplitUniformClass 2 V d d) := by
  obtain ⟨C⟩ := powerUniformClass_two_fejer hK1 hp1 hlemma6 hV hKV hpV
  have h43 : (2 : Nat) ^ 43 ≤ d := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hd
  have h15 : (2 : Nat) ^ 15 ≤ d := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hd
  exact ⟨(C.weaken hV le_rfl h43 hd h15).toSplit⟩

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs16UniformCoverTwoFejer.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
