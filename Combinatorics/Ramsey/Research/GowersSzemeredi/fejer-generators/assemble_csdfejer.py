"""Proofs16ClassStepDegreesFejer: the class-step degrees under the Fejér θ₁ and the tight radius."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs16ClassStepDegrees.lean').read_text(encoding='utf-8')


def between(t, start, end_marker):
    i = t.index(start)
    j = t.index(end_marker, i + len(start))
    return t[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


# the degrees, without stepP/stepT
degs = between(s, 'def stepY1', '/-! ### Bases -/')
bases = between(s, 'theorem twoDiv_budget_le', '/-- A level-`k` base, in the base `w` of the next class. -/')
main = between(s, '/-! ### The count -/', '/-! ### Weakening a class -/')
step = between(s, '/-! ### The step -/', 'end LeanProofs.GowersSzemeredi')

bases = sub(bases, [
    ('    (hgi : 2 / g ≤ (2 / (gamma * theta)) ^ (2 ^ (2 ^ (k + 5) + 5) + 1)) :',
     '    (hgi : 2 / g ≤ (2 / (gamma * theta)) ^ (32 * fejerProductExponent k + 1)) :'),
    ('      ≤ u ^ (2 ^ (2 ^ (k + 5) + 5) + 1) * u ^ (2 ^ (2 ^ (k + 5) + 5)) :=',
     '      ≤ u ^ (32 * fejerProductExponent k + 1) * u ^ (32 * fejerProductExponent k) :='),
    ('    _ = u ^ (2 ^ (2 ^ (k + 5) + 5) + 1 + 2 ^ (2 ^ (k + 5) + 5)) := by rw [← pow_add]',
     '    _ = u ^ (32 * fejerProductExponent k + 1 + 32 * fejerProductExponent k) := by rw [← pow_add]'),
    ('''        congr 1
        unfold stepP
        rw [show 2 ^ (k + 5) + 6 = (2 ^ (k + 5) + 5) + 1 by omega, pow_succ]
        ring
''', '''        congr 1
        unfold fejerStepP
        ring
'''),
])
main = sub(main, [
    ('''    unfold stepZDeg stepT
    have : 1 ≤ 2 ^ (2 ^ (k + 6)) := Nat.one_le_two_pow
    omega
''', '''    unfold stepZDeg stepT
    omega
'''),
    ('''    unfold stepThrDeg
    rw [← stepP]
    omega
''', '''    unfold stepThrDeg
    omega
'''),
    ('  unfold classStepThreshold classPieceThreshold\n', '  unfold classStepThresholdFejer classPieceThresholdW\n'),
])

T1 = 'fejerThetaOne theta gamma k'
B = '(fejerThetaOne_bounds k ht ht1 hg hg1)'
body = degs + '/-! ### Bases -/\n\n' + bases + main + step
body = body.replace('classBudget_pos_le k ht ht1 hg hg1', f'classBudgetW_pos_le k {B}.1 {B}.2')
body = body.replace('section16_theta_delta_bounds k ht ht1 hg hg1', f'section16_theta_delta_bounds_with {B}.1 {B}.2')
body = body.replace('classBudget_inv_le k hg hg1 ht ht1', 'classBudgetW_fejer_inv_le k hg hg1 ht ht1')
body = body.replace('classDelta_inv_le k hg hg1 ht ht1', 'classDeltaW_fejer_inv_le k hg hg1 ht ht1')
body = body.replace('section16Zeta_inv_le_gen k hg ht', 'tightZeta_fejer_inv_le_gen k hg hg1 ht ht1')
body = body.replace('lemma156ExplicitThreshold_le_gen', 'fejerProductThreshold_le_gen')
body = body.replace('classPieces_le_stepP', 'classPiecesFejer_le_gen')
body = body.replace('stepP_ge k', 'fejerStepP_ge k')
body = body.replace('classBudget theta gamma k', f'classBudgetW ({T1}) k')
body = body.replace('classDelta theta gamma k', f'section16Delta ({T1})')
body = body.replace('section16Zeta theta gamma k', f'tightZeta ({T1} / 4)')
body = body.replace('classStepThreshold V D theta gamma k', 'classStepThresholdFejer V D theta gamma k')
for a, b in [('stepP', 'fejerStepP'), ('stepT', 'fejerStepT'), ('classPieces', 'classPiecesFejer'),
             ('StepPiece', 'StepPieceFejer'), ('stepPieceGraphs', 'stepPieceFejerGraphs'),
             ('class_step_decomp', 'class_step_decomp_fejer'), ('class_step_cover', 'class_step_cover_fejer'),
             ('twoDiv_budget_le', 'twoDiv_budget_le_fejer'), ('twoDiv_delta_le', 'twoDiv_delta_le_fejer'),
             ('twoDiv_gamma_le', 'twoDiv_gamma_le_fejer'), ('step_count_le', 'step_count_le_fejer'),
             ('step_exp_inv_le', 'step_exp_inv_le_fejer'), ('step_thr_le', 'step_thr_le_fejer'),
             ('powerUniformClass_succ', 'powerUniformClass_succ_fejer')]:
    body = re.sub(r'\b' + a + r'\b', b, body)
body = re.sub(r'\bstep(Y1|QrDeg|SDeg|PbDeg|EbDeg|ErDeg|BqDeg|LDeg|ZDeg|CountDeg|ExpDeg|ThrDeg)\b',
              r'fejerStep\1', body)
bad = [l for l in body.split('\n') if re.search(
    r'classBudget\b|classBudget_|classDelta\b|classDelta_|section16Zeta|section16ThetaOne|\bstepP\b|\bstepT\b|'
    r'2 \^ \(2 \^|lemma156|\bclassStepThreshold\b|\bclassPieceThreshold\b|section16_theta_delta_bounds k|'
    r'\bclassPieces\b|\bStepPiece\b|\bstepPieceGraphs\b|'
    r'\bstep(Y1|QrDeg|SDeg|PbDeg|EbDeg|ErDeg|BqDeg|LDeg|ZDeg|CountDeg|ExpDeg|ThrDeg)\b', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs16ClassStepDegrees
import GowersSzemeredi.Proofs16ClassStepBoundsFejer

/-! **The class-step degrees under the Fejér θ₁ and the tight radius**
(Notes L.16d).

The Fejér instance of `Proofs16ClassStepDegrees`, generated from it by a
script with a guard that no printed parameter survives. Given a uniform class
of dimension `k ≥ 1` at one degree `D`, and the family Lemma 16.6 at
dimension `k` with constants `K, p ≤ V′`, the relations covered by Fejér step
pieces (`StepPieceFejer`) form a uniform class of dimension `k+1` at base
`V′`, with degrees
* `fejerStepCountDeg k D`, `fejerStepExpDeg k D`, `fejerStepThrDeg k D`.

These are the corpus's degrees with `P = fejerStepP k = 64·F` in place of
`stepP k = 2^(2^(k+5)+6)` and `T = fejerStepT k = 22·F + 105` in place of
`stepT k = 2^(2^(k+6))`, where `F = fejerProductExponent k ≤ 2^(5k+14)`.
So every degree is `D · 2^(O(k))` rather than `D · 2^(2^(O(k)))`.

The six inputs are `Proofs16ClassStepBoundsFejer`. The generic lemmas
(`level_base_le`, `step_w_facts`, `inv_scale_le`, `classVertexNum_succ_le`,
`PowerUniformClass.weaken`) are reused from `Proofs16ClassStepDegrees`.

* `powerUniformClass_succ_fejer`: **the Fejér step of route (II)**. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The degrees -/

'''
out = HEADER + body + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs16ClassStepDegreesFejer.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
