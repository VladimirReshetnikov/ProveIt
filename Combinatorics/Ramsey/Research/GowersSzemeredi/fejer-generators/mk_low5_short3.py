"""Proofs18CoverFejerLowDegrees5 (Theorem 18.1 at d+5, d <= 3) and
Proofs18CoverFejerShortLengths3 (Theorem 18.2 at L+3, L <= 5) (Notes L.16k)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
low = (GS / 'Proofs18CoverFejerLowDegrees.lean').read_text(encoding='utf8')
sh = (GS / 'Proofs18CoverFejerShortLengths.lean').read_text(encoding='utf8')

i = low.index('theorem theorem_18_1_d6_degree_zero')
j = low.rindex('end LeanProofs.GowersSzemeredi')
body = low[i:j]
body = body.replace('Theorem181AtSharp 6 ', 'Theorem181AtSharp 5 ')
body = body.replace('section18ExponentAt 6 ', 'section18ExponentAt 5 ')
body = re.sub(r'\((\d) \+ 6\)', r'(\1 + 5)', body)
body = body.replace('theorem_18_1_d6_', 'theorem_18_1_d5_').replace('section18ExponentAt6_', 'section18ExponentAt5_')
body = body.replace('`α^(2^(2^9))`', '`α^(2^(2^8))`')
bad = [l for l in body.split('\n') if re.search(r'\bd6\b|_d6_|At 6\b|At6_|\+ 6\)', l)]
assert not bad, bad
head = '''import GowersSzemeredi.Proofs18CoverFejerLowDegrees

/-! **Theorem 18.1 with exponent `α^(2^(2^(d+5)))` at degrees `0, …, 3`**
(Notes L.16k).

`Proofs18CoverFejerLowDegrees` with `6` replaced by `5` (generated). The
corpus exponents at degrees `0, 1, 2` are fixed powers of `α` (at most
`α^49462 ≥ α^(2^16)`, and `16 ≤ 2^(2+5)`). Degree three comes from the
polynomial base envelope `PolyEnvBound 3 74`, since `74 + 1 ≤ 2^(3+5)`.
With `Proofs18CoverFejerHeadlineT` this gives Theorem 18.1 at `d + 5` in
every degree. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

'''
(GS / 'Proofs18CoverFejerLowDegrees5.lean').write_text(head + body + 'end LeanProofs.GowersSzemeredi\n',
                                                      encoding='utf8', newline='\n')


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:80])
        t = t.replace(a, b)
    return t


i = sh.index('theorem roth_threshold_le_szemerediThresholdAt_four')
j = sh.rindex('end LeanProofs.GowersSzemeredi')
body = sh[i:j]
body = sub(body, [
    ('(2 : Real) ^ (4 : Nat) ≤ (2 : Real) ^ (k + 4 : Nat)', '(2 : Real) ^ (3 : Nat) ≤ (2 : Real) ^ (k + 3 : Nat)'),
    ('(k + 4 : Nat)', '(k + 3 : Nat)'),
    ('have h64 : (6 : Real) ≤ (2 : Real) ^ (4 : Nat) := by norm_num',
     'have h64 : (6 : Real) ≤ (2 : Real) ^ (3 : Nat) := by norm_num'),
    ('rw [show (2 : Real) ^ (4 + 4 : Nat) = 256 by norm_num]', 'rw [show (2 : Real) ^ (4 + 3 : Nat) = 128 by norm_num]'),
    ('(delta⁻¹ ^ ((2 : Nat) ^ 256))', '(delta⁻¹ ^ ((2 : Nat) ^ 128))'),
    ('(by norm_num : 21 ≤ 256)', '(by norm_num : 21 ≤ 128)'),
    ('rw [show (2 : Real) ^ (5 + 4 : Nat) = 512 by norm_num]', 'rw [show (2 : Real) ^ (5 + 3 : Nat) = 256 by norm_num]'),
    ('(delta⁻¹ ^ ((2 : Nat) ^ 512))', '(delta⁻¹ ^ ((2 : Nat) ^ 256))'),
    ('(by norm_num : 73 ≤ 512)', '(by norm_num : 73 ≤ 256)'),
])
body = body.replace('szemerediThresholdAt 4 ', 'szemerediThresholdAt 3 ')
body = body.replace('Theorem182AtSharp 4 ', 'Theorem182AtSharp 3 ').replace('Corollary187AtSharp 4 ', 'Corollary187AtSharp 3 ')
for a, b in [('roth_threshold_le_szemerediThresholdAt_four', 'roth_threshold_le_szemerediThresholdAt_three'),
             ('quadraticIntervalClosedThreshold_le_at_four', 'quadraticIntervalClosedThreshold_le_at_three'),
             ('fejerFiveTermThreshold_le_at_four', 'fejerFiveTermThreshold_le_at_three'),
             ('theorem_18_2_L4_le_five', 'theorem_18_2_L3_le_five'),
             ('corollary_18_7_L4_le_five', 'corollary_18_7_L3_le_five')]:
    body = re.sub(r'\b' + a + r'\b', b, body)
body = body.replace('with `L + 4` at every length', 'with `L + 3` at every length')
bad = [l for l in body.split('\n') if re.search(r'At 4\b|_L4_|_at_four\b|Sharp 4\b|\b512\b', l)]
assert not bad, bad
head = '''import GowersSzemeredi.Proofs18CoverFejerShortLengths

/-! **Theorem 18.2 and Corollary 18.7 with `L + 3` at lengths `L ≤ 5`**
(Notes L.16k).

`Proofs18CoverFejerShortLengths` with `4` replaced by `3` (generated). The
corpus's explicit thresholds (Roth's `exp(exp(10¹²·δ⁻¹))` for `L ≤ 3`;
towers with `2^21` and `2^73` on top for `L = 4, 5`) stay below the
threshold with `L + 3` on top: `2^(4+3) = 128 ≥ 21` and `2^(5+3) = 256 ≥ 73`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

'''
(GS / 'Proofs18CoverFejerShortLengths3.lean').write_text(head + body + 'end LeanProofs.GowersSzemeredi\n',
                                                        encoding='utf8', newline='\n')
print('ok')
