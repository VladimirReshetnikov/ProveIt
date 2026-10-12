"""Generate Proofs18CoverFejerLowDegrees (Theorem 18.1 at d+6, d ≤ 3) and
Proofs18CoverFejerShortLengths (Theorem 18.2 at L+4, L ≤ 5)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
low = (GS / 'Proofs18CoverSharperLowDegrees.lean').read_text(encoding='utf8')
thr = (GS / 'Proofs18CoverThresholdsSharp.lean').read_text(encoding='utf8')

# ---- low degrees: the c = 7 module with 7 -> 6
i = low.index('theorem theorem_18_1_d7_degree_zero')
j = low.rindex('end LeanProofs.GowersSzemeredi')
body = low[i:j]
body = body.replace('Theorem181AtSharp 7 ', 'Theorem181AtSharp 6 ')
body = body.replace('section18ExponentAt 7 ', 'section18ExponentAt 6 ')
body = re.sub(r'\((\d) \+ 7\)', r'(\1 + 6)', body)
body = body.replace('theorem_18_1_d7_', 'theorem_18_1_d6_').replace('section18ExponentAt7_', 'section18ExponentAt6_')
body = body.replace('`α^(2^(2^10))`', '`α^(2^(2^9))`')
bad = [l for l in body.split('\n') if re.search(r'\bd7\b|_d7_|At 7\b|At7_|\+ 7\)', l)]
assert not bad, bad
head = '''import GowersSzemeredi.Proofs18CoverSharperLowDegrees

/-! **Theorem 18.1 with exponent `α^(2^(2^(d+6)))` at degrees `0, …, 3`**
(Notes L.16d).

`Proofs18CoverSharperLowDegrees` with `7` replaced by `6` (generated). The
corpus exponents at degrees `0, 1, 2` are fixed powers of `α` (at most
`α^49462`), far above `α^(2^(2^(d+6)))`, and degree three comes from the
polynomial base envelope `PolyEnvBound 3 74`, since `74 + 1 ≤ 2^(3+6)`.
With `Proofs18CoverFejerHeadline` this gives Theorem 18.1 at `d + 6` in every
degree. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

'''
(GS / 'Proofs18CoverFejerLowDegrees.lean').write_text(head + body + 'end LeanProofs.GowersSzemeredi\n',
                                                     encoding='utf8', newline='\n')

# ---- short lengths: the c = 5 block of Proofs18CoverThresholdsSharp with 5 -> 4
i = thr.index('theorem roth_threshold_le_szemerediThresholdAt_five')
j = thr.rindex('end LeanProofs.GowersSzemeredi')
body = thr[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:80])
        t = t.replace(a, b)
    return t


body = sub(body, [
    ('(2 : Real) ^ (5 : Nat) ≤ (2 : Real) ^ (k + 5 : Nat)', '(2 : Real) ^ (4 : Nat) ≤ (2 : Real) ^ (k + 4 : Nat)'),
    ('(k + 5 : Nat)', '(k + 4 : Nat)'),
    ('have h64 : (6 : Real) ≤ (2 : Real) ^ (5 : Nat) := by norm_num',
     'have h64 : (6 : Real) ≤ (2 : Real) ^ (4 : Nat) := by norm_num'),
    ('rw [show (2 : Real) ^ (4 + 5 : Nat) = 512 by norm_num]', 'rw [show (2 : Real) ^ (4 + 4 : Nat) = 256 by norm_num]'),
    ('(delta⁻¹ ^ ((2 : Nat) ^ 512))', '(delta⁻¹ ^ ((2 : Nat) ^ 256))'),
    ('(by norm_num : 21 ≤ 512)', '(by norm_num : 21 ≤ 256)'),
    ('rw [show (2 : Real) ^ (5 + 5 : Nat) = 1024 by norm_num]', 'rw [show (2 : Real) ^ (5 + 4 : Nat) = 512 by norm_num]'),
    ('(delta⁻¹ ^ ((2 : Nat) ^ 1024))', '(delta⁻¹ ^ ((2 : Nat) ^ 512))'),
    ('(by norm_num : 73 ≤ 1024)', '(by norm_num : 73 ≤ 512)'),
])
body = body.replace('szemerediThresholdAt 5 ', 'szemerediThresholdAt 4 ')
body = body.replace('Theorem182AtSharp 5 ', 'Theorem182AtSharp 4 ').replace('Corollary187AtSharp 5 ', 'Corollary187AtSharp 4 ')
for a, b in [('roth_threshold_le_szemerediThresholdAt_five', 'roth_threshold_le_szemerediThresholdAt_four'),
             ('quadraticIntervalClosedThreshold_le_at_five', 'quadraticIntervalClosedThreshold_le_at_four'),
             ('fejerFiveTermThreshold_le_at_five', 'fejerFiveTermThreshold_le_at_four'),
             ('theorem_18_2_L5_le_five', 'theorem_18_2_L4_le_five'),
             ('corollary_18_7_L5_le_five', 'corollary_18_7_L4_le_five')]:
    body = re.sub(r'\b' + a + r'\b', b, body)
body = body.replace('with `L + 5` at every length', 'with `L + 4` at every length')
bad = [l for l in body.split('\n') if re.search(r'At 5\b|_L5_|_at_five\b|_five\b(?! \{)|1024', l)
       and 'le_five' not in l and 'L5' not in l.replace('_L5_', '')]
assert not bad, bad
head = '''import GowersSzemeredi.Proofs18CoverThresholdsSharp

/-! **Theorem 18.2 and Corollary 18.7 with `L + 4` at lengths `L ≤ 5`**
(Notes L.16d).

The short-length block of `Proofs18CoverThresholdsSharp` with `5` replaced
by `4` (generated). The corpus's explicit thresholds (Roth's
`exp(exp(10¹²·δ⁻¹))` for `L ≤ 3`; towers with `2^21` and `2^73` on top for
`L = 4, 5`) stay below the threshold with `L + 4` on top:
`2^(4+4) = 256 ≥ 21` and `2^(5+4) = 512 ≥ 73`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

'''
(GS / 'Proofs18CoverFejerShortLengths.lean').write_text(head + body + 'end LeanProofs.GowersSzemeredi\n',
                                                       encoding='utf8', newline='\n')
print('ok')
