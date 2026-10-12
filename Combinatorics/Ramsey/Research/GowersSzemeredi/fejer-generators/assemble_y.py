"""Proofs18CoverFejerHeadlineY: the Z envelope with the partition constant charged at 2^(k+9) (Notes L.16p)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
SP = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:110])
        t = t.replace(a, b)
    return t


s = (GS / 'Proofs18CoverFejerHeadlineZ.lean').read_text(encoding='utf-8')
a = s.index('/-- The envelope after one step (no threshold). -/')
b = s.index('/-- The polynomial bound on the family constants')
c = s.index('/-- The Theorem 18.1 envelope at the tight base budget. -/')
d = s.index('/-! ### Closed forms -/')
t1 = s.index('/-- The envelope after one step, with the threshold, without the cubic branch. -/')
t2 = s.index('/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/')
body = s[a:t1] + s[c:t2]
OLD_HN = '''    have hn : 4 * (k + 3) ^ 2 + 5 ≤ 2 ^ (4 * (k + 3) ^ 2 + 4) :=
      Nat.lt_two_pow_self (n := 4 * (k + 3) ^ 2 + 4)
'''
assert body.count(OLD_HN) == 1
body = body.replace(OLD_HN, '    have hn : 4 * (k + 3) ^ 2 + 5 ≤ 2 ^ (k + 9) := four_sq_add_five_le k\n')
assert body.count('4 * (k + 3) ^ 2 + 14') == 1
body = body.replace('4 * (k + 3) ^ 2 + 14', 'k + 19')
body = body.replace('(2 / alpha) ^ (2 ^ (4 * (k + 3) ^ 2 + 4))', '(2 / alpha) ^ (2 ^ (k + 9))')
body = body.replace('2 ^ (2 ^ (4 * (k + 3) ^ 2 + 4))', '2 ^ (2 ^ (k + 9))')
body = body.replace('max (max (4 * (k + 3) ^ 2 + 4) (E + 3) + 1) M1 + 1', 'max (max (k + 9) (E + 3) + 1) M1 + 1')
assert '4 * (k + 3) ^ 2 + 4' not in body, [l for l in body.split('\n') if '4 * (k + 3) ^ 2 + 4' in l]
for x, y in [('envStepZTx', 'envStepYTx'), ('envStepZ', 'envStepY'), ('polyEnvBound_stepZ', 'polyEnvBound_stepY'),
             ('envBound_stepZx', 'envBound_stepYx'), ('polyGenMuZ_succ', 'polyGenMuY_succ'), ('polyGenMuZ', 'polyGenMuY'),
             ('polyEnvBound_allZ', 'polyEnvBound_allY'), ('genMuXZ_succ', 'genMuXY_succ'), ('genMuXZ', 'genMuXY'),
             ('envBound_allXZ', 'envBound_allXY')]:
    body = re.sub(r'\b' + x + r'\b', y, body)
bad = [l for l in body.split('\n') if re.search(r'\b(envStepZ\w*|polyEnvBound_\w*Z|envBound_\w*Z\w*|polyGenMuZ\w*|genMuXZ\w*)\b', l)]
assert not bad, bad[:5]
head = (SP / 'headline_y_head.lean').read_text(encoding='utf-8')
tail = (SP / 'headline_y_tail.lean').read_text(encoding='utf-8')
PRE = 'set_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\nnamespace LeanProofs.GowersSzemeredi\n\n'
LEM = '''/-- The partition constant fits `2^(2^(k+9))`: `4(k+3)² + 5 ≤ 2^(k+9)`. -/
theorem four_sq_add_five_le (k : Nat) : 4 * (k + 3) ^ 2 + 5 ≤ 2 ^ (k + 9) := by
  rcases Nat.lt_or_ge k 4 with h | h
  · interval_cases k <;> norm_num
  · have h1 := sq_le_two_pow_four k h
    have h2 : (k + 3) ^ 2 ≤ (k + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h9 : 2 ^ (k + 9) = 512 * 2 ^ k := by rw [pow_add]; ring
    have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

'''
out = head + PRE + LEM + body + tail + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs18CoverFejerHeadlineY.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
