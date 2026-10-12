"""Proofs18CoverFejerHeadlineU: Theorem 18.2 at L+2 via the polynomial Bohr-radius bound (Notes L.16l)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
SP = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')


def sub(t, pairs, count=None):
    for a, b in pairs:
        assert a in t, ('missing', a[:100])
        t = t.replace(a, b)
    return t


ex = (GS / 'Proofs18CoverExponentsFejerT.lean').read_text(encoding='utf-8')
a = ex.index('/-- **The requirement on `m`**. -/')
b = ex.index('end GenParamsT', a)
mt = ex[a:b]
mt = sub(mt, [
    ('theorem MReq_le_expT', 'theorem MReq_le_expU'), ('theorem Tloc_le_expT', 'theorem Tloc_le_expU'),
    ('P.MReq_le_expT', 'P.MReq_le_expU'),
    ('(2 ^ (P.k + 6) + 4)', '(5 * P.k + 24)'),
    ('set Z := 2 ^ (k + 6) + 1 with hZdef', 'set Z := 5 * k + 21 with hZdef'),
    ('have hZ2 : 2 ≤ Z := by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega',
     'have hZ2 : 2 ≤ Z := by rw [hZdef]; omega'),
    ('zeta_gen_bounds_fejer k ha ha2', 'zeta_gen_bounds_fejer5 k ha ha2'),
    ('(by rw [hZdef]; have := Nat.one_le_two_pow (n := k + 6); omega)', '(by rw [hZdef]; omega)'),
    ('    rw [hTdef]; unfold threshDegT; omega\n',
     '    have := hET; have := hZT; have := Nat.two_pow_pos (k + 4)\n'
     '    simp only [max_def]; split_ifs <;> omega\n'),
    ('have hZT : 2 ^ (k + 6) + 5 ≤ T', 'have hZT : 2 ^ (k + 4) + 5 * k + 25 ≤ T'),
    ('''    have : 2 ^ (k + 4) + 4 * k + 13 ≤ 2 ^ (k + 6) + 5 := by
      have h := Nat.lt_two_pow_self (n := k)
      have h4 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
      have : 2 ^ (k + 6) = 64 * 2 ^ k := by rw [pow_add]; ring
      omega
''', '''    have : 2 ^ (k + 4) + 4 * k + 13 ≤ 2 ^ (k + 4) + 5 * k + 25 := by omega
'''),
])
mt = re.sub(r'\bthreshDegT\b', 'threshDegU', mt)
mt = re.sub(r'\bTloc_le_expT\b', 'Tloc_le_expU', mt)
assert 'k + 6' not in mt, [l for l in mt.split('\n') if 'k + 6' in l]
assert 'zeta_gen_bounds_fejer ' not in mt

hd = (GS / 'Proofs18CoverFejerHeadlineT.lean').read_text(encoding='utf-8')
p1 = hd[hd.index('/-- The envelope after one step, with the threshold, without the cubic branch. -/'):
        hd.index('/-- The standing hypotheses at the tight base budget. -/')]
p2 = hd[hd.index('/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/'):
        hd.index('/-! ### Closed forms -/')]
steps = p1 + p2
for x, y in [('envStepTTx', 'envStepUTx'), ('envBound_stepTx', 'envBound_stepUx'), ('Tloc_le_expT', 'Tloc_le_expU'),
             ('threshDegT', 'threshDegU'), ('genMuXT_succ', 'genMuXU_succ'), ('genMuXT', 'genMuXU'),
             ('envBound_allXT', 'envBound_allXU')]:
    steps = re.sub(r'\b' + x + r'\b', y, steps)
bad = [l for l in steps.split('\n') if re.search(r'envStepTTx|_stepTx\b|Tloc_le_expT|threshDegT|genMuXT|envBound_allXT', l)]
assert not bad, bad

head = (SP / 'headline_u_head.lean').read_text(encoding='utf-8')
tail = (SP / 'headline_u_tail.lean').read_text(encoding='utf-8')
out = (head + 'namespace GenParamsT\n\nvariable (P : GenParamsT) {alpha : Real}\n\n'
       '/-- The modulus-threshold degree with the polynomial Bohr radius. -/\n'
       'def threshDegU (k μ0 μK : Nat) : Nat := max (expDegT k μ0 μK + 4) (2 ^ (k + 4) + 5 * k + 25)\n\n'
       + mt + 'end GenParamsT\n\n' + steps + tail + 'end LeanProofs.GowersSzemeredi\n')
(GS / 'Proofs18CoverFejerHeadlineU.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
