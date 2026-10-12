"""Proofs18EtaStepSmall: eta_step / yIn_step with side condition 3(k+4)^2 <= m."""
from pathlib import Path
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs18GenericDensity.lean').read_text(encoding='utf-8')
a = s.index('theorem eta_step ')
a = s.rindex('\n\n', 0, a) + 2
b = s.index('/-- **The input parameter of the lower-degree bound**')
body = s[a:b]
reps = [('theorem eta_step ', 'theorem eta_step_small '), ('theorem yIn_step ', 'theorem yIn_step_small '),
        ('(hm : fixDeg k ≤ m)', '(hm : 3 * (k + 4) ^ 2 ≤ m)'),
        ('(fixDeg_cube k)', '(cube_le_two_pow_sq k)'),
        ('2 ^ fixDeg k', '2 ^ (3 * (k + 4) ^ 2)')]
for x, y in reps:
    assert x in body, x
    body = body.replace(x, y)
assert 'fixDeg' not in body, [l for l in body.split('\n') if 'fixDeg' in l]
HEAD = '''import GowersSzemeredi.Proofs18GenericDensity

/-! **The η and `yIn` steps with a polynomial side condition** (Notes L.16j).

`GenParams.eta_step` and `GenParams.yIn_step` ask for `fixDeg k ≤ m`, with
`fixDeg k = 2^(k+5) + 7`. They use it only to absorb
`2^(2(k+2)³)·2^(k+1)·(2/α)²` and `2·(2(k+3))^(k+3)` into `(2/α)^(2^m)`, and
`m ≥ 3(k+4)²` already suffices (`cube_le_two_pow_sq`). At the class constant
`4` the density degree is about `28·2^k < 32·2^k`, so the printed side
condition would raise one step from `28·2^k` to `32·2^k`. The envelope would
then tend to `64·2^k` and lose `d + 4`. The copies below (generated, proofs
verbatim up to the budget lemma) remove that floor. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The constants of the η and `yIn` steps fit `2^(3(k+4)²)`. -/
theorem cube_le_two_pow_sq (k : Nat) : 2 * (k + 2) ^ 3 + k + 3 ≤ 2 ^ (3 * (k + 4) ^ 2) ∧
    2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 ^ (3 * (k + 4) ^ 2) := by
  constructor
  · have h1 : (k + 2) ^ 3 ≤ (2 ^ (k + 2)) ^ 3 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
    have h2 : (2 ^ (k + 2)) ^ 3 = 2 ^ (3 * k + 6) := by rw [← pow_mul]; ring_nf
    have h3 : k + 3 ≤ 2 ^ (3 * k + 6) :=
      (Nat.lt_two_pow_self (n := k + 3)).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : 2 ^ (3 * k + 8) = 4 * 2 ^ (3 * k + 6) := by
      rw [show 3 * k + 8 = (3 * k + 6) + 2 by ring, pow_add]; ring
    have h5 : 2 ^ (3 * k + 8) ≤ 2 ^ (3 * (k + 4) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  · have hk3 : 2 * (k + 3) ≤ 2 ^ (k + 3) := by
      have := Nat.lt_two_pow_self (n := k + 2); rw [pow_succ]; omega
    calc 2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 * (2 ^ (k + 3)) ^ (k + 3) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk3 _)
      _ = 2 ^ ((k + 3) * (k + 3) + 1) := by rw [← pow_mul, pow_succ]; ring
      _ ≤ 2 ^ (3 * (k + 4) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

namespace GenParams

'''
out = HEAD + body + 'end GenParams\n\nend LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs18EtaStepSmall.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
