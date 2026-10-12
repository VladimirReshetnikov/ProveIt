"""Proofs18FejerEnvelopeBaseW: the polynomial base budget (Notes L.16m)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
SP = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:100])
        t = t.replace(a, b)
    return t


gd = (GS / 'Proofs18GenericDensity.lean').read_text(encoding='utf-8')
a = gd.index('/-- `8VX/B ≤ X^(2^μ₀)`. -/')
b = gd.index('/-- **The base density is a reciprocal power.** -/')
sl = sub(gd[a:b], [
    ('theorem slice_const_le ', 'theorem slice_const_le_deg '),
    ('{μV k μ0 : Nat}', '{μV b μ0 : Nat}'),
    ('(hBi : B⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k)) (hμ0 : max μV (fixDeg k) + 2 ≤ μ0)',
     '(h7 : 7 ≤ b)\n    (hBi : B⁻¹ ≤ (2 / alpha) ^ (2 ^ b)) (hμ0 : max μV b + 2 ≤ μ0)'),
    ('  set m := max μV (fixDeg k)\n  have h7 : 7 ≤ fixDeg k := Nat.le_add_left 7 _\n', '  set m := max μV b\n'),
    ('le_max_right μV (fixDeg k)', 'le_max_right μV b'),
])
sl = sl.replace('/-- `8VX/B ≤ X^(2^μ₀)`. -/', '/-- `8VX/B ≤ X^(2^μ₀)`, at any budget degree `b ≥ 7`. -/')
assert 'fixDeg' not in sl

ge = (GS / 'Proofs18GenericExponents.lean').read_text(encoding='utf-8')
a = ge.index('theorem uCount_scale_le ')
b = ge.index('/-! ### The nest decreases -/')
uc = sub(ge[a:b], [
    ('theorem uCount_scale_le ', 'theorem uCount_scale_le_deg '),
    ('(hVμ : V ≤ 2 ^ (2 ^ μV)) {k : Nat} (hμ0 : max μV (fixDeg k) + 2 ≤ μ0)',
     '(hVμ : V ≤ 2 ^ (2 ^ μV)) {b : Nat} (h7 : 7 ≤ b) (hμ0 : max μV b + 2 ≤ μ0)'),
    ('(hgi : γ⁻¹ ≤ X ^ (2 ^ fixDeg k))', '(hgi : γ⁻¹ ≤ X ^ (2 ^ b))'),
    ('(hti : θ⁻¹ ≤ X ^ (2 ^ fixDeg k))', '(hti : θ⁻¹ ≤ X ^ (2 ^ b))'),
    ('  set m := max μV (fixDeg k)\n  have h7 : 7 ≤ m := le_trans (Nat.le_add_left 7 _) (le_max_right μV (fixDeg k))\n',
     '  set m := max μV b\n  have h7m : 7 ≤ m := le_trans h7 (le_max_right μV b)\n'),
])
assert 'fixDeg' not in uc, [l for l in uc.split('\n') if 'fixDeg' in l]
uc = '/-- `uCount_scale_le` at any budget degree `b ≥ 7`. -/\n' + uc

HALF = '''/-- `(α/2)⁻¹ ≤ X^(2^b)` at any degree. -/
theorem half_inv_le_deg (b : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (alpha / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ b) := by
  rw [inv_div]; exact pw_X (two_div_ge_two ha ha2) _

'''

bq =(GS / 'Proofs18FejerEnvelopeBaseQ.lean').read_text(encoding='utf-8')
a = bq.index('theorem baseCFQ_recipPowerLB')
a = bq.rindex('\n\n', 0, a) + 2
b = bq.index('end Fixed')
bc = sub(bq[a:b], [
    ('theorem baseCFQ_recipPowerLB', 'theorem baseCFW_recipPowerLB'),
    ('at `fixDegQ`.** -/', 'at the polynomial budget `pDeg`.** -/'),
    ('(hμ0 : max μV (fixDegQ k) + 2 ≤ μ0)', '(hμ0 : max μV (pDeg k) + 2 ≤ μ0)'),
    ('budget_gen_bounds_fejerQ k ha ha2', 'budget_gen_bounds_fejerW k ha ha2'),
    ('GenParams.slice_const_le (V := V)', 'GenParams.slice_const_le_deg (V := V)'),
    ('(μV := μV) (k := k - 1) (μ0 := μ0) ha ha2 hV hVμ hB0 hBi hμ0',
     '(μV := μV) (b := pDeg k) (μ0 := μ0) ha ha2 hV hVμ hB0 (seven_le_pDeg k) hBi hμ0'),
])
assert 'fixDeg' not in bc, [l for l in bc.split('\n') if 'fixDeg' in l]

head = (SP / 'basew_head.lean').read_text(encoding='utf-8')
tail = (SP / 'basew_tail.lean').read_text(encoding='utf-8')
out = (head + uc + 'namespace GenParams\n\nvariable {alpha : Real}\n\n' + sl + HALF + 'end GenParams\n\nsection Fixed\n\nvariable {alpha : Real}\n\n'
       + (SP / 'basew_fixed.lean').read_text(encoding='utf-8') + bc + 'end Fixed\n\n' + tail + 'end LeanProofs.GowersSzemeredi\n')
(GS / 'Proofs18FejerEnvelopeBaseW.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
