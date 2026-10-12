"""X copies (class table tDegX: exact to 12, constant 5/2 beyond) of the W chain (Notes L.16n)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
SP = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


RENAMES = ['tDeg_eq_of_ge:tDegX_eq_of_ge', 'seventeen_le_tDeg:seventeen_le_tDegX', 'sq_le_three_tDeg:sq_le_three_tDegX',
           'tDeg_mono:tDegX_mono', 'tDeg:tDegX', 'uDegT_eq:uDegX_eq', 'uDegT_le_pow:uDegX_le_pow', 'uDegT:uDegX',
           'polyCoverAt_classT:polyCoverAt_classX',
           'GenParamsW:GenParamsX', 'coverPrec_gen_bounds_fejerW:coverPrec_gen_bounds_fejerX',
           'rhoDegW_ge:rhoDegX_ge', 'rhoDegW:rhoDegX', 'rho1_inv_leW:rho1_inv_leX', 'nestExp_inv_leW:nestExp_inv_leX',
           'densDegW:densDegX', 'yIn_boundsW:yIn_boundsX', 'expDegW:expDegX',
           'spectrum_exps_inv_leW:spectrum_exps_inv_leX', 'slice_exps_inv_leW:slice_exps_inv_leX',
           'Eloc_inv_leW:Eloc_inv_leX', 'threshDegW:threshDegX', 'MReq_le_expW:MReq_le_expX',
           'Tloc_le_expW:Tloc_le_expX', 'tightMu0W:tightMu0X', 'envStepWTx:envStepXTx', 'envStepW:envStepX',
           'polyEnvBound_stepW:polyEnvBound_stepX', 'envBound_stepWx:envBound_stepXx',
           'tightHyp_of_profiles_fejerW:tightHyp_of_profiles_fejerX', 'polyGenMuW_succ:polyGenMuX_succ',
           'polyGenMuW:polyGenMuX', 'polyEnvBound_allW:polyEnvBound_allX', 'genMuXW_succ:genMuXX_succ',
           'genMuXW:genMuXX', 'envBound_allXW:envBound_allXX', 'genMuKW:genMuKX']


def rename(t):
    for p in RENAMES:
        a, b = p.split(':')
        t = re.sub(r'\b' + a + r'\b', b, t)
    return t


BAD = re.compile(r'\b(?:' + '|'.join(p.split(':')[0] for p in RENAMES) + r')\b')


def check(name, t):
    bad = [(BAD.search(l).group(0), l.strip()[:150]) for l in t.split('\n')
           if BAD.search(l) and not l.lstrip().startswith(('--', '/-', '`'))]
    assert not bad, (name, bad[:10])


PRE = 'set_option autoImplicit false\nnoncomputable section\nnamespace LeanProofs.GowersSzemeredi\n\n'


def write(dst, head, b):
    check(dst, b)
    (GS / f'{dst}.lean').write_text(head + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')
    print('wrote', dst)


s = text('Proofs18CoverModulusFejerW')
b = rename(s[s.index('/-! ### The parameters -/'):s.rindex('end LeanProofs.GowersSzemeredi')])
write('Proofs18CoverModulusFejerX', '''import GowersSzemeredi.Proofs18CoverModulusFejerW
import GowersSzemeredi.Proofs18TightClassesFejerX

/-! **The Section 18 step at the class table `tDegX`** (Notes L.16n), part 1:
`GenParamsX` (generated from `Proofs18CoverModulusFejerW`, with the covers at
`uDegX l = 2^tDegX l`). -/
''' + PRE, b)

s = text('Proofs18CoverDensityFejerW')
b = rename(s[s.index('variable {alpha : Real}'):s.rindex('end LeanProofs.GowersSzemeredi')])
write('Proofs18CoverDensityFejerX', '''import GowersSzemeredi.Proofs18CoverModulusFejerX
import GowersSzemeredi.Proofs18EtaStepSmall

/-! **The Section 18 step at `tDegX`**, part 2: the density envelope (generated
from `Proofs18CoverDensityFejerW`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

''', b)

s = text('Proofs18CoverExponentsFejerW')
b = rename(s[s.index('namespace GenParamsW'):s.rindex('end LeanProofs.GowersSzemeredi')])


def sub(t, pairs):
    for a, c in pairs:
        assert a in t, ('missing', a[:110])
        t = t.replace(a, c)
    return t


# the polynomial Lemma 15.6 threshold (Notes L.16n)
b = sub(b, [
    ('def threshDegX (k μ0 μK : Nat) : Nat := max (expDegX k μ0 μK + 4) (2 ^ (k + 4) + 5 * k + 25)',
     'def threshDegX (k μ0 μK : Nat) : Nat := max (expDegX k μ0 μK + 4) (5 * k + 30)'),
    ('have hZT : 2 ^ (k + 4) + 5 * k + 25 ≤ T', 'have hZT : 5 * k + 30 ≤ T'),
    ('have hL := lemma156_gen_le_fejer hk ha ha2', 'have hL := lemma156_gen_le_fejer5 hk ha ha2'),
    ('    have : 2 ^ (k + 4) + 4 * k + 13 ≤ 2 ^ (k + 4) + 5 * k + 25 := by omega\n',
     '    have : 5 * k + 21 ≤ 5 * k + 30 := by omega\n'),
])
L156 = '''/-- **The Fejér Lemma 15.6 threshold is polynomial**: `≤ X^(2^(5k+21))`
(`lemma156_gen_le_fejer` weakens the same estimate to `2^(k+4) + 4k + 13`). -/
theorem lemma156_gen_le_fejer5 {k : Nat} (hk : 1 ≤ k) {alpha : Real} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    fejerProductThreshold k (alpha / 2) (alpha / 2) ≤ (2 / alpha) ^ (2 ^ (5 * k + 21)) := by
  have ha1 : alpha ≤ 1 := by linarith
  have hX := two_div_ge_two ha ha2
  have h := fejerProductThreshold_le_gen (gamma := alpha / 2) (theta := alpha) hk (half_pos ha)
    (by linarith) ha ha1
  have hu : 2 / (alpha / 2 * alpha) = (2 / alpha) ^ 2 := by field_simp <;> ring
  rw [hu, ← pow_mul] at h
  refine h.trans (pow_le_pow_right₀ (le_trans (by norm_num) hX) ?_)
  have hP := fejerStepP_le k
  calc 2 * fejerStepP k ≤ 2 * 2 ^ (5 * k + 20) := Nat.mul_le_mul_left 2 hP
    _ = 2 ^ (5 * k + 21) := by rw [pow_succ]; ring

'''
write('Proofs18CoverExponentsFejerX', '''import GowersSzemeredi.Proofs18CoverDensityFejerX
import GowersSzemeredi.Proofs18CoverFejerHeadlineU

/-! **The Section 18 step at `tDegX`**, part 3: the width exponents and
thresholds (generated from `Proofs18CoverExponentsFejerW`). The modulus
threshold uses the polynomial Lemma 15.6 threshold `lemma156_gen_le_fejer5`,
so `threshDegX = max(expDeg + 4, 5k + 30)`. -/
''' + PRE + L156, b)

s = text('Proofs18CoverFejerHeadlineW')
b = rename(s[s.index('/-- The polynomial base budget. -/'):s.index('/-! ### Closed forms -/')])
head = (SP / 'headline_x_head.lean').read_text(encoding='utf-8')
tail = (SP / 'headline_x_tail.lean').read_text(encoding='utf-8')
write('Proofs18CoverFejerHeadlineX', head + PRE.replace('noncomputable section\n', 'noncomputable section\nopen scoped BigOperators\n'),
      b + tail)
