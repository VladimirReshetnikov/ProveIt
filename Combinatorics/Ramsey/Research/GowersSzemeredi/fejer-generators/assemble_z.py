"""Z copies (class table exact to 14, then constant 5/2) of the X chain (Notes L.16o)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
SP = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:110])
        t = t.replace(a, b)
    return t


RENAMES = ['tDegX_eq_of_ge:tDegZ_eq_of_ge', 'seventeen_le_tDegX:seventeen_le_tDegZ', 'sq_le_three_tDegX:sq_le_three_tDegZ',
           'tDegX_mono:tDegZ_mono', 'tDegX:tDegZ', 'uDegX_eq:uDegZ_eq', 'uDegX_le_pow:uDegZ_le_pow', 'uDegX:uDegZ',
           'polyCoverAt_classX:polyCoverAt_classZ',
           'GenParamsX:GenParamsZ', 'coverPrec_gen_bounds_fejerX:coverPrec_gen_bounds_fejerZ',
           'rhoDegX_ge:rhoDegZ_ge', 'rhoDegX:rhoDegZ', 'rho1_inv_leX:rho1_inv_leZ', 'nestExp_inv_leX:nestExp_inv_leZ',
           'densDegX:densDegZ', 'yIn_boundsX:yIn_boundsZ', 'expDegX:expDegZ',
           'spectrum_exps_inv_leX:spectrum_exps_inv_leZ', 'slice_exps_inv_leX:slice_exps_inv_leZ',
           'Eloc_inv_leX:Eloc_inv_leZ', 'threshDegX:threshDegZ', 'MReq_le_expX:MReq_le_expZ',
           'Tloc_le_expX:Tloc_le_expZ', 'tightMu0X:tightMu0Z', 'envStepXTx:envStepZTx', 'envStepX:envStepZ',
           'polyEnvBound_stepX:polyEnvBound_stepZ', 'envBound_stepXx:envBound_stepZx',
           'tightHyp_of_profiles_fejerX:tightHyp_of_profiles_fejerZ', 'polyGenMuX_succ:polyGenMuZ_succ',
           'polyGenMuX:polyGenMuZ', 'polyEnvBound_allX:polyEnvBound_allZ', 'genMuXX_succ:genMuXZ_succ',
           'genMuXX:genMuXZ', 'envBound_allXX:envBound_allXZ', 'genMuKX:genMuKZ']


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


s = text('Proofs18CoverModulusFejerX')
b = rename(s[s.index('/-! ### The parameters -/'):s.rindex('end LeanProofs.GowersSzemeredi')])
write('Proofs18CoverModulusFejerZ', '''import GowersSzemeredi.Proofs18CoverModulusFejerX
import GowersSzemeredi.Proofs18TightClassesFejerZ

/-! **The Section 18 step at the class table `tDegZ`** (Notes L.16o), part 1
(generated from `Proofs18CoverModulusFejerX`). -/
''' + PRE, b)

s = text('Proofs18CoverDensityFejerX')
b = rename(s[s.index('variable {alpha : Real}'):s.rindex('end LeanProofs.GowersSzemeredi')])
write('Proofs18CoverDensityFejerZ', '''import GowersSzemeredi.Proofs18CoverModulusFejerZ
import GowersSzemeredi.Proofs18EtaStepSmall

/-! **The Section 18 step at `tDegZ`**, part 2 (generated from
`Proofs18CoverDensityFejerX`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

''', b)

s = text('Proofs18CoverExponentsFejerX')
b = rename(s[s.index('namespace GenParamsX'):s.rindex('end LeanProofs.GowersSzemeredi')])
write('Proofs18CoverExponentsFejerZ', '''import GowersSzemeredi.Proofs18CoverDensityFejerZ
import GowersSzemeredi.Proofs18CoverExponentsFejerX

/-! **The Section 18 step at `tDegZ`**, part 3 (generated from
`Proofs18CoverExponentsFejerX`, with the polynomial Lemma 15.6 threshold). -/
''' + PRE, b)

s = text('Proofs18CoverFejerHeadlineX')
b = rename(s[s.index('/-- The polynomial base budget. -/'):s.index('/-! ### Closed forms -/')])
tail = rename((SP / 'headline_x_tail.lean').read_text(encoding='utf-8'))
for x, y in [('envStepXTx_', 'envStepZTx_'), ('envStepX_', 'envStepZ_'), ('polyGenMuX_', 'polyGenMuZ_'),
             ('genMuXX_', 'genMuXZ_')]:
    tail = re.sub(r'\b' + x, y, tail)
tail = sub(tail, [
    ('theorem envStepZ_le_tight {k : Nat} (hk : 13 ≤ k)', 'theorem envStepZ_le_tight {k : Nat} (hk : 15 ≤ k)'),
    ('theorem envStepZTx_le_tight {k : Nat} (hk : 13 ≤ k)', 'theorem envStepZTx_le_tight {k : Nat} (hk : 15 ≤ k)'),
    ('/-- `32(k+5)² ≤ 2^k` for `k ≥ 15`. -/\ntheorem thirtytwo_sq_le_two_pow : ∀ k, 15 ≤ k →',
     '/-- `32(k+5)² ≤ 2^k` for `k ≥ 14`. -/\ntheorem thirtytwo_sq_le_two_pow_fourteen : ∀ k, 14 ≤ k →'),
    ('theorem polyGenMuZ_fifteen : polyGenMuZ 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel',
     'theorem polyGenMuZ_fourteen : polyGenMuZ 14 + 4 * 14 + 128 ≤ 16 * 2 ^ 14 := by decide +kernel'),
    ('theorem genMuXZ_fifteen : genMuXZ 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel',
     'theorem genMuXZ_fourteen : genMuXZ 14 + 4 * 14 + 128 ≤ 16 * 2 ^ 14 := by decide +kernel'),
    ('theorem polyGenMuZ_le16 : ∀ k, 15 ≤ k →', 'theorem polyGenMuZ_le16 : ∀ k, 14 ≤ k →'),
    ('theorem genMuXZ_le16 : ∀ k, 15 ≤ k →', 'theorem genMuXZ_le16 : ∀ k, 14 ≤ k →'),
    ('  | base => exact polyGenMuZ_fifteen', '  | base => exact polyGenMuZ_fourteen'),
    ('  | base => exact genMuXZ_fifteen', '  | base => exact genMuXZ_fourteen'),
    ('theorem_18_1_d2_seventeen_le_of_profiles_poly', 'theorem_18_1_d2_sixteen_le_of_profiles_poly'),
    ('{d : Nat} (hd : 17 ≤ d) : Theorem181AtSharp 2 d', '{d : Nat} (hd : 16 ≤ d) : Theorem181AtSharp 2 d'),
    ('theorem_18_2_L0_nineteen_le_of_profiles_poly', 'theorem_18_2_L0_eighteen_le_of_profiles_poly'),
    ('corollary_18_7_L0_nineteen_le_of_profiles_poly', 'corollary_18_7_L0_eighteen_le_of_profiles_poly'),
    ('{L : Nat} (hL : 19 ≤ L) : Theorem182AtSharp 0 L', '{L : Nat} (hL : 18 ≤ L) : Theorem182AtSharp 0 L'),
    ('{L : Nat} (hL : 19 ≤ L) : Corollary187AtSharp 0 L', '{L : Nat} (hL : 18 ≤ L) : Corollary187AtSharp 0 L'),
])
tail = tail.replace('thirtytwo_sq_le_two_pow k hk', 'thirtytwo_sq_le_two_pow_fourteen k hk')
tail = tail.replace('every degree `d ≥ 17`', 'every degree `d ≥ 16`').replace('every length `L ≥ 19`', 'every length `L ≥ 18`')
tail = tail.replace('for `k ≥ 15`. -/', 'for `k ≥ 14`. -/')
head = '''import GowersSzemeredi.Proofs18CoverExponentsFejerZ
import GowersSzemeredi.Proofs18CoverFejerHeadlineX

/-! **Theorem 18.1 at `d + 2` for every `d ≥ 16`, and Theorem 18.2 /
Corollary 18.7 with no offset for every `L ≥ 18`** (Notes L.16o).

`Proofs18CoverFejerHeadlineX` with the class table exact to dimension `14`
(`tDegZ`, `Proofs18TightClassesFejerZ`). The closed forms hold from
`k = 15`, and `decide +kernel` certifies the base of the invariant
`μ_k + 4k + 128 ≤ 16·2^k` at `k = 14`. That lowers both thresholds by one
(generated by `assemble_z.py`). -/
'''
write('Proofs18CoverFejerHeadlineZ', head + PRE.replace('noncomputable section\n', 'noncomputable section\nopen scoped BigOperators\n'),
      b + tail)
