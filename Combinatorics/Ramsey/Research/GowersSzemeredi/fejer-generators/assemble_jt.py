"""JT chain: the joint-slice step over the two-track classes tDegT2 (Notes L.16x)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


JSET = {'GenParamsJ', 'densDegJ', 'expDegJ', 'rhoDegJ', 'threshDegJ', 'yIn_boundsJ', 'Eloc_inv_leJ',
        'rho1_inv_leJ', 'nestExp_inv_leJ', 'spectrum_exps_inv_leJ', 'slice_exps_inv_leJ', 'MReq_le_expJ',
        'Tloc_le_expJ', 'coverPrec_gen_bounds_fejerJ', 'tightHyp_of_profiles_fejerJ', 'envStepJ',
        'polyEnvBound_stepJ', 'polyEnvBound_allJ'}
PREFIX = ('polyGenMuJ', 'envStepJ_')


def ren(tok):
    if tok in JSET:
        return tok + 'T'
    if tok.startswith('polyGenMuJ'):
        return 'polyGenMuJT' + tok[len('polyGenMuJ'):]
    if tok.startswith('envStepJ_'):
        return 'envStepJT_' + tok[len('envStepJ_'):]
    if tok.startswith('rhoDegJ_'):
        return 'rhoDegJT_' + tok[len('rhoDegJ_'):]
    for a, b in (('tDegZ', 'tDegT2'), ('uDegZ', 'uDegT2'), ('classZ', 'classT2')):
        tok = tok.replace(a, b)
    return tok


def rename(t):
    return re.sub(r"[A-Za-z_][A-Za-z0-9_']*", lambda m: ren(m.group(0)), t)


PRE = 'set_option autoImplicit false\nnoncomputable section\nnamespace LeanProofs.GowersSzemeredi\n\n'

# Modulus
s = text('Proofs18CoverModulusFejerJ')
b = rename(s[s.index('/-! ### The parameters -/'):s.rindex('end LeanProofs.GowersSzemeredi')])
(GS / 'Proofs18CoverModulusFejerJT.lean').write_text('''import GowersSzemeredi.Proofs18CoverModulusFejerJ
import GowersSzemeredi.Proofs16SplitTwoTrackClasses

/-! **The joint-slice step at the two-track classes `tDegT2`** (Notes L.16x), part 1
(generated from `Proofs18CoverModulusFejerJ` by `assemble_jt.py`). -/
''' + PRE + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')

# Density: keep sq_le_two (renamed), drop joint_dens_step (shared from DensityJ)
s = text('Proofs18CoverDensityFejerJ')
a = s.index('/-- `3(k+4)² ≤ 2·tDegZ k + 6k + 35`')
c = s.index('/-- **The joint-slice density**')
d = s.index('variable {alpha : Real}')
b = rename(s[a:c] + s[d:s.rindex('end LeanProofs.GowersSzemeredi')])
(GS / 'Proofs18CoverDensityFejerJT.lean').write_text('''import GowersSzemeredi.Proofs18CoverModulusFejerJT
import GowersSzemeredi.Proofs18CoverDensityFejerJ

/-! **The joint-slice step at `tDegT2`**, part 2 (generated from
`Proofs18CoverDensityFejerJ` by `assemble_jt.py`). -/
''' + PRE + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')

# Exponents
s = text('Proofs18CoverExponentsFejerJ')
b = rename(s[s.index('namespace GenParamsJ'):s.rindex('end LeanProofs.GowersSzemeredi')])
(GS / 'Proofs18CoverExponentsFejerJT.lean').write_text('''import GowersSzemeredi.Proofs18CoverDensityFejerJT
import GowersSzemeredi.Proofs18CoverExponentsFejerJ

/-! **The joint-slice step at `tDegT2`**, part 3 (generated from
`Proofs18CoverExponentsFejerJ` by `assemble_jt.py`). -/
''' + PRE + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')

# Headline: Theorem 18.1 only
h = text('Proofs18CoverFejerHeadlineJ')
a = h.index('/-- The standing hypotheses at the polynomial base budget. -/')
x1 = h.index('/-- The envelope after one step, with the threshold, without the cubic branch. -/')
c = h.index('/-! ### Closed forms -/')
hs = h.index('/-! ### The headline statements -/')
body = h[a:x1] + h[c:hs]
body = rename(body)
# fits: only d + 3 from d = 8, i.e. the 32-fit from k = 6
body = body.replace('theorem polyGenMuJT_small32 {k : Nat} (h1 : 7 ≤ k)', 'theorem polyGenMuJT_small32 {k : Nat} (h1 : 6 ≤ k)')
body = body.replace('theorem polyGenMuJT_fit32 {k : Nat} (hk : 7 ≤ k)', 'theorem polyGenMuJT_fit32 {k : Nat} (hk : 6 ≤ k)')
assert 'polyGenMuJT_small32 {k : Nat} (h1 : 6' in body and 'polyGenMuJT_fit32 {k : Nat} (hk : 6' in body
for P in (16, 64):
    i = body.index('theorem polyGenMuJT_small%d' % P)
    k2 = body.index('theorem polyGenMuJT_fit%d' % P)
    e = body.index('\n\n', body.index('    omega', k2)) + 2
    body = body[:i] + body[e:]
assert 'polyGenMuJT_fit16' not in body and 'polyGenMuJT_fit64' not in body and 'polyGenMuJT_fit32' in body
THM = open('jt_thm.lean.txt', encoding='utf-8').read()
bad = [l.strip()[:120] for l in body.split('\n') if re.search(r'\b(GenParamsJ|densDegJ|tDegZ|uDegZ|polyGenMuJ|classZ)\b', l)]
assert not bad, bad[:6]
HEAD = open('jt_head.lean.txt', encoding='utf-8').read()
(GS / 'Proofs18CoverFejerHeadlineJT.lean').write_text(HEAD + body + THM + 'end LeanProofs.GowersSzemeredi\n',
                                                      encoding='utf-8', newline='\n')
print('wrote JT chain')
