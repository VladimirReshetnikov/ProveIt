"""JM chain: the joint-slice step over the max classes tDegM (Notes L.16w)."""
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
        return tok + 'M'
    if tok.startswith('polyGenMuJ'):
        return 'polyGenMuJM' + tok[len('polyGenMuJ'):]
    if tok.startswith('envStepJ_'):
        return 'envStepJM_' + tok[len('envStepJ_'):]
    if tok.startswith('rhoDegJ_'):
        return 'rhoDegJM_' + tok[len('rhoDegJ_'):]
    for a, b in (('tDegZ', 'tDegM'), ('uDegZ', 'uDegM'), ('classZ', 'classM')):
        tok = tok.replace(a, b)
    return tok


def rename(t):
    return re.sub(r"[A-Za-z_][A-Za-z0-9_']*", lambda m: ren(m.group(0)), t)


PRE = 'set_option autoImplicit false\nnoncomputable section\nnamespace LeanProofs.GowersSzemeredi\n\n'

# Modulus
s = text('Proofs18CoverModulusFejerJ')
b = rename(s[s.index('/-! ### The parameters -/'):s.rindex('end LeanProofs.GowersSzemeredi')])
(GS / 'Proofs18CoverModulusFejerJM.lean').write_text('''import GowersSzemeredi.Proofs18CoverModulusFejerJ
import GowersSzemeredi.Proofs18TightClassesFejerM

/-! **The joint-slice step at the max classes `tDegM`** (Notes L.16w), part 1
(generated from `Proofs18CoverModulusFejerJ` by `assemble_jm.py`). -/
''' + PRE + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')

# Density: keep sq_le_two (renamed), drop joint_dens_step (shared from DensityJ)
s = text('Proofs18CoverDensityFejerJ')
a = s.index('/-- `3(k+4)² ≤ 2·tDegZ k + 6k + 35`')
c = s.index('/-- **The joint-slice density**')
d = s.index('variable {alpha : Real}')
b = rename(s[a:c] + s[d:s.rindex('end LeanProofs.GowersSzemeredi')])
(GS / 'Proofs18CoverDensityFejerJM.lean').write_text('''import GowersSzemeredi.Proofs18CoverModulusFejerJM
import GowersSzemeredi.Proofs18CoverDensityFejerJ

/-! **The joint-slice step at `tDegM`**, part 2 (generated from
`Proofs18CoverDensityFejerJ` by `assemble_jm.py`). -/
''' + PRE + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')

# Exponents
s = text('Proofs18CoverExponentsFejerJ')
b = rename(s[s.index('namespace GenParamsJ'):s.rindex('end LeanProofs.GowersSzemeredi')])
(GS / 'Proofs18CoverExponentsFejerJM.lean').write_text('''import GowersSzemeredi.Proofs18CoverDensityFejerJM
import GowersSzemeredi.Proofs18CoverExponentsFejerJ

/-! **The joint-slice step at `tDegM`**, part 3 (generated from
`Proofs18CoverExponentsFejerJ` by `assemble_jm.py`). -/
''' + PRE + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')

# Headline: Theorem 18.1 only
h = text('Proofs18CoverFejerHeadlineJ')
a = h.index('/-- The standing hypotheses at the polynomial base budget. -/')
x1 = h.index('/-- The envelope after one step, with the threshold, without the cubic branch. -/')
c = h.index('/-! ### Closed forms -/')
hs = h.index('/-! ### The headline statements -/')
body = h[a:x1] + h[c:hs]
body = rename(body)
# fits: d + 2 from d = 11 needs k >= 9
body = body.replace('theorem polyGenMuJM_small16 {k : Nat} (h1 : 10 ≤ k)', 'theorem polyGenMuJM_small16 {k : Nat} (h1 : 9 ≤ k)')
body = body.replace('theorem polyGenMuJM_fit16 {k : Nat} (hk : 10 ≤ k)', 'theorem polyGenMuJM_fit16 {k : Nat} (hk : 9 ≤ k)')
assert 'polyGenMuJM_small16 {k : Nat} (h1 : 9' in body and 'polyGenMuJM_fit16 {k : Nat} (hk : 9' in body
# only the 16-fit is needed
for P in (32, 64):
    i = body.index(f'theorem polyGenMuJM_small{P}')
    j = body.index('/-! ### The headline statements -/') if False else None
    k2 = body.index(f'theorem polyGenMuJM_fit{P}')
    e = body.index('\n\n', body.index('    omega', k2)) + 2
    body = body[:i] + body[e:]
assert 'polyGenMuJM_fit32' not in body and 'polyGenMuJM_fit64' not in body
THM = '''/-! ### The headline statement -/

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 2`**, from the profiles
with polynomial family constants (joint slices, max classes). -/
theorem theorem_18_1_d2_eleven_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 2 d := by
  have henv := polyEnvBound_allJM Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  have hle := polyGenMuJM_fit16 (k := d - 2) (by omega)
  have h2 : 2 ^ (d + 2) = 16 * 2 ^ (d - 2) := by
    rw [show d + 2 = (d - 2) + 4 by omega, pow_add]; ring
  rw [h2]
  exact hle

'''
bad = [l.strip()[:120] for l in body.split('\n') if re.search(r'\b(GenParamsJ|densDegJ|tDegZ|uDegZ|polyGenMuJ|classZ)\b', l)]
assert not bad, bad[:6]
(GS / 'Proofs18CoverFejerHeadlineJM.lean').write_text('''import GowersSzemeredi.Proofs18CoverExponentsFejerJM
import GowersSzemeredi.Proofs18CoverFejerHeadlineJ

/-! **Theorem 18.1 at `d + 2` from `d = 11`: joint slices over the max
classes** (Notes L.16w).

The Theorem 18.1 envelope of `Proofs18CoverFejerHeadlineJ` over the class
table `tDegM` of the split step combined by `max`
(`Proofs18TightClassesFejerM`). The closed forms are those of `tDegZ` from
`k = 15`; `decide +kernel` evaluates dimensions `9, …, 14` (generated by
`assemble_jm.py`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

''' + body + THM + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')
print('wrote JM chain')
