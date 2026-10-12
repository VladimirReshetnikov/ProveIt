"""T copies (exact class table tDeg) of the S Section 18 chain (Notes L.16k)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
SP = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


RENAMES = ['sDeg:tDeg', 'uDegS_eq:uDegT_eq', 'uDegS_le_pow:uDegT_le_pow', 'uDegS:uDegT',
           'GenParamsS:GenParamsT', 'coverPrec_gen_bounds_fejerS:coverPrec_gen_bounds_fejerT',
           'rhoDegS_ge:rhoDegT_ge', 'rhoDegS:rhoDegT', 'rho1_inv_leS:rho1_inv_leT', 'nestExp_inv_leS:nestExp_inv_leT',
           'densDegS:densDegT', 'yIn_boundsS:yIn_boundsT', 'expDegS:expDegT',
           'spectrum_exps_inv_leS:spectrum_exps_inv_leT', 'slice_exps_inv_leS:slice_exps_inv_leT',
           'Eloc_inv_leS:Eloc_inv_leT', 'threshDegS:threshDegT', 'MReq_le_expS:MReq_le_expT',
           'Tloc_le_expS:Tloc_le_expT', 'polyCoverAt_classS:polyCoverAt_classT', 'tightMu0S:tightMu0T',
           'envStepSTx:envStepTTx', 'envStepS:envStepT', 'polyEnvBound_stepS:polyEnvBound_stepT',
           'envBound_stepSx:envBound_stepTx', 'tightHyp_of_profiles_fejerS:tightHyp_of_profiles_fejerT',
           'polyGenMuS_succ:polyGenMuE_succ', 'polyGenMuS:polyGenMuE', 'polyEnvBound_allS:polyEnvBound_allE',
           'genMuXS_succ:genMuXT_succ', 'genMuXS:genMuXT', 'envBound_allXS:envBound_allXT']


def rename(t):
    for p in RENAMES:
        a, b = p.split(':')
        t = re.sub(r'\b' + a + r'\b', b, t)
    return t


BAD = re.compile(r'\b(?:sDeg|uDegS|GenParamsS|\w+S_ge|\w+_inv_leS|\w+DegS|\w+_expS|tightMu0S|envStepS\w*|'
                 r'polyGenMuS\w*|genMuXS\w*|\w+_allX?S|\w+_stepSx?|polyCoverAt_classS|\w+fejerS)\b')


def check(name, t):
    bad = [(BAD.search(l).group(0), l.strip()[:150]) for l in t.split('\n')
           if BAD.search(l) and not l.lstrip().startswith(('--', '/-', '`'))]
    assert not bad, (name, bad[:10])


PRE = 'set_option autoImplicit false\nnoncomputable section\nnamespace LeanProofs.GowersSzemeredi\n\n'


def write(dst, head, b):
    check(dst, b)
    (GS / f'{dst}.lean').write_text(head + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')
    print('wrote', dst)


# --- Modulus
s = text('Proofs18CoverModulusFejerS')
b = rename(s[s.index('/-! ### The parameters -/'):s.rindex('end LeanProofs.GowersSzemeredi')])
write('Proofs18CoverModulusFejerT', '''import GowersSzemeredi.Proofs18CoverExponentsFejer
import GowersSzemeredi.Proofs18TightClassesFejerT
import GowersSzemeredi.Proofs18FejerEnvelopeBaseQ
import GowersSzemeredi.Proofs18CoverTightBase

/-! **The Section 18 step at the exact class table `tDeg`** (Notes L.16k),
part 1: `GenParamsT` and the scale conditions. Generated from
`Proofs18CoverModulusFejerS`, with the covers at `uDegT l = 2^tDeg l`
(`polyCoverAt_classT`). -/
''' + PRE + '''theorem uDegT_eq (l : Nat) : uDegT l = 2 ^ tDeg l := rfl

theorem uDegT_le_pow {l k : Nat} (hl : l ≤ k) : uDegT l ≤ 2 ^ tDeg k := by
  rw [uDegT_eq]; exact Nat.pow_le_pow_right (by norm_num) (tDeg_mono hl)

/-- The η side condition `3(k+4)²` sits inside the base budget. -/
theorem sq_le_fixDegQ (k : Nat) : 3 * (k + 4) ^ 2 ≤ fixDegQ k + 64 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide
  · rw [fixDegQ_eq hk]
    rcases Nat.lt_or_ge k 4 with h | h
    · interval_cases k <;> norm_num
    · have h1 := sq_le_two_pow_four k h
      have h2 : 2 ^ (k + 4) = 16 * 2 ^ k := two_pow_four_mul k
      omega

''', b)

# --- Density
s = text('Proofs18CoverDensityFejerS')
b = s[s.index('variable {alpha : Real}'):s.rindex('end LeanProofs.GowersSzemeredi')]
OLD = '''  -- the polynomial side condition of `eta_step_small` (the printed `fixDeg k`
  -- would exceed the density degree at class constant `4`)
  have hm : 3 * (k + 4) ^ 2 ≤ rhoDegS k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by
    have : 3 * (k + 4) ^ 2 ≤ μD := by rw [hμDdef]; unfold sDeg; omega
    omega
'''
NEW = '''  -- the polynomial side condition of `eta_step_small`, inside the base budget
  have hm : 3 * (k + 4) ^ 2 ≤ rhoDegS k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by
    have h1 := sq_le_fixDegQ k
    have h2 := le_max_right μV (fixDegQ k)
    have h3 : 17 ≤ μD := by rw [hμDdef]; exact seventeen_le_tDeg k
    omega
'''
assert OLD in b
b = rename(b.replace(OLD, NEW))
write('Proofs18CoverDensityFejerT', '''import GowersSzemeredi.Proofs18CoverModulusFejerT
import GowersSzemeredi.Proofs18EtaStepSmall

/-! **The Section 18 step at `tDeg`**, part 2: the density envelope (generated
from `Proofs18CoverDensityFejerS`). The η side condition `3(k+4)² ≤ m` now
comes from the base budget (`sq_le_fixDegQ`), since the table entries are
below `3(k+4)²` in dimensions `1, …, 5`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

''', b)

# --- Exponents
s = text('Proofs18CoverExponentsFejerS')
b = rename(s[s.index('namespace GenParamsS'):s.rindex('end LeanProofs.GowersSzemeredi')])
write('Proofs18CoverExponentsFejerT', '''import GowersSzemeredi.Proofs18CoverDensityFejerT

/-! **The Section 18 step at `tDeg`**, part 3: the width exponents and
thresholds (generated from `Proofs18CoverExponentsFejerS`). -/
''' + PRE, b)

# --- Headline
s = text('Proofs18CoverFejerHeadlineS')
b = rename(s[s.index('/-- The base budget at the class-base term. -/'):s.index('/-! ### Closed forms -/')])
head = (SP / 'headline_t_head.lean').read_text(encoding='utf-8')
tail = (SP / 'headline_t_tail.lean').read_text(encoding='utf-8')
write('Proofs18CoverFejerHeadlineT', head + PRE.replace('noncomputable section\n', 'noncomputable section\nopen scoped BigOperators\n'),
      b + tail)
