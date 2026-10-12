"""S copies (class degree sDeg = 4*2^k + 3(k+4)^2 + 32) of the Q Section 18 chain (Notes L.16j)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
SP = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


RENAMES = ['qDeg_mono:sDeg_mono', 'qDeg:sDeg', 'uDegQ_eq:uDegS_eq', 'uDegQ_le_pow:uDegS_le_pow', 'uDegQ:uDegS',
           'GenParamsQ:GenParamsS', 'coverPrec_gen_bounds_fejerQ:coverPrec_gen_bounds_fejerS',
           'rhoDegQ_ge:rhoDegS_ge', 'rhoDegQ:rhoDegS', 'rho1_inv_leQ:rho1_inv_leS', 'nestExp_inv_leQ:nestExp_inv_leS',
           'densDegQ:densDegS', 'yIn_boundsQ:yIn_boundsS', 'expDegQ:expDegS',
           'spectrum_exps_inv_leQ:spectrum_exps_inv_leS', 'slice_exps_inv_leQ:slice_exps_inv_leS',
           'Eloc_inv_leQ:Eloc_inv_leS', 'threshDegQ:threshDegS', 'MReq_le_expQ:MReq_le_expS',
           'Tloc_le_expQ:Tloc_le_expS', 'polyCoverAt_classQ:polyCoverAt_classS', 'tightMu0Q:tightMu0S',
           'envStepQTx:envStepSTx', 'envStepQ:envStepS', 'polyEnvBound_stepQ:polyEnvBound_stepS',
           'envBound_stepQx:envBound_stepSx', 'tightHyp_of_profiles_fejerQ:tightHyp_of_profiles_fejerS',
           'polyGenMuQ_succ:polyGenMuS_succ', 'polyGenMuQ:polyGenMuS', 'polyEnvBound_allQ:polyEnvBound_allS',
           'genMuXQ_succ:genMuXS_succ', 'genMuXQ:genMuXS', 'envBound_allXQ:envBound_allXS']


def rename(t):
    for p in RENAMES:
        a, b = p.split(':')
        t = re.sub(r'\b' + a + r'\b', b, t)
    return t


# identifiers that must not survive (shared Q base lemmas are allowed)
BAD = re.compile(r'\b(?!fixDegQ|fixDeg_le_two_fixDegQ|five_k_le_fixDegQ|k_succ_le_two_pow_fixDegQ|'
                 r'budget_gen_bounds_fejerQ|T2_gen_bounds_fejerQ|delta_gen_bounds_fejerQ|baseCFQ_recipPowerLB|'
                 r'fixDegQ_eq|four_sq_le_two_pow_ten|h\w{0,3}Q\b)\w*Q(?:_\w*|x|Tx)?\b|\bqDeg|uDegQ')


def check(name, t):
    bad = [(BAD.search(l).group(0), l.strip()[:150]) for l in t.split('\n') if BAD.search(l) and not l.lstrip().startswith(('--', '/-', '`'))]
    assert not bad, (name, bad[:10])


def body(src, start):
    s = text(src)
    a = s.index(start)
    b = s.rindex('end LeanProofs.GowersSzemeredi')
    return s[a:b]


PRE = 'set_option autoImplicit false\nnoncomputable section\nnamespace LeanProofs.GowersSzemeredi\n\n'


def write(dst, head, b):
    check(dst, b)
    (GS / f'{dst}.lean').write_text(head + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')
    print('wrote', dst)


# --- Modulus
b = rename(body('Proofs18CoverModulusFejerQ', '/-! ### The parameters -/'))
write('Proofs18CoverModulusFejerS', '''import GowersSzemeredi.Proofs18CoverExponentsFejer
import GowersSzemeredi.Proofs18TightClassesFejerS
import GowersSzemeredi.Proofs18FejerEnvelopeBaseQ

/-! **The Section 18 step at the class degree `sDeg`** (Notes L.16j), part 1:
`GenParamsS` and the scale conditions. Generated from
`Proofs18CoverModulusFejerQ`, with the covers at `uDegS l = 2^sDeg l`,
`sDeg l = 4·2^l + 3(l+4)² + 32` (`polyCoverAt_classS`, from the small
dimension-two seed). -/
''' + PRE + '''/-- The log-degree of the class covers from the small dimension-two seed. -/
def sDeg (k : Nat) : Nat := 4 * 2 ^ k + 3 * (k + 4) ^ 2 + 32

theorem uDegS_eq (l : Nat) : uDegS l = 2 ^ sDeg l := rfl

theorem sDeg_mono {l k : Nat} (hl : l ≤ k) : sDeg l ≤ sDeg k := by
  unfold sDeg
  have h1 : 2 ^ l ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hl
  have h2 : (l + 4) ^ 2 ≤ (k + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem uDegS_le_pow {l k : Nat} (hl : l ≤ k) : uDegS l ≤ 2 ^ sDeg k := by
  rw [uDegS_eq]; exact Nat.pow_le_pow_right (by norm_num) (sDeg_mono hl)

''', b)

# --- Density
s = text('Proofs18CoverDensityFejerQ')
b = s[s.index('variable {alpha : Real}'):s.rindex('end LeanProofs.GowersSzemeredi')]
OLD_HM = '''  have hm : fixDeg k ≤ rhoDegQ k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by
    have h1 := fixDeg_le_two_fixDegQ k
    have h2 := fixDegQ_le_two_qDeg k
    have h3 := le_max_right μV (fixDegQ k)
    omega
  obtain ⟨he0, he8, hei⟩ := GenParams.eta_step (k := k) ha ha2 hd0 hd1 hdi hm
  obtain ⟨hy0, hyle, hyi⟩ := GenParams.yIn_step (k := k) ha ha2 he0 he8 hei (by omega)
'''
NEW_HM = '''  -- the polynomial side condition of `eta_step_small` (the printed `fixDeg k`
  -- would exceed the density degree at class constant `4`)
  have hm : 3 * (k + 4) ^ 2 ≤ rhoDegQ k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by
    have : 3 * (k + 4) ^ 2 ≤ μD := by rw [hμDdef]; unfold qDeg; omega
    omega
  obtain ⟨he0, he8, hei⟩ := GenParams.eta_step_small (k := k) ha ha2 hd0 hd1 hdi hm
  obtain ⟨hy0, hyle, hyi⟩ := GenParams.yIn_step_small (k := k) ha ha2 he0 he8 hei (by omega)
'''
assert OLD_HM in b
b = rename(b.replace(OLD_HM, NEW_HM))
write('Proofs18CoverDensityFejerS', '''import GowersSzemeredi.Proofs18CoverModulusFejerS
import GowersSzemeredi.Proofs18EtaStepSmall

/-! **The Section 18 step at `sDeg`**, part 2: the density envelope (generated
from `Proofs18CoverDensityFejerQ`). The η side condition is the polynomial
`3(k+4)² ≤ m` of `GenParams.eta_step_small`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

''', b)

# --- Exponents
b = rename(body('Proofs18CoverExponentsFejerQ', 'namespace GenParamsQ'))
write('Proofs18CoverExponentsFejerS', '''import GowersSzemeredi.Proofs18CoverDensityFejerS

/-! **The Section 18 step at `sDeg`**, part 3: the width exponents and
thresholds (generated from `Proofs18CoverExponentsFejerQ`). -/
''' + PRE, b)

# --- Headline (steps and recursions generated; closed forms hand-written)
s = text('Proofs18CoverFejerHeadlineQ')
b = s[s.index('/-- The base budget at the class-base term. -/'):s.index('/-! ### Closed forms -/')]
b = rename(b)
tail = (SP / 'headline_s_tail.lean').read_text(encoding='utf-8')
head = (SP / 'headline_s_head.lean').read_text(encoding='utf-8')
write('Proofs18CoverFejerHeadlineS', head + PRE.replace('noncomputable section\n', 'noncomputable section\nopen scoped BigOperators\n'),
      b + tail)
