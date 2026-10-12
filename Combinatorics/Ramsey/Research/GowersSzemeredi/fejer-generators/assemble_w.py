"""W copies (polynomial base budget pDeg, polynomial family constants, U threshold) of the T chain (Notes L.16m)."""
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


TOWER = '(hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))'
POLY = '(hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))'

RENAMES = ['GenParamsT:GenParamsW', 'coverPrec_gen_bounds_fejerT:coverPrec_gen_bounds_fejerW',
           'rhoDegT_ge:rhoDegW_ge', 'rhoDegT:rhoDegW', 'rho1_inv_leT:rho1_inv_leW', 'nestExp_inv_leT:nestExp_inv_leW',
           'densDegT:densDegW', 'yIn_boundsT:yIn_boundsW', 'expDegT:expDegW',
           'spectrum_exps_inv_leT:spectrum_exps_inv_leW', 'slice_exps_inv_leT:slice_exps_inv_leW',
           'Eloc_inv_leT:Eloc_inv_leW', 'threshDegT:threshDegW', 'MReq_le_expT:MReq_le_expW',
           'Tloc_le_expT:Tloc_le_expW', 'tightMu0T:tightMu0W', 'envStepTTx:envStepWTx', 'envStepT:envStepW',
           'polyEnvBound_stepT:polyEnvBound_stepW', 'envBound_stepTx:envBound_stepWx',
           'tightHyp_of_profiles_fejerT:tightHyp_of_profiles_fejerW', 'polyGenMuE_succ:polyGenMuW_succ',
           'polyGenMuE:polyGenMuW', 'polyEnvBound_allE:polyEnvBound_allW', 'genMuXT_succ:genMuXW_succ',
           'genMuXT:genMuXW', 'envBound_allXT:envBound_allXW',
           # the budget
           'fixDegQ:pDeg', 'budget_gen_bounds_fejerQ:budget_gen_bounds_fejerW', 'T2_gen_bounds_fejerQ:T2_gen_bounds_fejerW',
           'delta_gen_bounds_fejerQ:delta_gen_bounds_fejerW', 'baseCFQ_recipPowerLB:baseCFW_recipPowerLB',
           'five_k_le_fixDegQ:five_k_le_pDeg', 'k_succ_le_two_pow_fixDegQ:k_succ_le_two_pow_pDeg',
           'tightMuV:tightMuW', 'genMuK:genMuKW']


def rename(t):
    for p in RENAMES:
        a, b = p.split(':')
        t = re.sub(r'\b' + a + r'\b', b, t)
    # the degree-generic count and half-inverse lemmas
    t, n = re.subn(r'uCount_scale_le (\([^\n]*?)hX (H\.hV|hV) (H\.hVμ|hVμ) (H\.hμ0|hμ0)',
                   r'uCount_scale_le_deg \1hX \2 \3 (seven_le_pDeg _) \4', t)
    t = re.sub(r'GenParams\.half_inv_le \((P\.k|k) - 1\)', r'GenParams.half_inv_le_deg (pDeg \1)', t)
    assert 'uCount_scale_le ' not in t and 'half_inv_le (' not in t
    return t


BAD = re.compile(r'\b(?!uDegT\b|uDegT_)(?:fixDegQ|fixDeg|GenParamsT|\w+T_ge|\w+_inv_leT|\w+DegT|\w+_expT|tightMu0T|envStepT\w*|'
                 r'polyGenMuE\w*|genMuXT\w*|\w+_allX?[TE]|\w+_stepTx?|tightMuV|genMuK|\w+fejerT|\w+fejerQ|baseCFQ\w*)\b')


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
s = text('Proofs18CoverModulusFejerT')
b = rename(s[s.index('/-! ### The parameters -/'):s.rindex('end LeanProofs.GowersSzemeredi')])
write('Proofs18CoverModulusFejerW', '''import GowersSzemeredi.Proofs18CoverModulusFejerT
import GowersSzemeredi.Proofs18FejerEnvelopeBaseW

/-! **The Section 18 step at the polynomial base budget** (Notes L.16m),
part 1: `GenParamsW` and the scale conditions. Generated from
`Proofs18CoverModulusFejerT`, with `fixDegQ` replaced by `pDeg k = 5k + 21`. -/
''' + PRE, b)

# --- Density
s = text('Proofs18CoverDensityFejerT')
b = s[s.index('variable {alpha : Real}'):s.rindex('end LeanProofs.GowersSzemeredi')]
b = sub(b, [('''    have h1 := sq_le_fixDegQ k
    have h2 := le_max_right μV (fixDegQ k)
    have h3 : 17 ≤ μD := by rw [hμDdef]; exact seventeen_le_tDeg k
''', '''    have h1 := sq_le_three_tDeg k
    have h2 := le_max_right μV (fixDegQ k)
    have h3 : μD = tDeg k := hμDdef
    have h5 : fixDegQ k = 5 * k + 21 := rfl
'''), ('  -- the polynomial side condition of `eta_step_small`, inside the base budget\n',
       '  -- the polynomial side condition of `eta_step_small`, from the class degree\n')])
b = rename(b)
write('Proofs18CoverDensityFejerW', '''import GowersSzemeredi.Proofs18CoverModulusFejerW
import GowersSzemeredi.Proofs18EtaStepSmall

/-! **The Section 18 step at the polynomial base budget**, part 2: the density
envelope (generated from `Proofs18CoverDensityFejerT`). The η side condition
`3(k+4)²` now comes from the class degree (`sq_le_three_tDeg`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

''', b)

# --- Exponents (with the polynomial Bohr radius in MReq / Tloc)
s = text('Proofs18CoverExponentsFejerT')
b = s[s.index('namespace GenParamsT'):s.rindex('end LeanProofs.GowersSzemeredi')]
b = sub(b, [
    ('def threshDegT (k μ0 μK : Nat) : Nat := max (expDegT k μ0 μK + 4) (2 ^ (k + 6) + 5)',
     'def threshDegT (k μ0 μK : Nat) : Nat := max (expDegT k μ0 μK + 4) (2 ^ (k + 4) + 5 * k + 25)'),
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
assert 'k + 6' not in b, [l for l in b.split('\n') if 'k + 6' in l]
b = rename(b)
write('Proofs18CoverExponentsFejerW', '''import GowersSzemeredi.Proofs18CoverDensityFejerW
import GowersSzemeredi.Proofs18CoverFejerHeadlineU

/-! **The Section 18 step at the polynomial base budget**, part 3: the width
exponents and thresholds (generated from `Proofs18CoverExponentsFejerT`, with
the polynomial Bohr radius `zeta_gen_bounds_fejer5` of
`Proofs18CoverFejerHeadlineU` in the requirement on `m`). -/
''' + PRE, b)

# --- Headline (steps and recursions generated; tightHyp and closed forms hand-written)
s = text('Proofs18CoverFejerHeadlineT')
b = s[s.index('/-- The base budget at the class-base term. -/'):s.index('/-! ### Closed forms -/')]
i = b.index('/-- The standing hypotheses at the tight base budget. -/')
j = b.index('/-- The Theorem 18.1 envelope at the tight base budget. -/')
b = b[:i] + (SP / 'headline_w_hyp.lean').read_text(encoding='utf-8') + b[j:]
assert TOWER in b
b = b.replace(TOWER, POLY)
b = rename(b)
b = b.replace('/-- The base budget at the class-base term. -/', '/-- The polynomial base budget. -/')
head = (SP / 'headline_w_head.lean').read_text(encoding='utf-8')
tail = (SP / 'headline_w_tail.lean').read_text(encoding='utf-8')
write('Proofs18CoverFejerHeadlineW', head + PRE.replace('noncomputable section\n', 'noncomputable section\nopen scoped BigOperators\n'),
      b + tail)
