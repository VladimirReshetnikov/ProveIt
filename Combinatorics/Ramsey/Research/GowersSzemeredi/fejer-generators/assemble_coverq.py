"""Q copies (class degree qDeg, base budget fixDegQ) of the Fejér cover modules."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:100])
        t = t.replace(a, b)
    return t


NAMES = [('rhoDegC_gF', 'rhoDegQ_ge'), ('GenParamsF', 'GenParamsQ'), ('rhoDegF', 'rhoDegQ'),
         ('densDegF', 'densDegQ'), ('expDegF', 'expDegQ'), ('threshDegF', 'threshDegQ'),
         ('rho1_inv_leF', 'rho1_inv_leQ'), ('nestExp_inv_leF', 'nestExp_inv_leQ'),
         ('yIn_boundsF', 'yIn_boundsQ'), ('spectrum_exps_inv_leF', 'spectrum_exps_inv_leQ'),
         ('slice_exps_inv_leF', 'slice_exps_inv_leQ'), ('Eloc_inv_leF', 'Eloc_inv_leQ'),
         ('MReq_le_expF', 'MReq_le_expQ'), ('Tloc_le_expF', 'Tloc_le_expQ'),
         ('coverPrec_gen_bounds_fejer', 'coverPrec_gen_bounds_fejerQ'),
         ('budget_gen_bounds_fejer', 'budget_gen_bounds_fejerQ'), ('T2_gen_bounds_fejer', 'T2_gen_bounds_fejerQ'),
         ('delta_gen_bounds_fejer', 'delta_gen_bounds_fejerQ'), ('baseCF_recipPowerLB', 'baseCFQ_recipPowerLB'),
         ('k_succ_le_two_pow_fixDeg', 'k_succ_le_two_pow_fixDegQ'),
         ('uDeg23', 'uDegQ'), ('polyCoverAt_class23', 'polyCoverAt_classQ'),
         # headline
         ('envStepFTx_le_tight', 'envStepQTx_le_tight'), ('envStepFTx', 'envStepQTx'),
         ('envBound_stepFx', 'envBound_stepQx'), ('polyEnvBound_stepF', 'polyEnvBound_stepQ'),
         ('envStepF', 'envStepQ'), ('polyGenMuF_succ', 'polyGenMuQ_succ'), ('polyGenMuF', 'polyGenMuQ'),
         ('genMuXF_succ', 'genMuXQ_succ'), ('genMuXF', 'genMuXQ'), ('polyEnvBound_allF', 'polyEnvBound_allQ'),
         ('envBound_allXF', 'envBound_allXQ'), ('tightHyp_of_profiles_fejer', 'tightHyp_of_profiles_fejerQ'),
         ('tightMu0', 'tightMu0Q')]


def common(t):
    # the eta side condition keeps the printed fixDeg (eta_step is instantiated at the true k)
    t = t.replace('  have hm : fixDeg k ≤ rhoDegF k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by omega\n',
                  '  have hm : fixDeg k ≤ rhoDegF k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by\n'
                  '    have h1 := fixDeg_le_two_fixDegQ k\n'
                  '    have h2 := fixDegQ_le_two_qDeg k\n'
                  '    have h3 := le_max_right μV (fixDegQ k)\n'
                  '    omega\n')
    t = t.replace('    unfold fixDeg; have := Nat.lt_two_pow_self (n := P.k + 5); omega\n',
                  '    have := five_k_le_fixDegQ P.k; omega\n')
    t = t.replace('    refine ⟨by have := hEE.1; positivity, ?_⟩\n',
                  '    refine ⟨div_pos (mul_pos hBx hEE.1) (by norm_num), ?_⟩\n')
    t = t.replace('''  have p3 := pw_mul' hX (inv_pos.mpr hBx0).le (by positivity) hBx p2
  have p4 := pw_mul hX (by norm_num) (by positivity) h32 p1
  have p5 := pw_mul' hX (by positivity) (by positivity) p4 p3
''', '''  have hEE0 : 0 ≤ (P.Eth alpha)⁻¹ * (P.Ec alpha)⁻¹ :=
    mul_nonneg (inv_pos.mpr hEth0).le (inv_pos.mpr hEc0).le
  have hNE0 : 0 ≤ (P.NestExp alpha)⁻¹ * (P.Em alpha)⁻¹ :=
    mul_nonneg (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le
  have p3 := pw_mul' hX (inv_pos.mpr hBx0).le hEE0 hBx p2
  have p4 := pw_mul hX (by norm_num) hNE0 h32 p1
  have p5 := pw_mul' hX (mul_nonneg (by norm_num) hNE0) (mul_nonneg (inv_pos.mpr hBx0).le hEE0) p4 p3
''')
    for a, b in [
        ('    rw [le_div_iff₀ (by positivity)]\n    have : R ^ 3 ≤ 1 := pow_le_one₀ hR0.le hR1\n'
         '    have : z * R ^ 3 ≤ 1 / 2 * 1 := mul_le_mul hz1 this (by positivity) (by norm_num)\n',
         '    rw [le_div_iff₀ (mul_pos hz0 (pow_pos hR0 3))]\n    have : R ^ 3 ≤ 1 := pow_le_one₀ hR0.le hR1\n'
         '    have : z * R ^ 3 ≤ 1 / 2 * 1 := mul_le_mul hz1 this (pow_pos hR0 3).le (by norm_num)\n'),
        ('  have e1 := ex_rpow hX h8z1 h8z (by positivity) hBe\n  have e2 := ex_rpow hX h4zr1 h4zr (by positivity) hBe\n'
         '  have e3 := ex_rpow hX h16z1 h16z (by positivity) hBe2\n',
         '  have e1 := ex_rpow hX h8z1 h8z (div_nonneg zero_le_one hBpos.le) hBe\n'
         '  have e2 := ex_rpow hX h4zr1 h4zr (div_nonneg zero_le_one hBpos.le) hBe\n'
         '  have e3 := ex_rpow hX h16z1 h16z (div_nonneg zero_le_two hBpos.le) hBe2\n'),
        ('    exact pw_mul hX (by norm_num) (by positivity) (hX.trans (pw_X hX _)) p1\n',
         '    exact pw_mul hX (by norm_num) (mul_nonneg (inv_pos.mpr hN0).le (inv_pos.mpr hEm0).le)\n'
         '      (hX.trans (pw_X hX _)) p1\n'),
        ('    show 0 < P.NestExp alpha * (P.Em alpha / 2)\n    positivity\n',
         '    show 0 < P.NestExp alpha * (P.Em alpha / 2)\n    exact mul_pos hN0 (half_pos hEm0)\n'),
        ('      rw [hF, div_le_div_iff₀ (by positivity) hEl0]; nlinarith\n',
         '      rw [hF, div_le_div_iff₀ (mul_pos (by norm_num) hEl0) hEl0]; nlinarith\n'),
        ('    max_le (Real.one_le_exp (by positivity)) h64\n',
         '    max_le (Real.one_le_exp (pow_nonneg (by linarith) _)) h64\n')]:
        if a in t:
            t = t.replace(a, b)
    t = t.replace('    show 0 < familyRecExp k P.p _ / 2; positivity\n',
                  '    show 0 < familyRecExp k P.p _ / 2; exact half_pos this\n')
    t = re.sub(r'\bfixDeg\b(?! k ≤ rhoDegF)', 'fixDegQ', t)
    t = t.replace('fixDegQ_le_two_fixDegQ', 'fixDeg_le_two_fixDegQ')     # undo inside the inserted lines
    t = t.replace('have h1 := fixDegQ_le_two_fixDegQ k', 'have h1 := fixDeg_le_two_fixDegQ k')
    t = t.replace('GenParams.half_inv_le P.k ', 'GenParams.half_inv_le (P.k - 1) ')
    t = t.replace('GenParams.half_inv_le k ', 'GenParams.half_inv_le (k - 1) ')
    t = re.sub(r'23 \* 2 \^ (P\.k|k|l)\b', r'qDeg \1', t)
    t = t.replace('Nat.pow_le_pow_right (by norm_num)\n    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hl))',
                  'uDegQ_le_pow hl')
    for a, b in NAMES:
        t = re.sub(r'\b' + a + r'\b', b, t)
    return t


BAD = re.compile(r'GenParamsF|uDeg23|class23|\b23 \*|(?:rhoDeg|densDeg|expDeg|threshDeg|envStep|genMuX|polyGenMu|'
                 r'_inv_le|_bounds|_exps_inv_le|_le_exp)\w*F\b|gen_bounds_fejer\b|\bfixDeg\b(?! k ≤ rhoDeg)')


def check(name, t):
    bad = [l.strip()[:140] for l in t.split('\n') if BAD.search(l)
           and not re.search(r'zeta_gen_bounds_fejer|lemma156_gen_le_fejer|single_piece_inverse_step_global_cover_fejer|'
                             r'singlePiece\w*F\b|SinglePiece\w*F\b|baseCF\b|fejerThetaOne|polyGenMuF|cover_fejer|'
                             r'single_piece_frequency_box_global_cover_fejer', l)]
    assert not bad, (name, bad[:12])


def emit(src, dst, head, cut_start, cut_end=None):
    s = text(src)
    a = s.index(cut_start)
    b = s.rindex('end LeanProofs.GowersSzemeredi') if cut_end is None else s.index(cut_end)
    body = common(s[a:b])
    check(dst, body)
    (GS / f'{dst}.lean').write_text(head + body + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')


PRE = 'set_option autoImplicit false\nnoncomputable section\nnamespace LeanProofs.GowersSzemeredi\n\n'
emit('Proofs18CoverModulusFejer', 'Proofs18CoverModulusFejerQ',
     '''import GowersSzemeredi.Proofs18CoverExponentsFejer
import GowersSzemeredi.Proofs18TightClassesFejerQ
import GowersSzemeredi.Proofs18FejerEnvelopeBaseQ

/-! **The Section 18 step at the class degree `qDeg` and the base budget
`fixDegQ`** (Notes L.16i), part 1: `GenParamsQ` and the scale conditions.
Generated from `Proofs18CoverModulusFejer`, with the covers at `uDegQ`. -/
''' + PRE + '''/-- The log-degree of the class covers with additive slack. -/
def qDeg (k : Nat) : Nat := 14 * 2 ^ k + 3 * (k + 4) ^ 2 + 2

theorem uDegQ_eq (l : Nat) : uDegQ l = 2 ^ qDeg l := rfl

theorem qDeg_mono {l k : Nat} (hl : l ≤ k) : qDeg l ≤ qDeg k := by
  unfold qDeg
  have h1 : 2 ^ l ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hl
  have h2 : (l + 4) ^ 2 ≤ (k + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem uDegQ_le_pow {l k : Nat} (hl : l ≤ k) : uDegQ l ≤ 2 ^ qDeg k := by
  rw [uDegQ_eq]; exact Nat.pow_le_pow_right (by norm_num) (qDeg_mono hl)

theorem fixDegQ_le_two_qDeg (k : Nat) : fixDegQ k ≤ 2 * qDeg k := by
  unfold fixDegQ fixDeg qDeg
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · rw [show k - 1 + 5 = k + 4 by omega, show k + 4 = k + 4 by rfl]
    have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
    have : 16 ≤ 3 * (k + 4) ^ 2 := by nlinarith
    omega

''', '/-! ### The parameters -/')
emit('Proofs18CoverDensityFejer', 'Proofs18CoverDensityFejerQ',
     '''import GowersSzemeredi.Proofs18CoverModulusFejerQ

/-! **The Section 18 step at `(qDeg, fixDegQ)`**, part 2: the density envelope
(generated from `Proofs18CoverDensityFejer`). -/
''' + PRE, 'variable {alpha : Real}')
emit('Proofs18CoverExponentsFejer', 'Proofs18CoverExponentsFejerQ',
     '''import GowersSzemeredi.Proofs18CoverDensityFejerQ

/-! **The Section 18 step at `(qDeg, fixDegQ)`**, part 3: the width exponents
and thresholds (generated from `Proofs18CoverExponentsFejer`). -/
''' + PRE, 'namespace GenParamsF')
print('ok')
