"""Fejér copies of Proofs18CoverModulus / CoverDensity / CoverExponents (class degree uDeg23)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


def cut(t, start, end_marker):
    a = t.index(start)
    b = t.index(end_marker, a + len(start))
    return t[:a] + t[b:]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:100])
        t = t.replace(a, b)
    return t


def T1(K):
    return f'fejerThetaOne alpha (alpha / 2) {K}'


def FB(K):
    return f'(fejerThetaOne_bounds {K} ha (by linarith) (half_pos ha) (by linarith))'


COVERW = {'coverRho1': 'coverRho1W', 'coverCount': 'coverCountW', 'coverExp': 'coverExpW',
          'coverRemWidth': 'coverRemWidthW', 'coverRemWidth_powerLB': 'coverRemWidthW_powerLB',
          'coverCount_pos': 'coverCountW_pos', 'coverExp_pos_le': 'coverExpW_pos_le',
          'coverRho1_pos_le': 'coverRho1W_pos_le'}

# names defined in the copied modules that end in `C` are renamed to end in `F`
C_NAMES = ['GenParamsC', 'rhoDegC', 'rhoDegC_ge', 'densDegC', 'rho1_inv_leC', 'nestExp_inv_leC',
           'yIn_boundsC', 'expDegC', 'spectrum_exps_inv_leC', 'slice_exps_inv_leC', 'Eloc_inv_leC',
           'threshDegC', 'MReq_le_expC', 'Tloc_le_expC',
           'singlePieceGlobalDensityC', 'singlePieceGlobalQmaxC', 'singlePieceGlobalWidthC',
           'SinglePieceGlobalScaleC', 'singlePieceEtaC', 'SinglePieceModulusConditionsC',
           'singlePieceGlobalC']
LEMMAS = ['budget_gen_bounds', 'T2_gen_bounds', 'delta_gen_bounds', 'zeta_gen_bounds', 'lemma156_gen_le',
          'single_piece_inverse_step_global_cover', 'coverPrec_gen_bounds']


def common(t):
    t = t.replace('uDeg68', 'uDeg23').replace('68 * 2 ^', '23 * 2 ^')
    t = t.replace('`globalBudget α (α/2) k`', '`globalBudgetW θ₁′ k`')
    for a in ['coverCount', 'coverRho1', 'coverExp', 'coverPrec', 'globalBudget', 'globalTheta2']:
        for _ in range(3):
            t = re.sub(r'(unfold [^\n]*)\b' + a + r'\b', lambda m, a=a: m.group(1) + a + 'W', t)
    t = t.replace('(GenParams.std P.V (uDeg23 k) P.k P.K P.p P.μ0).baseC alpha (P.ThS alpha)',
                  'baseCF P.V (uDeg23 k) P.k alpha (P.ThS alpha)')
    t = re.sub(r'GenParams\.baseC_recipPowerLB \(D := uDeg23 k\) \(K := P\.K\) \(p := P\.p\)',
               'baseCF_recipPowerLB (D := uDeg23 k) (k := k)', t)
    for K in ['P.k', 'k']:
        Kre = re.escape(K)
        t = t.replace(f'section16ThetaTwo_pos_le (gamma := alpha / 2) {K} ha ha1 hg hg1',
                      f'section16ThetaTwo_pos_le_with {FB(K)}.1 {FB(K)}.2')
        t = t.replace(f'section16_theta_delta_bounds {K} ha ha1 hg hg1',
                      f'section16_theta_delta_bounds_with {FB(K)}.1 {FB(K)}.2')
        t = t.replace(f'section16Zeta_pos_le_half {K} ha ha1 hg hg1',
                      f'tightZeta_pos_le_half {FB(K)}.1 (by linarith [{FB(K)}.2])')
        t = t.replace(f'section16Zeta_pos_le_half {K} ha (by linarith) (half_pos ha) (by linarith)',
                      f'tightZeta_pos_le_half {FB(K)}.1 (by linarith [{FB(K)}.2])')
        t = t.replace(f'coverPrec_pos_le alpha (alpha / 2) {K} ha (by linarith) (half_pos ha)\n    (by linarith)',
                      f'coverPrecW_pos_le ({T1(K)}) {K} {FB(K)}.1 {FB(K)}.2')
        # the cover objects: `name args alpha (alpha / 2) K` -> `nameW args (θ₁′) (alpha / 2) K`
        for a, b in COVERW.items():
            t = re.sub(r'\b' + a + r'\b((?:(?!\balpha \(alpha / 2\)).){0,160}?) alpha \(alpha / 2\)(\s+)' + Kre +
                       r'\b', lambda m, b=b, K=K: f'{b}{m.group(1)} ({T1(K)}) (alpha / 2){m.group(2)}{K}', t,
                       flags=re.S)
        # positivity facts after the objects
        t = re.sub(r'coverRho1W_pos_le (_ \(fun l g t s _ _ => one_le_uCount P\.V \(uDeg23 l\) g t s\)) \(' +
                   re.escape(T1(K)) + r'\) \(alpha / 2\)(\s+)' + Kre + r' ha (?:ha1|\(by linarith\)) (?:hg|\(half_pos ha\)) (?:hg1|\(by linarith\))',
                   lambda m, K=K: f'coverRho1W_pos_le {m.group(1)} ({T1(K)}) (alpha / 2){m.group(2)}{K} {FB(K)}.1 {FB(K)}.2',
                   t)
        t = re.sub(r'\bcoverPrec alpha \(alpha / 2\) ' + Kre + r'\b', f'coverPrecW ({T1(K)}) {K}', t)
        t = re.sub(r'\bglobalBudget alpha \(alpha / 2\) ' + Kre + r'\b', f'globalBudgetW ({T1(K)}) {K}', t)
        t = re.sub(r'\bglobalTheta2 alpha \(alpha / 2\) ' + Kre + r'\b', f'globalTheta2W ({T1(K)})', t)
        t = re.sub(r'\bsection16Zeta alpha \(alpha / 2\) ' + Kre + r'\b', f'tightZeta ({T1(K)} / 4)', t)
        t = re.sub(r'\bsection16ThetaOne alpha \(alpha / 2\) ' + Kre + r'\b', T1(K), t)
    for a in ['coverCount', 'coverRho1', 'coverExp', 'coverPrec', 'globalBudget', 'globalTheta2']:
        t = re.sub(r'(unfold [^\n]*)\b' + a + r'\b', lambda m, a=a: m.group(1) + a + 'W', t)
        t = re.sub(r'(unfold [^\n]*)\b' + a + r'\b', lambda m, a=a: m.group(1) + a + 'W', t)
    t = t.replace('lemma156ExplicitThreshold', 'fejerProductThreshold')
    for a in C_NAMES:
        t = re.sub(r'\b' + a + r'\b', a[:-1] + 'F', t)
    for a in LEMMAS:
        t = re.sub(r'\b' + a + r'\b', a + '_fejer', t)
    return t


BAD = re.compile(r'section16ThetaOne|section16Zeta\b|section16Zeta_|lemma156Explicit|lemma156_gen_le\b|\bglobalBudget\b|\bglobalTheta2\b|'
                 r'\bcoverRho1\b|\bcoverCount\b|\bcoverExp\b|\bcoverPrec\b|\bcoverRemWidth\b|uDeg68|\b68\b|'
                 r'GenParamsC|GenParams\.std|GenParams\.baseC|coverRho1_pos_le|coverPrec_pos_le|'
                 r'section16ThetaTwo_pos_le\b|section16_theta_delta_bounds\b|\w+C\b(?<!\bF)')
ALLOW_C = {'IsMultilinearC'}


def check(name, t):
    bad = []
    for l in t.split('\n'):
        for m in BAD.finditer(l):
            w = m.group(0)
            if re.fullmatch(r'\w+C', w) and (w in ALLOW_C or w in {'ModAP', 'C'} or not w[0].isalpha()):
                continue
            bad.append((w, l.strip()[:150]))
    # names ending in C that are fine (generic)
    bad = [b for b in bad if not re.fullmatch(r'\w*(?:recipPowerLB|NoC|HC)', b[0])]
    assert not bad, (name, bad[:20])


# ---- CoverModulus
s = text('Proofs18CoverModulus')
body = s[s.index('/-! ### The parameters -/'):s.rindex('end LeanProofs.GowersSzemeredi')]
body = common(body)
check('Modulus', body)
MOD_HEAD = '''import GowersSzemeredi.Proofs18CoverModulus
import GowersSzemeredi.Proofs18SinglePieceCoverInverseFejer
import GowersSzemeredi.Proofs18TightClassesFejer
import GowersSzemeredi.Proofs18FejerEnvelopeBase

/-! **The scale conditions of the Section 18 step under the Fejér θ₁**
(Notes L.16d).

The Fejér instance of `Proofs18CoverModulus`, generated from it by a script
with a guard that no printed parameter survives: `GenParamsF` is
`GenParamsC` with the budget, `θ₂/2`, `ρ₁`, `δ`, the remainder width and the
radius at the Fejér density `θ₁′ = fejerThetaOne α (α/2) k`
(`globalBudgetW`, `globalTheta2W`, `coverRho1W`, `coverRemWidthW`,
`tightZeta (θ₁′/4)`), the Lemma 15.6 threshold `fejerProductThreshold`, and
the class covers at degree `uDeg23 l` in place of `uDeg68 l`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The cover remainder width at density `t1` -/

theorem coverExpW_pos_le (Eb : Nat → Real → Real → Real → Real)
    (hEb : ∀ l g t s, 0 < Eb l g t s ∧ Eb l g t s ≤ 1) (t1 gamma : Real) (k : Nat) :
    0 < coverExpW Eb t1 gamma k ∧ coverExpW Eb t1 gamma k ≤ 1 := by
  unfold coverExpW
  have hf : ∀ e : Fin k → Bool,
      0 < Eb (section16VertexDirections e).card gamma (globalBudgetW t1 k)
          (coverPrecW t1 k) / 16 ^ (k + 1 - (section16VertexDirections e).card) ∧
        Eb (section16VertexDirections e).card gamma (globalBudgetW t1 k)
          (coverPrecW t1 k) / 16 ^ (k + 1 - (section16VertexDirections e).card) ≤ 1 := by
    intro e
    obtain ⟨h0, h1⟩ := hEb (section16VertexDirections e).card gamma (globalBudgetW t1 k)
      (coverPrecW t1 k)
    have h16 : (1 : Real) ≤ 16 ^ (k + 1 - (section16VertexDirections e).card) :=
      one_le_pow₀ (by norm_num)
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    linarith
  refine ⟨Finset.prod_pos fun e _ => (hf e).1, ?_⟩
  calc _ ≤ ∏ _e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true), (1 : Real) :=
        Finset.prod_le_prod (fun e _ => (hf e).1.le) fun e _ => (hf e).2
    _ = 1 := by simp

/-- The remainder width is `N^coverExpW`, with no threshold. -/
theorem coverRemWidthW_powerLB (Eb : Nat → Real → Real → Real → Real) (t1 gamma : Real)
    (k : Nat) :
    WidthPowerLB (fun L => coverRemWidthW Eb t1 gamma k L) (coverExpW Eb t1 gamma k) 1 :=
  fun _ _ => Nat.le_ceil _

'''
(GS / 'Proofs18CoverModulusFejer.lean').write_text(MOD_HEAD + body + 'end LeanProofs.GowersSzemeredi\n',
                                                   encoding='utf-8', newline='\n')

# ---- CoverDensity
s = text('Proofs18CoverDensity')
body = s[s.index('variable {alpha : Real}'):s.rindex('end LeanProofs.GowersSzemeredi')]
body = cut(body, '/-- `3^(k+1) ≤ X^(2^a)` once `k + 2 ≤ a`. -/', 'namespace GenParamsC')
body = common(body)
check('Density', body)
DEN_HEAD = '''import GowersSzemeredi.Proofs18CoverDensity
import GowersSzemeredi.Proofs18CoverModulusFejer

/-! **The density envelope of the Section 18 step under the Fejér θ₁**
(Notes L.16d).

The Fejér instance of `Proofs18CoverDensity` (generated; no printed parameter
survives). The log-degrees are the corpus's with the class degree
`23·2^k` in place of `68·2^k`:
* `rhoDegF k μ₀ = max(23·2^k + μ₀ + 3, fixDeg k + 1) + k` (`rho1_inv_leF`);
* `densDegF k μ₀ = rhoDegF k μ₀ + 2·(23·2^k) + 13` (`yIn_boundsF`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

'''
(GS / 'Proofs18CoverDensityFejer.lean').write_text(DEN_HEAD + body + 'end LeanProofs.GowersSzemeredi\n',
                                                   encoding='utf-8', newline='\n')

# ---- CoverExponents
s = text('Proofs18CoverExponents')
body = s[s.index('namespace GenParamsC'):s.rindex('end LeanProofs.GowersSzemeredi')]
body = common(body)
check('Exponents', body)
EXP_HEAD = '''import GowersSzemeredi.Proofs18CoverExponents
import GowersSzemeredi.Proofs18CoverDensityFejer

/-! **The width exponents and thresholds of the Section 18 step under the
Fejér θ₁** (Notes L.16d).

The Fejér instance of `Proofs18CoverExponents` (generated; no printed
parameter survives): `expDegF`, `threshDegF` and their bounds, with the class
degree `23·2^k` in place of `68·2^k`. The fixed parameters enter through
`Proofs18FejerEnvelopeBase` at the printed exponents. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

'''
(GS / 'Proofs18CoverExponentsFejer.lean').write_text(EXP_HEAD + body + 'end LeanProofs.GowersSzemeredi\n',
                                                     encoding='utf-8', newline='\n')
print('ok')
