"""Proofs16PolynomialFejerJ: Theorem 16.2 at the Z classes and Corollary 16.11 with joint slices."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


def sub(t, pairs):
    for a, b in pairs:
        assert t.count(a) == 1, ('count', t.count(a), a[:120])
        t = t.replace(a, b)
    return t


pf = text('Proofs16PolynomialFejer')
a = pf.index('theorem singlePieceEtaF_le_density')
b = pf.index('\ntheorem ', a + 10)
b2 = pf.index('\n/--', a + 10)
lem = pf[a:min(b, b2)].rstrip() + '\n\n'
lem = lem.replace('singlePieceEtaF_le_density', 'singlePieceEtaFJ_le_density')
lem = re.sub(r'\bsinglePieceEtaF\b', 'singlePieceEtaFJ', lem)
lem = re.sub(r'\bsinglePieceGlobalDensityF\b', 'singlePieceGlobalDensityFJ', lem)

x = text('Proofs16PolynomialFejerX')
body = x[x.index('theorem uDegX_le_uDeg68'):x.rindex('end LeanProofs.GowersSzemeredi')]
body = sub(body, [
    # the class degree to dimension 14
    ('''  rcases Nat.lt_or_ge k 13 with h | h
  · interval_cases k <;> decide
  · rw [tDegX_eq_of_ge h]
    have h1 := sq_le_two_pow_four k (by omega)''',
     '''  rcases Nat.lt_or_ge k 15 with h | h
  · interval_cases k <;> decide
  · rw [tDegZ_eq_of_ge h]
    have h1 := sq_le_two_pow_four k (by omega)'''),
    # the exponent degree
    ('''/-- The exponent degree at `(tDegX, tightMu0X)`. -/
theorem expDegX_tight_le (k : Nat) :
    GenParamsX.expDegX k (tightMu0X k) (genMuKX k) + 3 ≤ 3 * tDegX k + 6 * k + 38 := by
  unfold GenParamsX.expDegX GenParamsX.rhoDegX tightMu0X tightMuW genMuKX pDeg
  have := seventeen_le_tDegX k
  have hkt : k ≤ tDegX k := by
    rcases Nat.lt_or_ge k 13 with h | h
    · interval_cases k <;> decide
    · rw [tDegX_eq_of_ge h]
      have : k ≤ (k + 4) ^ 2 := by nlinarith
      omega
  simp only [max_def]
  split_ifs <;> omega''',
     '''/-- The exponent degree of the joint-slice step at `(tDegZ, tightMu0Z)`: two
class degrees (`3·tDegX` at the X step). -/
theorem expDegJ_tight_le (k : Nat) :
    GenParamsJ.expDegJ k (tightMu0Z k) (genMuKZ k) + 3 ≤ 2 * tDegZ k + 7 * k + 38 := by
  unfold GenParamsJ.expDegJ GenParamsJ.rhoDegJ tightMu0Z tightMuW genMuKZ pDeg
  simp only [max_def]
  split_ifs <;> omega'''),
    ('''    show GenParamsX.rhoDegX k (tightMu0X k) + 2 * (tDegX k) + 12 ≤
      GenParamsX.expDegX k (tightMu0X k) (genMuKX k) + 3
    unfold GenParamsX.expDegX
    have := le_max_left (GenParamsX.rhoDegX k (tightMu0X k) + 2 * (tDegX k) + 9)
      (max (GenParamsX.rhoDegX k (tightMu0X k) + tDegX k + k + 7) (genMuKX k + 2))''',
     '''    show GenParamsJ.rhoDegJ k (tightMu0Z k) + tDegZ k + 10 ≤
      GenParamsJ.expDegJ k (tightMu0Z k) (genMuKZ k) + 3
    unfold GenParamsJ.expDegJ
    have := le_max_left (GenParamsJ.rhoDegJ k (tightMu0Z k) + tDegZ k + 9)
      (max (GenParamsJ.rhoDegJ k (tightMu0Z k) + tDegZ k + k + 7) (genMuKZ k + 2))'''),
])
RN = [('uDegX_le_uDeg68', 'uDegZ_le_uDeg68'), ('theorem_16_2_polynomial_fejerX_of_profiles', 'theorem_16_2_polynomial_fejerZ_of_profiles'),
      ('corollary_16_11_polynomial_fejerX_of_profiles', 'corollary_16_11_polynomial_fejerJ_of_profiles'),
      ('theorem162At_of_polynomial_fejerX', 'theorem162At_of_polynomial_fejerZ'),
      ('tightHyp_of_profiles_fejerX', 'tightHyp_of_profiles_fejerJ'), ('polyCoverAt_classX', 'polyCoverAt_classZ'),
      ('Eloc_inv_leX', 'Eloc_inv_leJ'), ('yIn_boundsX', 'yIn_boundsJ'), ('GenParamsX', 'GenParamsJ'),
      ('expDegX', 'expDegJ'), ('rhoDegX', 'rhoDegJ'), ('tightMu0X', 'tightMu0Z'), ('genMuKX', 'genMuKZ'),
      ('uDegX', 'uDegZ'), ('tDegX', 'tDegZ'),
      ('singlePieceGlobalDensityF_pos', 'singlePieceGlobalDensityFJ_pos'),
      ('singlePieceGlobalDensityF', 'singlePieceGlobalDensityFJ'), ('singlePieceEtaF_pos', 'singlePieceEtaFJ_pos'),
      ('singlePieceEtaF_le_density', 'singlePieceEtaFJ_le_density'),
      ('single_piece_frequency_box_global_cover_fejer', 'single_piece_frequency_box_global_cover_fejer_joint')]
for p, q in RN:
    body = re.sub(r'\b' + p + r'\b', q, body)
body = body.replace('(polyCoverAt_classZ Kc pc hK1 hp hlem hk).uniform_mono', '(polyCoverAt_classZ Kc pc hK1 hp hlem hk).uniform_mono')
a = body.index('theorem tightMuW_le_tightMuV')
b = body.index('/-- **Theorem 16.2 with polynomial controls', a)
body = body[:a] + body[b:]
bad = [l.strip()[:140] for l in body.split('\n')
       if re.search(r'\b\w*X\b', l) and re.search(r'GenParamsX|tDegX|uDegX|_fejerX\b|classX|tightMu0X|genMuKX', l)]
assert not bad, bad[:8]
HEAD = '''import GowersSzemeredi.Proofs16PolynomialFejerX
import GowersSzemeredi.Proofs18CoverFejerHeadlineJ

/-! **Theorem 16.2 at the classes `tDegZ`, and Corollary 16.11 with joint
slices** (Notes L.16u).

`Proofs16PolynomialFejerX` with the class table exact to dimension `14`
(`polyCoverAt_classZ`) and the frequency box of the joint-slice step
(`single_piece_frequency_box_global_cover_fejer_joint`), generated by
`assemble_polyj.py`:
* `theorem_16_2_polynomial_fejerZ_of_profiles`: graph count
  `max(1, (4V/(γθρ))^uDegZ k)`, `log₂ uDegZ k = tDegZ k`, the exact table
  up to `k = 14`;
* `corollary_16_11_polynomial_fejerJ_of_profiles` with `expDegJ_tight_le`:
  `e⁻¹ ≤ (2/α)^(2^(2·tDegZ k + 7k + 38))`, that is `5·2^k + O(k²)`,
  against `3·tDegX k + 6k + 38 ~ 7.5·2^k` at the X step and `236·2^k`
  printed. The density of the joint-slice frequency box costs one class
  degree less. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

'''
out = HEAD + lem + body + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs16PolynomialFejerJ.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
