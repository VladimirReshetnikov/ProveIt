"""J copies (joint slices, Notes L.16q) of the Z step chain: Modulus, Density, Exponents."""
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


RENAMES = ['GenParamsZ:GenParamsJ', 'coverPrec_gen_bounds_fejerZ:coverPrec_gen_bounds_fejerJ',
           'rhoDegZ_ge:rhoDegJ_ge', 'rhoDegZ:rhoDegJ', 'rho1_inv_leZ:rho1_inv_leJ', 'nestExp_inv_leZ:nestExp_inv_leJ',
           'densDegZ:densDegJ', 'yIn_boundsZ:yIn_boundsJ', 'expDegZ:expDegJ',
           'spectrum_exps_inv_leZ:spectrum_exps_inv_leJ', 'slice_exps_inv_leZ:slice_exps_inv_leJ',
           'Eloc_inv_leZ:Eloc_inv_leJ', 'threshDegZ:threshDegJ', 'MReq_le_expZ:MReq_le_expJ',
           'Tloc_le_expZ:Tloc_le_expJ']


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
    old = [l.strip()[:150] for l in t.split('\n')
           if re.search(r'\bsinglePieceEtaF\b|\bSinglePieceModulusConditionsF\b|\bSinglePieceGlobalScaleF\b|'
                        r'\bsinglePieceGlobalWidthF\b|single_piece_inverse_step_global_cover_fejer\b|GenParams\.dens_step\b', l)]
    assert not old, (name, old[:6])


PRE = 'set_option autoImplicit false\nnoncomputable section\nnamespace LeanProofs.GowersSzemeredi\n\n'


def write(dst, head, b):
    check(dst, b)
    (GS / f'{dst}.lean').write_text(head + b + 'end LeanProofs.GowersSzemeredi\n', encoding='utf-8', newline='\n')
    print('wrote', dst)


# ---------------------------------------------------------------- Modulus
s = text('Proofs18CoverModulusFejerZ')
b = rename(s[s.index('/-! ### The parameters -/'):s.rindex('end LeanProofs.GowersSzemeredi')])
b = sub(b, [
    ('/-- The first slice exponent. -/\ndef Eth : Real := uExp P.V (uDegZ P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 2)',
     '/-- The slice exponent `E(θ_S/4)` of the joint slices. -/\n'
     'def Eth : Real := uExp P.V (uDegZ P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 4)'),
    ('/-- The second slice exponent. -/\ndef Ec : Real := uExp P.V (uDegZ P.k) (alpha / 2) (P.B alpha) (P.CS alpha / 2)',
     '/-- The second factor of the joint-slice exponent (equal to `Eth`). -/\n'
     'def Ec : Real := uExp P.V (uDegZ P.k) (alpha / 2) (P.B alpha) (P.ThS alpha / 4)'),
    ('uExp_pos hV (uDegZ P.k) hg hg1 hB.1 hB.2 (half_pos hS.1) (by linarith [hS.2])',
     'uExp_pos hV (uDegZ P.k) hg hg1 hB.1 hB.2 (by linarith [hS.1]) (by linarith [hS.1, hS.2])'),
    ('uExp_pos hV (uDegZ P.k) hg hg1 hB.1 hB.2 (half_pos hCS.1) (by linarith [hCS.2])',
     'uExp_pos hV (uDegZ P.k) hg hg1 hB.1 hB.2 (by linarith [hS.1]) (by linarith [hS.1, hS.2])'),
    ('    SinglePieceModulusConditionsF (fun l => uCount P.V (uDegZ l))',
     '    SinglePieceModulusConditionsFJ (fun l => uCount P.V (uDegZ l))'),
    ('  unfold SinglePieceModulusConditionsF SinglePieceGlobalScaleF singlePieceGlobalWidthF',
     '  unfold SinglePieceModulusConditionsFJ SinglePieceGlobalScaleFJ singlePieceGlobalWidthFJ'),
    ('''      (N : Real) ^ P.F alpha ≤
        coverWidth (uExp P.V (uDegZ P.k) (alpha / 2) (P.B alpha)) (P.CS alpha)
          (coverWidth (uExp P.V (uDegZ P.k) (alpha / 2) (P.B alpha)) (P.ThS alpha)
            ⌈spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8⌉₊) ∧''',
     '''      (N : Real) ^ P.F alpha ≤
        jointSliceWidth (uExp P.V (uDegZ P.k) (alpha / 2) (P.B alpha))
          (spectrumPieceRho (fun t => t / 2) (P.Rho1 alpha)) 1
            ⌈spectrumCellWidth (P.Zeta alpha) m (familyRecExp P.k P.p q) / 8⌉₊ ∧'''),
])
a = b.index('    have hin := coverWidth_powerLB (uExp P.V (uDegZ P.k) (alpha / 2) (P.B alpha)) (P.ThS alpha)')
e = b.index('    exact hNm\n', a) + len('    exact hNm\n')
b = b[:a] + '''    show (N : Real) ^ P.F alpha ≤ ((⌈(L : Real) ^ (P.Eth alpha * P.Ec alpha)⌉₊ : Nat) : Real)
    refine le_trans ?_ (Nat.le_ceil _)
    have hEE : 0 ≤ P.Eth alpha * P.Ec alpha := mul_nonneg hEth.le hEc.le
    have hstep : ((m : Real) ^ (P.Bexp alpha / 2)) ^ (P.Eth alpha * P.Ec alpha) ≤
        (L : Real) ^ (P.Eth alpha * P.Ec alpha) :=
      Real.rpow_le_rpow hm0 hLge hEE
    refine le_trans ?_ hstep
    have hNm : ((N : Real) ^ P.MExp alpha) ^ (P.Bexp alpha / 2 * (P.Eth alpha * P.Ec alpha)) ≤
        (m : Real) ^ (P.Bexp alpha / 2 * (P.Eth alpha * P.Ec alpha)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hmpow
        (mul_nonneg (div_nonneg hb.le (by norm_num)) hEE)
    rw [← Real.rpow_mul (by linarith)]
    rw [← Real.rpow_mul hNpos.le] at hNm
    have hexp1 : P.F alpha =
        P.MExp alpha * (P.Bexp alpha / 2 * (P.Eth alpha * P.Ec alpha)) := by
      unfold F; ring
    rw [hexp1]
    exact hNm
''' + b[e:]
write('Proofs18CoverModulusFejerJ', '''import GowersSzemeredi.Proofs18CoverModulusFejerZ
import GowersSzemeredi.Proofs18JointSliceInverseFejer

/-! **The Section 18 step with joint slices** (Notes L.16q), part 1
(generated from `Proofs18CoverModulusFejerZ` by `assemble_j.py`).

The class table is `tDegZ`. The step goes through
`single_piece_inverse_step_global_cover_fejer_joint`: the final width is
`jointSliceWidth`, `⌈L^(E(θ_S/4)²)⌉`, so both slice exponents `Eth` and `Ec`
are `E(θ_S/4)` (the second slice exponent at `c(θ_S)` is gone). -/
''' + PRE, b)

# ---------------------------------------------------------------- Density
s = text('Proofs18CoverDensityFejerZ')
b = rename(s[s.index('variable {alpha : Real}'):s.rindex('end LeanProofs.GowersSzemeredi')])
b = sub(b, [
    ('def eta : Real := singlePieceEtaF (fun l => uCount P.V (uDegZ l)) alpha P.k',
     'def eta : Real := singlePieceEtaFJ (fun l => uCount P.V (uDegZ l)) alpha P.k'),
    ('  exact single_piece_inverse_step_global_cover_fejer (Qb := fun l => uCount P.V (uDegZ l))',
     '  exact single_piece_inverse_step_global_cover_fejer_joint (Qb := fun l => uCount P.V (uDegZ l))'),
    ('def densDegJ (k μ0 : Nat) : Nat := rhoDegJ k μ0 + 2 * (tDegZ k) + 13',
     'def densDegJ (k μ0 : Nat) : Nat := rhoDegJ k μ0 + tDegZ k + 11'),
    ('      (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJ P.k P.μ0 + 2 * (tDegZ P.k) + 12)) ∧',
     '      (P.eta alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJ P.k P.μ0 + tDegZ P.k + 10)) ∧'),
    ('  obtain ⟨hd0, hd1, hdi⟩ := GenParams.dens_step hX hbase hS0 hS1 hSi ha0 hb0 (by omega)',
     '''  obtain ⟨hd0, hd1, hdi⟩ := GenParams.joint_dens_step hX hbase
    (Q := uCount P.V (uDegZ k) (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k))
    (fun _ => rfl) (fun _ _ _ => one_le_uCount _ _ _ _ _) hS0 hS1 hSi ha0 hb0 (by omega)'''),
    ('''  have hm : 3 * (k + 4) ^ 2 ≤ rhoDegJ k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 := by
    have h1 := sq_le_three_tDegZ k''',
     '''  have hm : 3 * (k + 4) ^ 2 ≤ rhoDegJ k P.μ0 + 2 + 3 + (μD + 1) + 3 := by
    have h1 := sq_le_two_tDegZ k
    have h6 : tDegZ k + P.μ0 + 3 + k ≤ rhoDegJ k P.μ0 := by
      unfold rhoDegJ; have := le_max_left (tDegZ k + P.μ0 + 3) (pDeg k + 1); omega'''),
    ('''  have e1 : rhoDegJ k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 = rhoDegJ k P.μ0 + 2 * μD + 12 := by
    ring
  have e2 : rhoDegJ k P.μ0 + 2 + 3 + 2 * (μD + 1) + 4 + 1 + 1 = densDegJ k P.μ0 := by''',
     '''  have e1 : rhoDegJ k P.μ0 + 2 + 3 + (μD + 1) + 3 + 1 = rhoDegJ k P.μ0 + μD + 10 := by
    ring
  have e2 : rhoDegJ k P.μ0 + 2 + 3 + (μD + 1) + 3 + 1 + 1 = densDegJ k P.μ0 := by'''),
])
write('Proofs18CoverDensityFejerJ', '''import GowersSzemeredi.Proofs18CoverModulusFejerJ
import GowersSzemeredi.Proofs18CoverDensityFejerZ

/-! **The Section 18 step with joint slices**, part 2 (generated from
`Proofs18CoverDensityFejerZ` by `assemble_j.py`).

The joint-slice density `θ·(θ/2)/Q(θ/4)²` equals `8·c(θ/2)²` for
`c(s) = s/2/Q(s/2)`, so it costs one application of the class control
(`GenParams.joint_dens_step`, exponent `m + μ_b + 3`) instead of two
(`GenParams.dens_step`, `m + 2μ_b + 4`). The density degree is
`ρ + tDeg + 11` instead of `ρ + 2·tDeg + 13`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `3(k+4)² ≤ 2·tDegZ k + 6k + 35`: the side condition of `eta_step_small`
at the joint-slice density degree. -/
theorem sq_le_two_tDegZ (k : Nat) : 3 * (k + 4) ^ 2 ≤ 2 * tDegZ k + 6 * k + 35 := by
  rcases Nat.lt_or_ge k 15 with h | h
  · interval_cases k <;> decide
  · rw [tDegZ_eq_of_ge h]; omega

/-- **The joint-slice density** `θ·(θ - (θ/4 + θ/4))/Q(θ/4)²` for a class control
`c(s) = s/2/Q(s/2)` that is a reciprocal power: one application of `c`. -/
theorem GenParams.joint_dens_step {X : Real} (hX : 2 ≤ X) {c : Real → Real} {a0 b0 : Nat}
    (hc : RecipPowerLB X c a0 b0) {Q : Real → Real} (hcQ : ∀ s, c s = s / 2 / Q (s / 2))
    (hQ1 : ∀ t, 0 < t → t ≤ 1 → 1 ≤ Q t)
    {θ : Real} {m μa μb : Nat} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθi : θ⁻¹ ≤ X ^ (2 ^ m))
    (ha0 : a0 ≤ 2 ^ μa) (hb0 : b0 ≤ 2 ^ μb) (hμa : μa ≤ m) :
    0 < θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))) ∧
      θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))) ≤ 1 ∧
      (θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))))⁻¹ ≤ X ^ (2 ^ (m + μb + 3)) := by
  have hX1 : (1 : Real) ≤ X := by linarith
  have h20 : 0 < θ / 2 := half_pos hθ0
  have h21 : θ / 2 ≤ 1 := by linarith
  have h2i : (θ / 2)⁻¹ ≤ X ^ (2 ^ (m + 1)) := by
    rw [inv_div, div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hθ0).le (hX.trans (pw_X hX _)) hθi
  obtain ⟨hc0, -, hci⟩ := hc.apply_le hX1 h20 h21 h2i
  have hci' : (c (θ / 2))⁻¹ ≤ X ^ (2 ^ (m + μb + 2)) := by
    refine hci.trans (pow_le_pow_right₀ hX1 ?_)
    have h1 : 2 ^ (m + 1) * b0 ≤ 2 ^ (m + 1) * 2 ^ μb := Nat.mul_le_mul_left _ hb0
    have h2 : 2 ^ (m + 1) * 2 ^ μb = 2 ^ (m + μb + 1) := by rw [← pow_add]; ring_nf
    have h3 : 2 ^ μa ≤ 2 ^ (m + μb + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (m + μb + 2) = 2 * 2 ^ (m + μb + 1) := by rw [pow_succ]; ring
    omega
  have hq := hQ1 (θ / 4) (by linarith) (by linarith)
  have hqq : 1 ≤ Q (θ / 4) * Q (θ / 4) := by nlinarith
  have hf0 : 0 ≤ (θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4)) :=
    div_nonneg (by linarith) (by linarith)
  have hf1 : (θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4)) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hle : θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))) ≤ 1 := by nlinarith
  have hQ0 : Q (θ / 4) ≠ 0 := (show (0 : Real) < Q (θ / 4) by linarith).ne'
  have hval : θ * ((θ - (θ / 4 + θ / 4)) / (Q (θ / 4) * Q (θ / 4))) =
      8 * (c (θ / 2) * c (θ / 2)) := by
    rw [hcQ (θ / 2), show θ / 2 / 2 = θ / 4 by ring]
    field_simp
    ring
  rw [hval] at hle ⊢
  have hcc := mul_pos hc0 hc0
  refine ⟨by linarith, hle, ?_⟩
  have hsq := pw_mul hX (inv_pos.mpr hc0).le (inv_pos.mpr hc0).le hci' hci'
  have hinv : (8 * (c (θ / 2) * c (θ / 2)))⁻¹ ≤ (c (θ / 2))⁻¹ * (c (θ / 2))⁻¹ := by
    rw [mul_inv, mul_inv]
    have h0 : 0 ≤ (c (θ / 2))⁻¹ * (c (θ / 2))⁻¹ := by positivity
    nlinarith
  exact hinv.trans hsq

''', b)

# ---------------------------------------------------------------- Exponents
s = text('Proofs18CoverExponentsFejerZ')
b = rename(s[s.index('namespace GenParamsZ'):s.rindex('end LeanProofs.GowersSzemeredi')])
b = sub(b, [
    ('  max (rhoDegJ k μ0 + 2 * (tDegZ k) + 9) (max (rhoDegJ k μ0 + tDegZ k + k + 7) (μK + 2))',
     '  max (rhoDegJ k μ0 + tDegZ k + 9) (max (rhoDegJ k μ0 + tDegZ k + k + 7) (μK + 2))'),
    ('''    (P.Eth alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJ P.k P.μ0 + 2 * (tDegZ P.k) + 9)) ∧
      (P.Ec alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJ P.k P.μ0 + 2 * (tDegZ P.k) + 9)) := by''',
     '''    (P.Eth alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJ P.k P.μ0 + tDegZ P.k + 9)) ∧
      (P.Ec alpha)⁻¹ ≤ (2 / alpha) ^ (2 ^ (rhoDegJ P.k P.μ0 + tDegZ P.k + 9)) := by'''),
    ('''  obtain ⟨hc0, hc1, hci⟩ := GenParams.cS_step hX hbase hS0 hS1 hSi ha0 hb0 (by omega)
  have hCS : P.CS alpha =
      baseCF P.V (uDegZ k) P.k alpha (P.ThS alpha) := rfl
  rw [← hCS] at hc0 hc1 hci
''', ''),
    ('''  constructor
  · exact pw_mono hX (hslice hS0 hS1 hSi (by omega)) (by omega)
  · exact pw_mono hX (hslice hc0 hc1 hci (by omega)) (by omega)''',
     '''  have hS2 : 0 < P.ThS alpha / 2 := half_pos hS0
  have hS21 : P.ThS alpha / 2 ≤ 1 := by linarith
  have hS2i : (P.ThS alpha / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ (ρ + 2 + 3 + 1)) := by
    rw [inv_div, div_eq_mul_inv]
    exact pw_mul hX (by norm_num) (inv_pos.mpr hS0).le (hX.trans (pw_X hX _)) hSi
  have hE := hslice hS2 hS21 hS2i (by omega)
  rw [show P.ThS alpha / 2 / 2 = P.ThS alpha / 4 by ring] at hE
  exact ⟨pw_mono hX hE (by omega), pw_mono hX hE (by omega)⟩'''),
    ('  have hM1 : rhoDegJ P.k P.μ0 + 2 * (tDegZ P.k) + 9 ≤ M := by',
     '  have hM1 : rhoDegJ P.k P.μ0 + tDegZ P.k + 9 ≤ M := by'),
])
write('Proofs18CoverExponentsFejerJ', '''import GowersSzemeredi.Proofs18CoverDensityFejerJ
import GowersSzemeredi.Proofs18CoverExponentsFejerZ

/-! **The Section 18 step with joint slices**, part 3 (generated from
`Proofs18CoverExponentsFejerZ` by `assemble_j.py`). Both slice exponents are
`E(θ_S/4)`, of degree `ρ + tDeg + 9` (was `ρ + 2·tDeg + 9`). -/
''' + PRE, b)
