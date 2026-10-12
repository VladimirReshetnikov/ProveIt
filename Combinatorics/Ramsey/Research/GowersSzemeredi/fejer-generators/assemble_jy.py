"""Proofs18CoverFejerHeadlineJ: Theorem 18.1 with joint slices (Notes L.16q), from HeadlineY."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


RENAMES = ['GenParamsZ:GenParamsJ', 'densDegZ:densDegJ', 'expDegZ:expDegJ', 'rhoDegZ:rhoDegJ',
           'yIn_boundsZ:yIn_boundsJ', 'Eloc_inv_leZ:Eloc_inv_leJ', 'envStepY:envStepJ',
           'polyEnvBound_stepY:polyEnvBound_stepJ', 'polyGenMuY_succ:polyGenMuJ_succ', 'polyGenMuY:polyGenMuJ',
           'polyEnvBound_allY:polyEnvBound_allJ', 'tightHyp_of_profiles_fejerZ:tightHyp_of_profiles_fejerJ']


def rename(t):
    for p in RENAMES:
        a, b = p.split(':')
        t = re.sub(r'\b' + a + r'\b', b, t)
    return t


BAD = re.compile(r'\b(?:' + '|'.join(p.split(':')[0] for p in RENAMES) + r')\b')

z = text('Proofs18CoverFejerHeadlineZ')
a = z.index('/-- The standing hypotheses at the polynomial base budget. -/')
b = z.index('/-- The Theorem 18.1 envelope at the tight base budget. -/')
hyp = rename(z[a:b])

y = text('Proofs18CoverFejerHeadlineY')
a = y.index('/-- The envelope after one step (no threshold). -/')
b = y.index('/-! ### Closed forms -/')
body = rename(y[a:b])

TAIL = '''/-! ### Closed forms -/

theorem envStepJ_le_tight {k : Nat} (hk : 15 ≤ k) (μ : Nat) :
    envStepJ k (tightMu0Z k) (genMuKZ k) μ ≤
      μ + 10 * 2 ^ (k - 1) + 6 * (k + 4) ^ 2 + 7 * k + 64 := by
  unfold envStepJ GenParamsJ.densDegJ GenParamsJ.expDegJ GenParamsJ.rhoDegJ tightMu0Z tightMuW
    genMuKZ pDeg
  rw [tDegZ_eq_of_ge hk]
  have := Nat.lt_two_pow_self (n := k - 1)
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ (k - 1) = y at *
  omega

theorem polyGenMuJ_fifteen : polyGenMuJ 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel

theorem polyGenMuJ_le16 : ∀ k, 15 ≤ k → polyGenMuJ k + 4 * k + 128 ≤ 16 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuJ_fifteen
  | succ k hk ih =>
    rw [polyGenMuJ_succ (by omega)]
    have h1 := envStepJ_le_tight (k := k + 1) (by omega) (polyGenMuJ k)
    have h2 := thirtytwo_sq_le_two_pow_fourteen k (by omega)
    have h4 : 7 * k + 80 ≤ (k + 5) ^ 2 := by nlinarith
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 - 1 = k by omega] at h1
    rw [pow_succ]
    generalize (k + 5) ^ 2 = s5 at *
    generalize 2 ^ k = x at *
    omega

/-! The envelopes in dimensions `2, …, 14`, kernel-evaluated. -/

theorem polyGenMuJ_small16 {k : Nat} (h1 : 10 ≤ k) (h2 : k ≤ 14) :
    polyGenMuJ k + 1 ≤ 16 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuJ_fit16 {k : Nat} (hk : 10 ≤ k) : polyGenMuJ k + 1 ≤ 16 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact polyGenMuJ_small16 hk (by omega)
  · have := polyGenMuJ_le16 k h
    omega

theorem polyGenMuJ_small32 {k : Nat} (h1 : 7 ≤ k) (h2 : k ≤ 14) :
    polyGenMuJ k + 1 ≤ 32 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuJ_fit32 {k : Nat} (hk : 7 ≤ k) : polyGenMuJ k + 1 ≤ 32 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact polyGenMuJ_small32 hk (by omega)
  · have := polyGenMuJ_le16 k h
    have h16 : 16 * 2 ^ k ≤ 32 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

theorem polyGenMuJ_small64 {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 14) :
    polyGenMuJ k + 1 ≤ 64 * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem polyGenMuJ_fit64 {k : Nat} (hk : 2 ≤ k) : polyGenMuJ k + 1 ≤ 64 * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact polyGenMuJ_small64 hk (by omega)
  · have := polyGenMuJ_le16 k h
    have h16 : 16 * 2 ^ k ≤ 64 * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

/-! ### The headline statements -/

'''


def headline(c, d0, fit, kmin, word):
    pre = 2 ** (c + 2)
    return f'''/-- **Theorem 18.1 at every degree `d ≥ {d0}` with `d + {c}`**, from the profiles
with polynomial family constants (joint slices). -/
theorem theorem_18_1_d{c}_{word}_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {{Kφ : Real}} {{pφ : Nat}} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {{d : Nat}} (hd : {d0} ≤ d) : Theorem181AtSharp {c} d := by
  have henv := polyEnvBound_allJ Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  have hle := {fit} (k := d - 2) (by omega)
  have h2 : 2 ^ (d + {c}) = {pre} * 2 ^ (d - 2) := by
    rw [show d + {c} = (d - 2) + {c + 2} by omega, pow_add]; ring
  rw [h2]
  exact hle

'''


TAIL += headline(2, 12, 'polyGenMuJ_fit16', 10, 'twelve')
TAIL += headline(3, 9, 'polyGenMuJ_fit32', 7, 'nine')
TAIL += headline(4, 4, 'polyGenMuJ_fit64', 2, 'four')

# ------------------------------------------------------------------ Theorem 18.2
RENAMES_X = ['envStepZTx:envStepJTx', 'envBound_stepZx:envBound_stepJx', 'genMuXZ_succ:genMuXJ_succ',
             'genMuXZ:genMuXJ', 'envBound_allXZ:envBound_allXJ', 'threshDegZ:threshDegJ',
             'MReq_le_expZ:MReq_le_expJ', 'Tloc_le_expZ:Tloc_le_expJ']


def rename_x(t):
    t = rename(t)
    for p in RENAMES_X:
        a, b = p.split(':')
        t = re.sub(r'\b' + a + r'\b', b, t)
    return t


a = z.index('/-- The envelope after one step, with the threshold, without the cubic branch. -/')
b = z.rindex('/--', 0, z.index('def genMuKZ'))
xstep = rename_x(z[a:b])
assert 'genMuKZ (k : Nat)' not in xstep
a = z.index('/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/')
b = z.index('/-! ### Closed forms -/')
xall = rename_x(z[a:b])

XTAIL = '''/-! ### Theorem 18.2 -/

theorem envStepJTx_le_tight {k : Nat} (hk : 15 ≤ k) (μ : Nat) :
    envStepJTx k (tightMu0Z k) (genMuKZ k) μ ≤
      μ + 10 * 2 ^ (k - 1) + 6 * (k + 4) ^ 2 + 4 * (k + 3) ^ 2 + 6 * k + 59 := by
  unfold envStepJTx GenParamsJ.densDegJ GenParamsJ.threshDegJ GenParamsJ.expDegJ
    GenParamsJ.rhoDegJ tightMu0Z tightMuW genMuKZ pDeg
  rw [tDegZ_eq_of_ge hk]
  have := Nat.lt_two_pow_self (n := k - 1)
  have hkq : k ≤ 4 * (k + 3) ^ 2 := by nlinarith
  generalize 4 * (k + 3) ^ 2 = q at hkq ⊢
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ (k - 1) = y at *
  omega

theorem envStepJTx_ge (k μ0 μK μ : Nat) : 5 * k + 33 ≤ envStepJTx k μ0 μK μ := by
  unfold envStepJTx GenParamsJ.threshDegJ
  omega

theorem genMuXJ_fifteen : genMuXJ 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel

/-- **The Theorem 18.2 envelope with joint slices**: `μ_k + 4k + 128 ≤ 16·2^k`
for `k ≥ 15`. -/
theorem genMuXJ_le16 : ∀ k, 15 ≤ k → genMuXJ k + 4 * k + 128 ≤ 16 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXJ_fifteen
  | succ k hk ih =>
    rw [genMuXJ_succ (by omega)]
    have h1 := envStepJTx_le_tight (k := k + 1) (by omega) (genMuXJ k)
    have h2 := thirtytwo_sq_le_two_pow_fourteen k (by omega)
    have h3 : (k + 4) ^ 2 ≤ (k + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : 6 * k + 70 ≤ (k + 5) ^ 2 := by nlinarith
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 + 3 = k + 4 by ring,
      show k + 1 - 1 = k by omega] at h1
    rw [pow_succ]
    generalize (k + 5) ^ 2 = s5 at *
    generalize (k + 4) ^ 2 = s4 at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXJ_ge {k : Nat} (hk : 2 ≤ k) : 5 * k + 33 ≤ genMuXJ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXJ_succ (by omega)]
  exact envStepJTx_ge _ _ _ _

'''


def xfit(P, kmin):
    return f'''theorem genMuXJ_small{P} {{k : Nat}} (h1 : {kmin} ≤ k) (h2 : k ≤ 14) :
    genMuXJ k + 2 * k + 22 ≤ {P} * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXJ_fit{P} {{k : Nat}} (hk : {kmin} ≤ k) : genMuXJ k + 2 * k + 22 ≤ {P} * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact genMuXJ_small{P} hk (by omega)
  · have := genMuXJ_le16 k h
    have h16 : 16 * 2 ^ k ≤ {P} * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

'''


def xheadline(c, L0, word):
    P = 2 ** (c + 4)
    return f'''/-- **Theorem 18.2 at every length `L ≥ {L0}` with offset `{c}`** (joint slices),
from the recurrence profiles with polynomial family constants. -/
theorem theorem_18_2_L{c}_{word}_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {{L : Nat}} (hL : {L0} ≤ L) : Theorem182AtSharp {c} L := by
  have henv := envBound_allXJ Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXJ_ge (k := L - 4) (by omega)
  have hle := genMuXJ_fit{P} (k := L - 4) (by omega)
  have h42 : 42 ≤ genMuXJ (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXJ (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXJ (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  have h2 : 2 ^ (L + {c}) = {P} * 2 ^ (L - 4) := by
    rw [show L + {c} = (L - 4) + {c + 4} by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Corollary 18.7 at every length `L ≥ {L0}` with offset `{c}`** (joint slices). -/
theorem corollary_18_7_L{c}_{word}_le_of_profiles_poly (Kc pc : Nat → Nat)
    (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {{L : Nat}} (hL : {L0} ≤ L) : Corollary187AtSharp {c} L :=
  (theorem_18_2_L{c}_{word}_le_of_profiles_poly Kc pc hK hp hrec hconst hL).corollary_18_7

'''


XTAIL += xfit(16, 11) + xfit(32, 8) + xfit(64, 5)
XTAIL += xheadline(0, 15, 'fifteen') + xheadline(1, 12, 'twelve') + xheadline(2, 9, 'nine')
TAIL = xstep + xall + TAIL + XTAIL

HEAD = '''import GowersSzemeredi.Proofs18CoverExponentsFejerJ
import GowersSzemeredi.Proofs18CoverFejerHeadlineY

/-! **Joint slices: Theorem 18.1 at `d + 2` from `d = 12`, `d + 3` from
`d = 9`, `d + 4` from `d = 4`; Theorem 18.2 / Corollary 18.7 at `L + 0` from
`L = 15`, `L + 1` from `L = 12`, `L + 2` from `L = 9`** (Notes L.16q).

The envelopes of `Proofs18CoverFejerHeadlineY` (Theorem 18.1) and
`Proofs18CoverFejerHeadlineZ` (Theorem 18.2) over the joint-slice step
(`Proofs18CoverModulusFejerJ`, `…DensityFejerJ`, `…ExponentsFejerJ`). The two
anchor slices of the single-piece lift are covered jointly, so the density of
the step costs one class degree (`densDegJ = ρ + tDeg + 11`) instead of two
(`ρ + 2·tDeg + 13`). Both envelopes are then about `10·2^k` instead of
`15·2^k`. The closed forms hold from `k = 15`, and `decide +kernel` evaluates
the envelopes in dimensions `2, …, 14` (generated by `assemble_jy.py`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

'''
out = HEAD + hyp + body + TAIL + 'end LeanProofs.GowersSzemeredi\n'
BAD = re.compile(r'\b(?:' + '|'.join(p.split(':')[0] for p in RENAMES + RENAMES_X) + r')\b')
bad = [l.strip()[:150] for l in out.split('\n') if BAD.search(l) and not l.lstrip().startswith(('--', '/-', '`'))]
assert not bad, bad[:8]
(GS / 'Proofs18CoverFejerHeadlineJ.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
