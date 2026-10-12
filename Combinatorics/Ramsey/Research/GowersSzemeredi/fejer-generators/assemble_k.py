"""Proofs18CoverFejerHeadlineK: Theorem 18.2 with the sharp partition constant (Notes L.16s)."""
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


# -------------------------------------------------- inv_thr_le_ex with partDeg
th = text('Proofs18CoverThresholdsSharp')
a = th.index('/-- **The phase-refinement threshold, with the constants at the exponential\nlevel.** -/')
b = th.index('/-- The envelope after one step, with the threshold, without the cubic branch. -/')
inv = th[a:b]
inv = sub(inv, [
    ('''  have hpow : ((η * β / 2)⁻¹) ^ polynomialPartitionConstant (k + 1 + 1) ≤
      X ^ (2 ^ (M + 2 + 4 * (k + 1 + 1 + 1) ^ 2)) :=
    pw_pow hX (inv_pos.mpr hb).le hbi (polyPartConst_le (k + 1 + 1))
  rw [show k + 1 + 1 + 1 = k + 3 by ring] at hpow
''', '''  have hpow : ((η * β / 2)⁻¹) ^ polynomialPartitionConstant (k + 1 + 1) ≤
      X ^ (2 ^ (M + 2 + partDeg k)) :=
    pw_pow hX (inv_pos.mpr hb).le hbi (polyPartConst_le_sharp k)
'''),
    ('theorem inv_thr_le_ex ', 'theorem inv_thr_le_ex_sharp '),
])
inv = inv.replace('4 * (k + 3) ^ 2', 'partDeg k')
inv = inv.replace('level.** -/', 'level**, with the partition constant at `2^partDeg k`. -/', 1)
assert 'polyPartConst_le ' not in inv and '4 * (k' not in inv

# -------------------------------------------------- the J 18.2 step and envelope
hj = text('Proofs18CoverFejerHeadlineJ')
a = hj.index('/-- The envelope after one step, with the threshold, without the cubic branch. -/')
b = hj.rindex('/--', 0, hj.index('def genMuKZ') if 'def genMuKZ' in hj else hj.index('/-- The Theorem 18.2 envelope'))
b = hj.index('/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/')
step = hj[a:b]
c = hj.index('/-! ### Closed forms -/')
env = hj[b:c]
step = sub(step, [
    ('''    have hP := polyPartConst_le (k + 1 + 1)
    rw [show k + 1 + 1 + 1 = k + 3 by ring] at hP
''', '''    have hP := polyPartConst_le_sharp k
'''),
])
RN = [('envStepJTx', 'envStepKTx'), ('envBound_stepJx', 'envBound_stepKx'), ('genMuXJ_succ', 'genMuXK_succ'),
      ('genMuXJ', 'genMuXK'), ('envBound_allXJ', 'envBound_allXK'), ('inv_thr_le_ex', 'inv_thr_le_ex_sharp')]


def rn(t):
    for x, y in RN:
        t = re.sub(r'\b' + x + r'\b', y, t)
    return t


step = rn(step).replace('4 * (k + 3) ^ 2', 'partDeg k')
env = rn(env)
for t in (step, env):
    assert '4 * (k + 3)' not in t and 'polyPartConst_le ' not in t
    assert not re.search(r'\b(envStepJTx|envBound_stepJx|genMuXJ|envBound_allXJ)\b', t)

LEMMAS = '''/-- `(n+1)² ≤ 4^n` for `n ≥ 1`. -/
theorem succ_sq_le_four_pow : ∀ n, 1 ≤ n → (n + 1) ^ 2 ≤ 4 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc (n + 1 + 1) ^ 2 ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (n + 1) ^ 2 := by ring
      _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (n + 1) := by ring

/-- `(d!)² · 2^d ≤ 2^(d²)`. -/
theorem factorial_sq_mul_two_pow_le : ∀ d : Nat, d.factorial ^ 2 * 2 ^ d ≤ 2 ^ (d * d)
  | 0 => by norm_num
  | n + 1 => by
    have ih := factorial_sq_mul_two_pow_le n
    have h4 : (n + 1) ^ 2 * 2 ≤ 2 ^ (2 * n + 1) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; norm_num
      · have h1 := succ_sq_le_four_pow n h
        have e : 2 ^ (2 * n + 1) = 4 ^ n * 2 := by
          rw [pow_succ, pow_mul]; norm_num
        rw [e]; omega
    have e1 : (n + 1).factorial ^ 2 * 2 ^ (n + 1) =
        (n.factorial ^ 2 * 2 ^ n) * ((n + 1) ^ 2 * 2) := by
      rw [Nat.factorial_succ]; ring
    have e2 : 2 ^ ((n + 1) * (n + 1)) = 2 ^ (n * n) * 2 ^ (2 * n + 1) := by
      rw [← pow_add]; congr 1 <;> ring
    rw [e1, e2]
    exact Nat.mul_le_mul ih h4

/-- The log-degree of the partition constant of the step: `(k+3)² + (k+2)(k+1)`. -/
def partDeg (k : Nat) : Nat := (k + 3) ^ 2 + (k + 2) * (k + 1)

/-- **The polynomial partition constant, sharply**: `(d!)²·2^((d+1)²) ≤ 2^((d+1)² + d(d-1))`
at `d = k + 2` (`polyPartConst_le` charges `2^(4(d+1)²)`). -/
theorem polyPartConst_le_sharp (k : Nat) :
    polynomialPartitionConstant (k + 1 + 1) ≤ 2 ^ partDeg k := by
  unfold polynomialPartitionConstant partDeg
  have h := factorial_sq_mul_two_pow_le (k + 1 + 1)
  have e : 2 ^ ((k + 1 + 1) * (k + 1 + 1)) = 2 ^ ((k + 2) * (k + 1)) * 2 ^ (k + 1 + 1) := by
    rw [← pow_add]; congr 1 <;> ring
  rw [e] at h
  have h' : (k + 1 + 1).factorial ^ 2 ≤ 2 ^ ((k + 2) * (k + 1)) :=
    Nat.le_of_mul_le_mul_right h (by positivity)
  calc (k + 1 + 1).factorial ^ 2 * 2 ^ ((k + 1 + 1 + 1) ^ 2)
      ≤ 2 ^ ((k + 2) * (k + 1)) * 2 ^ ((k + 1 + 1 + 1) ^ 2) := Nat.mul_le_mul_right _ h'
    _ = 2 ^ ((k + 3) ^ 2 + (k + 2) * (k + 1)) := by rw [← pow_add]; congr 1 <;> ring

theorem partDeg_le (k : Nat) : partDeg k ≤ 4 * (k + 3) ^ 2 := by
  unfold partDeg; nlinarith

'''

TAIL = '''/-! ### Closed forms -/

theorem envStepKTx_le_tight {k : Nat} (hk : 15 ≤ k) (μ : Nat) :
    envStepKTx k (tightMu0Z k) (genMuKZ k) μ ≤
      μ + 10 * 2 ^ (k - 1) + 6 * (k + 4) ^ 2 + partDeg k + 6 * k + 59 := by
  unfold envStepKTx GenParamsJ.densDegJ GenParamsJ.threshDegJ GenParamsJ.expDegJ
    GenParamsJ.rhoDegJ tightMu0Z tightMuW genMuKZ pDeg
  rw [tDegZ_eq_of_ge hk]
  have := Nat.lt_two_pow_self (n := k - 1)
  have hkq : k ≤ partDeg k := by unfold partDeg; nlinarith
  generalize partDeg k = q at hkq ⊢
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ (k - 1) = y at *
  omega

theorem envStepKTx_ge (k μ0 μK μ : Nat) : 5 * k + 33 ≤ envStepKTx k μ0 μK μ := by
  unfold envStepKTx GenParamsJ.threshDegJ
  omega

theorem genMuXK_fifteen : genMuXK 15 + 4 * 15 + 128 ≤ 16 * 2 ^ 15 := by decide +kernel

/-- **The Theorem 18.2 envelope with the sharp partition constant**:
`μ_k + 4k + 128 ≤ 16·2^k` for `k ≥ 15`. -/
theorem genMuXK_le16 : ∀ k, 15 ≤ k → genMuXK k + 4 * k + 128 ≤ 16 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXK_fifteen
  | succ k hk ih =>
    rw [genMuXK_succ (by omega)]
    have h1 := envStepKTx_le_tight (k := k + 1) (by omega) (genMuXK k)
    have h2 := thirtytwo_sq_le_two_pow_fourteen k (by omega)
    have h3 : partDeg (k + 1) ≤ 2 * (k + 5) ^ 2 := by unfold partDeg; nlinarith
    have h4 : 6 * k + 70 ≤ (k + 5) ^ 2 := by nlinarith
    rw [show k + 1 + 4 = k + 5 by ring, show k + 1 - 1 = k by omega] at h1
    rw [pow_succ]
    generalize partDeg (k + 1) = q at *
    generalize (k + 5) ^ 2 = s5 at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXK_ge {k : Nat} (hk : 2 ≤ k) : 5 * k + 33 ≤ genMuXK k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXK_succ (by omega)]
  exact envStepKTx_ge _ _ _ _

'''


def xfit(P, kmin):
    return f'''theorem genMuXK_small{P} {{k : Nat}} (h1 : {kmin} ≤ k) (h2 : k ≤ 14) :
    genMuXK k + 2 * k + 22 ≤ {P} * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem genMuXK_fit{P} {{k : Nat}} (hk : {kmin} ≤ k) : genMuXK k + 2 * k + 22 ≤ {P} * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact genMuXK_small{P} hk (by omega)
  · have := genMuXK_le16 k h
    have h16 : 16 * 2 ^ k ≤ {P} * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega

'''


def xheadline(c, L0, word):
    P = 2 ** (c + 4)
    return f'''/-- **Theorem 18.2 at every length `L ≥ {L0}` with offset `{c}`** (joint slices,
sharp partition constant), from the recurrence profiles with polynomial family constants. -/
theorem theorem_18_2_L{c}_{word}_le_of_profiles_poly (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {{L : Nat}} (hL : {L0} ≤ L) : Theorem182AtSharp {c} L := by
  have henv := envBound_allXK Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXK_ge (k := L - 4) (by omega)
  have hle := genMuXK_fit{P} (k := L - 4) (by omega)
  have h42 : 42 ≤ genMuXK (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXK (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXK (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  have h2 : 2 ^ (L + {c}) = {P} * 2 ^ (L - 4) := by
    rw [show L + {c} = (L - 4) + {c + 4} by omega, pow_add]; ring
  rw [h2]
  omega

/-- **Corollary 18.7 at every length `L ≥ {L0}` with offset `{c}`.** -/
theorem corollary_18_7_L{c}_{word}_le_of_profiles_poly (Kc pc : Nat → Nat)
    (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))
    {{L : Nat}} (hL : {L0} ≤ L) : Corollary187AtSharp {c} L :=
  (theorem_18_2_L{c}_{word}_le_of_profiles_poly Kc pc hK hp hrec hconst hL).corollary_18_7

'''


TAIL += xfit(16, 10) + xfit(32, 7) + xfit(64, 4)
TAIL += xheadline(0, 14, 'fourteen') + xheadline(1, 11, 'eleven') + xheadline(2, 8, 'eight')

HEAD = '''import GowersSzemeredi.Proofs18CoverFejerHeadlineJ

/-! **Theorem 18.2 / Corollary 18.7 at `L + 0` from `L = 14`, `L + 1` from
`L = 11`, `L + 2` from `L = 8`: the partition constant, sharply** (Notes L.16s).

In Theorem 18.2 the inverse-step threshold raises the refinement constant to
the power `polynomialPartitionConstant (k+2) = ((k+2)!)²·2^((k+3)²)`
(`inv_thr_le_ex`), so its logarithm is a genuine cost of every step. The
corpus bound `polyPartConst_le` charges `4(k+3)²` for it, through
`d! ≤ 2^(d²)`. Since `(d!)²·2^d ≤ 2^(d²)` (`factorial_sq_mul_two_pow_le`),
`partDeg k = (k+3)² + (k+2)(k+1)` suffices (`polyPartConst_le_sharp`), about
half. This module contains `inv_thr_le_ex_sharp`, and the Theorem 18.2 step
and envelope of `Proofs18CoverFejerHeadlineJ` with that charge (generated by
`assemble_k.py`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

'''
out = HEAD + LEMMAS + inv + step + env + TAIL + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs18CoverFejerHeadlineK.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
