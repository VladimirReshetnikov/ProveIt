"""Proofs18CoverFejerHeadline: Theorem 18.1 at d + 6 and Theorem 18.2 at L + 4 from the profiles."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


def between(t, start, end_marker):
    a = t.index(start)
    b = t.index(end_marker, a + len(start))
    return t[a:b]


deg = text('Proofs18CoverDegrees')
thr = text('Proofs18CoverThresholdsSharp')
tb = text('Proofs18CoverTightBase')
parts = [
    between(deg, '/-- The envelope after one step (no threshold). -/',
            '/-- The polynomial envelope of the degree-`(k+2)` bound. -/'),
    between(thr, '/-- The envelope after one step, with the threshold, without the cubic branch. -/',
            '/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/'),
    between(tb, '/-- The standing hypotheses at the tight base budget. -/',
            '/-! ### The envelopes at the tight base budget -/'),
    between(tb, '/-- The Theorem 18.1 envelope at the tight base budget. -/',
            '/-- The Theorem 18.2 envelope at the tight base budget. -/'),
    between(tb, 'theorem polyEnvBound_allT', 'theorem envBound_allT'),
    between(thr, '/-- The Theorem 18.2 envelope at the tight base budget, without the cubic branch. -/',
            'theorem envStepCTx_le_tight'),
]
body = '\n'.join(parts)
REN = [('envStepCTx', 'envStepFTx'), ('envBound_stepCx', 'envBound_stepFx'),
       ('polyEnvBound_stepC', 'polyEnvBound_stepF'), ('envStepC', 'envStepF'),
       ('polyGenMuT_succ', 'polyGenMuF_succ'), ('polyGenMuT', 'polyGenMuF'),
       ('genMuX_succ', 'genMuXF_succ'), ('genMuX', 'genMuXF'),
       ('polyEnvBound_allT', 'polyEnvBound_allF'), ('envBound_allX', 'envBound_allXF'),
       ('tightHyp_of_profiles', 'tightHyp_of_profiles_fejer'),
       ('polyCoverAt_class68', 'polyCoverAt_class23'), ('uDeg68', 'uDeg23'),
       ('GenParamsC', 'GenParamsF'), ('densDegC', 'densDegF'), ('expDegC', 'expDegF'),
       ('threshDegC', 'threshDegF'), ('yIn_boundsC', 'yIn_boundsF'), ('Eloc_inv_leC', 'Eloc_inv_leF'),
       ('Tloc_le_expC', 'Tloc_le_expF')]
for a, b in REN:
    body = re.sub(r'\b' + a + r'\b', b, body)
bad = [l for l in body.split('\n') if re.search(r'GenParamsC|uDeg68|class68|\w+C\b|\bpolyGenMuT\b|\bgenMuX\b', l)
       and not re.search(r'NoC\b', l)]
bad = [l for l in bad if not re.search(r'\bP\.CHyp\b', l) or re.search(r'GenParamsC|uDeg68', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs18CoverExponentsFejer
import GowersSzemeredi.Proofs18CoverThresholdsSharp

/-! **Theorem 18.1 at `d + 6` and Theorem 18.2 / Corollary 18.7 at `L + 4`,
from the recurrence profiles, under the Fejér θ₁** (Notes L.16d).

The Section 18 envelope of `Proofs18CoverTightBase` and
`Proofs18CoverThresholdsSharp` at the parameters `GenParamsF`: class covers
at degree `uDeg23 l` (`polyCoverAt_class23`), the Fejér θ₁ and the tight
radius in the single-piece step, and the tight base budget `tightMu0`. The
step lemmas and the recursions are generated from the corpus by a script;
the closed forms are new.

One step now costs `101·2^k + 4(k+3)² + k + 39`
(`envStepF_le_tight`, `envStepFTx_le_tight`): the vertex covers `23·2^k`,
the base budget `32·2^k` and the two slice controls `2·23·2^k`, against the
printed `68 + 32 + 136 = 236`. So the envelopes grow like `202·2^k`, below
the `256·2^k` that `d + 6` and `L + 4` allow
(`models/model_fejer_envelope_exact.py`: at most `219·2^k`):
* `polyGenMuF_le`, `genMuXF_le`: at most `230·2^k` for `k ≥ 4`;
* `theorem_18_1_d6_of_profiles_cover`: **Theorem 18.1 at every degree
  `d ≥ 4` with exponent `α^(2^(2^(d+6)))`** (printed `d + 10`, corpus best
  `d + 7`);
* `theorem_18_2_L4_all_of_profiles_cover`,
  `corollary_18_7_L4_all_of_profiles_cover`: **Theorem 18.2 and
  Corollary 18.7 at every length `L ≥ 6` with `L + 4`** (printed `L + 9`,
  corpus best `L + 5`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

'''

TAIL = '''
/-! ### Closed forms -/

/-- One step at the tight base budget costs `101·2^k` plus a polynomial. -/
theorem envStepF_le_tight (k μ : Nat) :
    envStepF k (tightMu0 k) (genMuK k) μ ≤ μ + 101 * 2 ^ k + 4 * (k + 3) ^ 2 + k + 39 := by
  unfold envStepF GenParamsF.densDegF GenParamsF.expDegF GenParamsF.rhoDegF tightMu0 tightMuV
    genMuK fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem envStepFTx_le_tight (k μ : Nat) :
    envStepFTx k (tightMu0 k) (genMuK k) μ ≤ μ + 101 * 2 ^ k + 4 * (k + 3) ^ 2 + k + 39 := by
  unfold envStepFTx GenParamsF.densDegF GenParamsF.threshDegF GenParamsF.expDegF
    GenParamsF.rhoDegF tightMu0 tightMuV genMuK fixDeg
  rw [two_pow_six_mul, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem envStepFTx_ge_tight (k μ : Nat) :
    μ + 101 * 2 ^ k ≤ envStepFTx k (tightMu0 k) (genMuK k) μ := by
  unfold envStepFTx GenParamsF.densDegF GenParamsF.rhoDegF tightMu0 tightMuV fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem polyGenMuF_small : polyGenMuF 2 + 1 ≤ 2 ^ (4 + 6) ∧ polyGenMuF 3 + 1 ≤ 2 ^ (5 + 6) ∧
    polyGenMuF 4 ≤ 230 * 2 ^ 4 := by
  decide

/-- **The Theorem 18.1 envelope under the Fejér θ₁ is `≤ 230·2^k`**, `k ≥ 4`. -/
theorem polyGenMuF_le : ∀ k, 4 ≤ k → polyGenMuF k ≤ 230 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuF_small.2.2
  | succ k hk ih =>
    rw [polyGenMuF_succ (by omega)]
    have h1 := envStepF_le_tight (k + 1) (polyGenMuF k)
    have h2 := sq_le_two_pow_four k hk
    have h3 : 16 ≤ 2 ^ k := le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hk)
    have h4 := Nat.lt_two_pow_self (n := k)
    rw [show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 4) ^ 2 = s at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXF_small : genMuXF 2 + 2 * 6 + 14 ≤ 2 ^ (6 + 4) ∧
    genMuXF 3 + 2 * 7 + 14 ≤ 2 ^ (7 + 4) ∧ genMuXF 4 ≤ 230 * 2 ^ 4 := by
  decide

/-- **The Theorem 18.2 envelope under the Fejér θ₁ is `≤ 230·2^k`**, `k ≥ 4`. -/
theorem genMuXF_le : ∀ k, 4 ≤ k → genMuXF k ≤ 230 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuXF_small.2.2
  | succ k hk ih =>
    rw [genMuXF_succ (by omega)]
    have h1 := envStepFTx_le_tight (k + 1) (genMuXF k)
    have h2 := sq_le_two_pow_four k hk
    have h3 : 16 ≤ 2 ^ k := le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hk)
    have h4 := Nat.lt_two_pow_self (n := k)
    rw [show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 4) ^ 2 = s at *
    generalize 2 ^ k = x at *
    omega

theorem genMuXF_ge : ∀ k, 2 ≤ k → 101 * 2 ^ k ≤ genMuXF k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuXF_succ (by omega)]
  have := envStepFTx_ge_tight (j + 1) (genMuXF j)
  omega

/-! ### The headline statements -/

/-- **Theorem 18.1 at every degree `d ≥ 4` with exponent `α^(2^(2^(d+6)))`**,
from the recurrence profiles and a phase partition. -/
theorem theorem_18_1_d6_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd4 : 4 ≤ d) : Theorem181AtSharp 6 d := by
  have henv := polyEnvBound_allF Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  rcases Nat.lt_or_ge d 6 with h | h
  · obtain ⟨h4, h5, -⟩ := polyGenMuF_small
    interval_cases d
    · exact h4
    · exact h5
  · have hle := polyGenMuF_le (d - 2) (by omega)
    have h2 : 2 ^ (d + 6) = 256 * 2 ^ (d - 2) := by
      rw [show d + 6 = (d - 2) + 8 by omega, pow_add]; ring
    rw [h2]
    have := Nat.one_le_two_pow (n := d - 2)
    omega

/-- **Theorem 18.2 at every length `L ≥ 6` with `L + 4` in the threshold**,
from the recurrence profiles. -/
theorem theorem_18_2_L4_all_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) : Theorem182AtSharp 4 L := by
  have henv := envBound_allXF Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXF_ge (L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h4 : 4 ≤ 2 ^ (L - 4) :=
    le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h42 : 42 ≤ genMuXF (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXF (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXF (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  rcases Nat.lt_or_ge L 8 with hL | hL
  · obtain ⟨h6, h7, -⟩ := genMuXF_small
    interval_cases L
    · exact h6
    · exact h7
  · have hle := genMuXF_le (L - 4) (by omega)
    have h16 : 16 ≤ 2 ^ (L - 4) :=
      le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 2 ^ (L + 4) = 256 * 2 ^ (L - 4) := by
      rw [show L + 4 = (L - 4) + 8 by omega, pow_add]; ring
    rw [h2]
    omega

/-- **Corollary 18.7 at every length `L ≥ 6` with `L + 4`**, from the profiles. -/
theorem corollary_18_7_L4_all_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL6 : 6 ≤ L) : Corollary187AtSharp 4 L :=
  (theorem_18_2_L4_all_of_profiles_cover Kc pc hK hp hrec hconst hL6).corollary_18_7

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs18CoverFejerHeadline.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
