"""Proofs16SplitStepFejer: the split step and every dimension under the Fejér θ₁ and the tight radius."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs16SplitStepBounds.lean').read_text(encoding='utf-8')
i = s.index('/-! ### The split degrees -/')
j = s.rindex('end LeanProofs.GowersSzemeredi')
body = s[i:j]


def cut(t, start, end_marker):
    a = t.index(start)
    b = t.index(end_marker, a + len(start))
    return t[:a] + t[b:]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


# generic pieces are reused from Proofs16SplitStepBounds
body = cut(body, '/-- The count control of a split class, as a named function. -/',
           '/-- **The remainder count, in two bases.** -/')
body = cut(body, 'theorem pow_le_exp_mul', '/-- **The width exponent of the next class, in two bases.** -/')
body = cut(body, 'theorem splitCnt_controls', '/-- **The split step of route (II).**')
body = sub(body, [
    ('/-- The family exponent of the next split class. -/\ndef splitStepA (k a : Nat) : Nat := sCountN k a + sExpN k a\n\n', ''),
    ('/-- The family exponent of the count of the next class. -/\ndef sCountN (k a : Nat) : Nat := 1 + 2 * sSN k a + 2 * sPbN k a\n\n', ''),
    ('/-- The family exponent of the width exponent of the next class. -/\ndef sExpN (k a : Nat) : Nat := 1 + sLN k a + sPbN k a\n\n', ''),
])
body = '\n'.join(l for l in body.split('\n')
                 if not re.match(r'def s(QrN|SN|PbN|ErN|BqN|LN) ', l))

T1 = 'fejerThetaOne theta gamma k'
B = '(fejerThetaOne_bounds k ht ht1 hg hg1)'
body = body.replace('classBudget_pos_le k ht ht1 hg hg1', f'classBudgetW_pos_le k {B}.1 {B}.2')
body = body.replace('section16_theta_delta_bounds k ht ht1 hg hg1', f'section16_theta_delta_bounds_with {B}.1 {B}.2')
body = body.replace('section16Zeta_inv_le_gen k hg ht', 'tightZeta_fejer_inv_le_gen k hg hg1 ht ht1')
body = body.replace('classPieces_le_stepP', 'classPiecesFejer_le_gen')
body = body.replace('stepP_ge k', 'fejerStepP_ge k')
body = body.replace('classBudget theta gamma k', f'classBudgetW ({T1}) k')
body = body.replace('classDelta theta gamma k', f'section16Delta ({T1})')
body = body.replace('section16Zeta theta gamma k', f'tightZeta ({T1} / 4)')
for a, b in [('stepP', 'fejerStepP'), ('stepT', 'fejerStepT'), ('classPieces', 'classPiecesFejer'),
             ('StepPiece', 'StepPieceFejer'), ('stepPieceGraphs', 'stepPieceFejerGraphs'),
             ('class_step_decomp', 'class_step_decomp_fejer'),
             ('class_step_cover_gen', 'class_step_cover_gen_fejer'),
             ('classStepThreshold_eq', 'classStepThresholdFejer_eq'), ('classStepThr', 'classStepThrFejer'),
             ('stepThrDeg', 'fejerStepThrDeg'), ('step_thr_le', 'step_thr_le_fejer'),
             ('twoDiv_gamma_le', 'twoDiv_gamma_le_fejer'), ('twoDiv_delta_le', 'twoDiv_delta_le_fejer'),
             ('split_step_basics', 'split_step_basics_fejer'), ('split_Qr_le', 'split_Qr_le_fejer'),
             ('split_samples_le', 'split_samples_le_fejer'), ('split_count_le', 'split_count_le_fejer'),
             ('split_exp_inv_le', 'split_exp_inv_le_fejer'),
             ('splitUniformClass_succ', 'splitUniformClass_succ_fejer'), ('splitStepD', 'splitStepDFejer')]:
    body = re.sub(r'\b' + a + r'\b', b, body)
body = re.sub(r'\bs(StepY|QrW|SW|PbW|CountW|EbW|ErW|BqW|LW|ZW|ExpW)\b', r'fs\1', body)
bad = [l for l in body.split('\n') if re.search(
    r'classBudget\b|classBudget_|classDelta\b|classDelta_|section16Zeta|section16ThetaOne|\bstepP\b|\bstepT\b|'
    r'2 \^ \(2 \^|lemma156|\bclassStepThreshold\b|\bclassStepThr\b|section16_theta_delta_bounds k|'
    r'\bclassPieces\b|\bStepPiece\b|\bstepPieceGraphs\b|\bstepThrDeg\b|\bsplitStepD\b|'
    r'\bs(StepY|QrW|SW|PbW|CountW|EbW|ErW|BqW|LW|ZW|ExpW)\b', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs16SplitStepBounds
import GowersSzemeredi.Proofs16ClassStepDegreesFejer
import GowersSzemeredi.Proofs16SplitFejerDegrees
import GowersSzemeredi.Proofs16UniformCoverTwoFejer

/-! **Split uniform classes in every dimension under the Fejér θ₁ and the
tight radius** (Notes L.16d).

The Fejér instance of `Proofs16SplitStepBounds` and
`Proofs16SplitAllDimensions`. The step is generated from the corpus by a
script with a guard that no printed parameter survives:
* the parameter-side degrees `fsStepY … fsExpW`: the corpus's with
  `fejerStepP k = 64F`, `fejerStepT k = 22F + 105` in place of
  `stepP k`, `stepT k`, where `F = fejerProductExponent k`. The family-side
  degrees (`sQrN … sExpN`, `splitStepA`) do not see Section 16 and are
  reused;
* `split_count_le_fejer`, `split_exp_inv_le_fejer`;
* `splitUniformClass_succ_fejer`: the split step with family exponent
  `splitStepA k a` and parameter degree `splitStepDFejer k a D`.
  `splitStepDFejer_eq` identifies the latter with
  `splitStepDWith (fejerStepP k) (fejerStepT k) k a D`
  (`Proofs16SplitFejerDegrees`).

From the dimension-two seed `splitUniformClass_two_fejer` (`a = D = 2^46`),
`splitUniformClass_all_fejer` gives a split class in every dimension
`k ≥ 2` with degrees `splitPairWith (2^46) (2^46) k`. By
`split_pair_with_bounds_fourteen`, `log₂ D_k ≤ 22·2^k`
(`split_pair_fejer_bound`), against `75·2^k` (`split_pair_bounds`) for the
printed parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

'''

TAIL = '''theorem splitStepDFejer_eq (k a D : Nat) :
    splitStepDFejer k a D = splitStepDWith (fejerStepP k) (fejerStepT k) k a D := by
  unfold splitStepDWith wCountW wExpW wThrDeg wZW wLW wBqW wErW wEbW wPbW wSW wStepY
    splitStepDFejer fsCountW fsExpW fejerStepThrDeg fsZW fsLW fsBqW fsErW fsEbW fsPbW fsSW fsQrW fsStepY
  rfl

/-! ### Every dimension -/

/-- The dimension-two seed under the Fejér θ₁: `2^46` (printed `2^132`). -/
def splitSeedFejer : Nat := 2 ^ 46

theorem split_pair_fejer_basic : ∀ k, 2 ≤ k →
    1 ≤ (splitPairWith splitSeedFejer splitSeedFejer k).1 ∧
      1 ≤ (splitPairWith splitSeedFejer splitSeedFejer k).2 := by
  intro k hk
  have h := split_pair_with_bounds 14 (seedA := splitSeedFejer) (seedD := splitSeedFejer)
    Nat.one_le_two_pow Nat.one_le_two_pow
    (by unfold splitSeedFejer; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (by unfold splitSeedFejer; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)) k hk
  exact ⟨h.1, h.2.1⟩

/-- **The parameter degree of the Fejér split class**: `log₂ D_k ≤ 22·2^k`. -/
theorem split_pair_fejer_bound : ∀ k, 2 ≤ k →
    (splitPairWith splitSeedFejer splitSeedFejer k).2 ≤ 2 ^ (22 * 2 ^ k) :=
  split_pair_with_bounds_fourteen Nat.one_le_two_pow Nat.one_le_two_pow
    (by unfold splitSeedFejer; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (by unfold splitSeedFejer; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))

/-- **A split uniform class in every dimension `k ≥ 2` under the Fejér θ₁
and the tight radius**, with degrees `splitPairWith (2^46) (2^46) k`, so
`log₂ D_k ≤ 22·2^k` (`split_pair_fejer_bound`). -/
theorem splitUniformClass_all_fejer (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (SplitUniformClass k (classV Kc pc k) (splitPairWith splitSeedFejer splitSeedFejer k).1
        (splitPairWith splitSeedFejer splitSeedFejer k).2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitPairWith_two]
    exact splitUniformClass_two_fejer (hK 1) (hp 1) (hlem 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl) (by unfold splitSeedFejer; exact le_rfl)
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    obtain ⟨ha, hD⟩ := split_pair_fejer_basic k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitPairWith_succ _ _ hk, ← splitStepDFejer_eq]
    exact splitUniformClass_succ_fejer (by omega) hV1 ha hD C (hK k) (hp k) (hlem k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs16SplitStepFejer.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
