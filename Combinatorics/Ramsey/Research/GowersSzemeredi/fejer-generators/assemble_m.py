"""Proofs18TightClassesFejerM: the split step with max in place of sum (Notes L.16w)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


def sub(t, pairs):
    for a, b in pairs:
        assert t.count(a) >= 1, ('missing', a[:120])
        t = t.replace(a, b)
    return t


MAXLE = 'first | omega | simp only [le_max_iff, le_refl, true_or, or_true]'

# --- the step lemma
sf = text('Proofs16SplitStepFejer')
a = sf.index('theorem splitUniformClass_succ_fejer ')
b = sf.index('theorem splitStepDFejer_eq')
step = sf[a:b]
step = sub(step, [
    ('theorem splitUniformClass_succ_fejer ', 'theorem splitUniformClass_succ_fejer_max '),
    ('(splitStepA k a) (splitStepDFejer k a D)', '(splitStepAMax k a) (splitStepDMaxF k a D)'),
    ('(by unfold splitStepDFejer; omega)', f'(by unfold splitStepDMaxF; {MAXLE})'),
    ('(by unfold splitStepA; omega)', f'(by unfold splitStepAMax; {MAXLE})'),
    ("(a' := splitStepA k a)", "(a' := splitStepAMax k a)"),
    ("(b' := splitStepDFejer k a D)", "(b' := splitStepDMaxF k a D)"),
])
assert 'splitStepDFejer' not in step and 'splitStepA k' not in step.replace('splitStepAMax k', '')

# --- the quad invariant, the half invariant, the all-dimension class
s_ = text('Proofs18TightClassesFejerS')
a = s_.index('/-- **The split invariants at class constant `4` in every dimension `l ≥ 2`**')
b = s_.index('/-- The class degree at class constant `4`. -/')
quad_all = s_[a:b]
x_ = text('Proofs18TightClassesFejerX')
a = x_.index('/-- The exact twelfth dimension fits the invariant at constant `5/2`. -/')
b = x_.index('/-- The class log-degree: exact up to dimension `12`, constant `5/2` beyond. -/')
half = x_[a:b]
both = quad_all + half
both = both.replace('splitPairWith_succ', 'splitPairMax_succ').replace('splitPairWith_two', 'splitPairMax_two')
both = re.sub(r'\bsplitPairWith\b', 'splitPairMax', both)
both = sub(both, [
    ('theorem split_pair_small_quad ', 'theorem split_pair_max_quad '),
    ('split_pair_small_quad', 'split_pair_max_quad'),
    ('theorem splitUniformClass_all_small ', 'theorem splitUniformClass_all_max '),
    ('theorem split_pair_twelve_half ', 'theorem split_pair_max_twelve_half '),
    ('exact ⟨ha, hD, split_pair_twelve_half⟩', 'exact ⟨ha, hD, split_pair_max_twelve_half⟩'),
    ('theorem split_pair_small_half ', 'theorem split_pair_max_half '),
    ('(splitStepA_le ha)', '((splitStepAMax_le_sum k a).trans (splitStepA_le ha))'),
    ('(splitStepDWith_le ha hDp (fejerStepP_ge k))',
     '((splitStepDMaxWith_le_sum _ _ k a D).trans (splitStepDWith_le ha hDp (fejerStepP_ge k)))'),
    ('    · unfold splitStepA sCountN; omega\n    · unfold splitStepDWith wCountW; omega',
     '    · exact (show 1 ≤ sCountN k a by unfold sCountN; omega).trans (le_max_left _ _)\n'
     '    · exact (show 1 ≤ wCountW (fejerStepP k) k a D by unfold wCountW; omega).trans\n'
     '        ((le_max_left _ _).trans (le_max_left _ _))'),
    ('rw [splitPairMax_succ _ _ hk, ← splitStepDFejer_eq]', 'rw [splitPairMax_succ _ _ hk, ← splitStepDMaxF_eq]'),
    ('exact splitUniformClass_succ_fejer (by omega)', 'exact splitUniformClass_succ_fejer_max (by omega)'),
])
# the all-dimension class needs the quad invariant in the same pairs
assert 'splitStepA k' not in both.replace('splitStepAMax', '')

# --- the table lemmas, from Z
z_ = text('Proofs18TightClassesFejerZ')
a = z_.index('/-- The exact class log-degrees in dimensions `0, …, 14`. -/')
b = z_.index('/-- **The split degrees fit `uDegZ`**')
tab = z_[a:b]
tab = tab.replace('[17, 17, 49, 85, 136, 210, 326, 524, 881, 1550, 2841, 5371, 10375, 20323, 40154]',
                  '[17, 17, 49, 85, 134, 205, 317, 505, 842, 1472, 2684, 5057, 9746, 19064, 37637]')
for p, q in (('tTableZ', 'tTableM'), ('tDegZ', 'tDegM'), ('uDegZ', 'uDegM')):
    tab = tab.replace(p, q)
assert '40154' not in tab

FIT = '''/-- **The max-split degrees fit `uDegM`**, kernel-evaluated up to dimension `14`. -/
theorem split_pair_max_le_uDegM {l : Nat} (hl : 2 ≤ l) :
    (splitPairMax splitSeedSmallA splitSeedSmallD l).1 +
      (splitPairMax splitSeedSmallA splitSeedSmallD l).2 + l + 1 ≤ uDegM l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide +kernel
  · obtain ⟨-, -, hA, hD⟩ := split_pair_max_half l (by omega)
    unfold uDegM
    rw [tDegM_eq_of_ge h]
    set a := (splitPairMax splitSeedSmallA splitSeedSmallD l).1
    set D := (splitPairMax splitSeedSmallA splitSeedSmallD l).2
    set Y := 2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2) with hYdef
    have ha : a ≤ Y := by
      have h1 : a ≤ 2 ^ (5 * 2 ^ (l - 1)) :=
        le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
      exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hl1 : l + 1 ≤ Y := by
      have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
      have h2 : l + 1 ≤ 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 := by
        have : l + 1 ≤ (l + 4) ^ 2 := by nlinarith
        omega
      exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
    have h4 : 2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2) = 4 * Y := by
      rw [hYdef, pow_add]; ring
    rw [h4]
    omega

/-- **The class cover in dimension `l` at degree `uDegM l`.** -/
theorem polyCoverAt_classM (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDegM l)) (uExp (classV Kc pc l) (uDegM l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDegM
    exact Nat.pow_le_pow_right (by norm_num) (seventeen_le_tDegM 1)
  · obtain ⟨C⟩ := splitUniformClass_all_max Kc pc hK hp hlem l hl
    have hfit := split_pair_max_le_uDegM hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDegM l) (by omega) (by omega)
      (by omega)
    refine P0.weaken ?_ ?_ ?_
    · intro g t s hg hg1 ht ht1 hs hs1
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    · intro g t s _ _ _ _ _ _
      exact (uExp_pos_le _ _ g t s).1
    · intro g t s hg hg1 ht ht1 hs hs1
      show (uCount _ _ g t s)⁻¹ ≤ _
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]

/-- `tDegM ≤ tDegZ`: the max step never loses against the sum step. -/
theorem tDegM_le_tDegZ (l : Nat) : tDegM l ≤ tDegZ l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide
  · rw [tDegM_eq_of_ge h, tDegZ_eq_of_ge h]

'''

DEFS = '''/-- The family exponent of the next split class, combined by `max`. -/
def splitStepAMax (k a : Nat) : Nat := max (sCountN k a) (sExpN k a)

/-- The parameter degree of the next split class (Fejér inputs), combined by `max`. -/
def splitStepDMaxF (k a D : Nat) : Nat :=
  max (max (fsCountW k a D) (fsExpW k a D)) (fejerStepThrDeg k D)

/-- The parameter degree with general step inputs, combined by `max`. -/
def splitStepDMaxWith (P T k a D : Nat) : Nat :=
  max (max (wCountW P k a D) (wExpW P T k a D)) (wThrDeg P D)

theorem splitStepAMax_le_sum (k a : Nat) : splitStepAMax k a ≤ splitStepA k a := by
  unfold splitStepAMax splitStepA
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem splitStepDMaxWith_le_sum (P T k a D : Nat) :
    splitStepDMaxWith P T k a D ≤ splitStepDWith P T k a D := by
  unfold splitStepDMaxWith splitStepDWith
  refine max_le (max_le ?_ ?_) ?_ <;> omega

theorem splitStepDMaxF_eq (k a D : Nat) :
    splitStepDMaxF k a D = splitStepDMaxWith (fejerStepP k) (fejerStepT k) k a D := by
  unfold splitStepDMaxWith wCountW wExpW wThrDeg wZW wLW wBqW wErW wEbW wPbW wSW wStepY
    splitStepDMaxF fsCountW fsExpW fejerStepThrDeg fsZW fsLW fsBqW fsErW fsEbW fsPbW fsSW fsQrW fsStepY
  rfl

/-- The split recursion with the Fejér inputs, combined by `max`. -/
def splitPairMax (seedA seedD : Nat) : Nat → Nat × Nat
  | 0 => (seedA, seedD)
  | k + 1 => if k < 2 then (seedA, seedD)
      else (splitStepAMax k (splitPairMax seedA seedD k).1,
        splitStepDMaxWith (fejerStepP k) (fejerStepT k) k
          (splitPairMax seedA seedD k).1 (splitPairMax seedA seedD k).2)

theorem splitPairMax_two (seedA seedD : Nat) : splitPairMax seedA seedD 2 = (seedA, seedD) := by
  simp [splitPairMax]

theorem splitPairMax_succ (seedA seedD : Nat) {k : Nat} (hk : 2 ≤ k) :
    splitPairMax seedA seedD (k + 1) =
      (splitStepAMax k (splitPairMax seedA seedD k).1,
        splitStepDMaxWith (fejerStepP k) (fejerStepT k) k
          (splitPairMax seedA seedD k).1 (splitPairMax seedA seedD k).2) := by
  rw [splitPairMax, if_neg (by omega)]

'''

HEAD = '''import GowersSzemeredi.Proofs18TightClassesFejerZ

/-! **The split step combined by `max`** (Notes L.16w).

The split step bounds the count, the width exponent and the threshold of the
next class separately, and then takes one family exponent and one parameter
degree for all three. `splitStepA = sCountN + sExpN` and
`splitStepDFejer = countW + expW + thrDeg` add them. Since every control of a
split class is monotone in `(a, D)`, the `max` suffices:
* `splitUniformClass_succ_fejer_max`: the step at `splitStepAMax`,
  `splitStepDMaxF`;
* `splitPairMax`, `split_pair_max_quad`, `split_pair_max_half` (the
  invariants at class constants `4` and `5/2`, through
  `splitStepAMax_le_sum`, `splitStepDMaxWith_le_sum`), and
  `splitUniformClass_all_max`;
* `tDegM`: the exact table up to `l = 14`
  (`…, 842, 1472, 2684, 5057, 9746, 19064, 37637`, against
  `…, 881, 1550, 2841, 5371, 10375, 20323, 40154` for the sum), then
  `5·2^(l−1) + 3(l+4)² + 2`; `split_pair_max_le_uDegM`,
  `polyCoverAt_classM`, `tDegM_le_tDegZ`
(generated by `assemble_m.py`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

'''
out = HEAD + DEFS + step + '\n' + both + tab + FIT + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs18TightClassesFejerM.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
