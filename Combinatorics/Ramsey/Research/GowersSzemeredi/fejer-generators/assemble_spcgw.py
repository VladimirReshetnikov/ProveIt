"""Proofs16SinglePieceCoverGlobalWith: the joint-cover single-piece lift with (θ₁, ζ) as parameters."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs16SinglePieceCoverGlobal.lean').read_text(encoding='utf-8')
i = s.index('/-- **The single-piece lift from global-to-local covers, with the remainder')
j = s.rindex('end LeanProofs.GowersSzemeredi')
thm = s[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


thm = sub(thm, [
    ('theorem single_piece_lift_global_cover {k : Nat} (hk : 1 ≤ k) {theta gamma : Real}\n'
     '    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)\n',
     'theorem single_piece_lift_global_cover_with {k : Nat} (hk : 1 ≤ k) {t1 zeta gamma : Real}\n'
     '    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)\n'
     '    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)\n'
     '    (hz0 : 0 < zeta) (hz2 : zeta ≤ 1 / 2) (hg : 0 < gamma) (hg1 : gamma ≤ 1)\n'),
    ('  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds k ht ht1 hg hg1\n'
     '  obtain ⟨hζpos, hζle⟩ := section16Zeta_pos_le_one_div_32 k ht ht1 hg hg1\n'
     '  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le k ht ht1 hg hg1\n',
     '  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds_with ha0 haS\n'
     '  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le_with ha0 haS\n'),
    ('    section16_dense_induced_selection_of_arrangements (Fact.out : N.Prime) theta gamma B phi\n'
     '      ht ht1 hg hg1 hB\n',
     '    section16_dense_induced_selection_with (k := k) (Fact.out : N.Prime) t1 zeta B phi\n'
     '      ha0 haS hzeta hz0 hB\n'),
    ('lemma_16_7_holds N k theta gamma B phi H Y phiPrime', 'lemma_16_7_with t1 zeta hθ₁pos.le B phi H Y phiPrime'),
    ('  exact single_piece_lift_core_rem hk hζpos (by linarith)', '  exact single_piece_lift_core_rem hk hz0 hz2'),
    ('coverPrec_pos_le theta gamma k ht ht1 hg hg1', 'coverPrecW_pos_le t1 k ha0 haS'),
    ('nonTop_coverPrec_sum_le theta gamma k ht ht1 hg hg1', 'nonTop_coverPrecW_sum_le t1 k ha0 haS'),
    ('coverRho1_pos_le Qb hQb theta gamma k ht ht1 hg hg1', 'coverRho1W_pos_le Qb hQb t1 gamma k ha0 haS'),
    ('    rw [hθ\'def, globalBudget, ← hθ₂def]\n', '    rw [hθ\'def, globalBudgetW, ← hθ₂def]\n'),
    ('    rw [globalTheta2, ← hθ₂def]\n', '    rw [globalTheta2W, ← hθ₂def]\n'),
    ('      rw [coverRho1, hcc]\n', '      rw [coverRho1W, hcc]\n'),
])
thm = thm.replace('coverCount_pos Qb hQb theta gamma k', 'coverCountW_pos Qb hQb t1 gamma k')
thm = thm.replace('globalBudget theta gamma k', 'globalBudgetW t1 k')
thm = thm.replace('globalTheta2 theta gamma k', 'globalTheta2W t1')
thm = thm.replace('coverPrec theta gamma k', 'coverPrecW t1 k')
thm = thm.replace('coverCount Qb theta gamma k', 'coverCountW Qb t1 gamma k')
thm = thm.replace('coverRho1 Qb theta gamma k', 'coverRho1W Qb t1 gamma k')
thm = thm.replace('coverExp Eb theta gamma k', 'coverExpW Eb t1 gamma k')
thm = thm.replace('coverRemWidth Eb theta gamma k N', 'coverRemWidthW Eb t1 gamma k N')
thm = thm.replace('section16ThetaOne theta gamma k', 't1').replace('section16Zeta theta gamma k', 'zeta')
thm = thm.replace("rw [hθ'def, globalBudget, div_le_one", "rw [hθ'def, globalBudgetW, div_le_one")
thm = sub(thm, [('rw [hθ\'def, globalBudget]', 'rw [hθ\'def, globalBudgetW]'),
                ('⟨by rw [globalTheta2]; positivity, by rw [globalTheta2]; linarith⟩',
                 '⟨by rw [globalTheta2W]; positivity, by rw [globalTheta2W]; linarith⟩')])
bad = [l for l in thm.split('\n') if re.search(
    r'section16ThetaOne|section16Zeta|\btheta\b(?! :=)|\bht\b|\bht1\b|\bglobalBudget\b|\bglobalTheta2\b|'
    r'\bcoverPrec\b|\bcoverCount\b|\bcoverRho1\b|\bcoverExp\b|\bcoverRemWidth\b|_holds\b|of_arrangements', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs16SinglePieceCoverGlobal
import GowersSzemeredi.Proofs16DenseSelectionWith
import GowersSzemeredi.Proofs16PolyPieceTwoDataWith

/-! **The joint-cover single-piece lift with `(θ₁, ζ)` as parameters**
(Notes L.16d).

`single_piece_lift_global_cover` (`Proofs16SinglePieceCoverGlobal`) is the
single-piece lift of the Section 18 inverse step. It fixes the printed
`θ₁ = section16ThetaOne θ γ k` and `ζ = section16Zeta θ γ k` through
Lemmas 16.5 and 16.7 and through the budgets
`globalBudget = θ₂(θ₁)/(2(2^k+1))` and `globalTheta2 = θ₂(θ₁)/2`. Here:
* `globalBudgetW t1 k`, `globalTheta2W t1`, `coverPrecW`, `coverCountW`,
  `coverRho1W`, `coverExpW`, `coverRemWidthW`: the same quantities at density
  `t1`; at the printed `t1` they are the corpus's by `rfl` (`…_printed`);
* `single_piece_lift_global_cover_with`: the lift with `(t1, zeta)`, under
  `0 < t1/4 ≤ 1/36`, `ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6`, and
  `0 < ζ ≤ 1/2`. It uses `section16_dense_induced_selection_with` and
  `lemma_16_7_with`, and is generated from the corpus proof by a script
  with a guard that no printed parameter survives. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The deletion budget of each good set at density `t1`: `θ₂(t1)/(2(2^k+1))`. -/
def globalBudgetW (t1 : Real) (k : Nat) : Real := section16ThetaTwo t1 / (2 * (2 ^ k + 1))

/-- The density of the retained good domain at density `t1`: `θ₂(t1)/2`. -/
def globalTheta2W (t1 : Real) : Real := section16ThetaTwo t1 / 2

/-- The common precision of the vertex covers, `θ₂(t1)/2^(k+1)`. -/
def coverPrecW (t1 : Real) (k : Nat) : Real := globalTheta2W t1 / 2 ^ (k + 1)

/-- The product of the vertex cover counts at density `t1`. -/
def coverCountW (Qb : Nat → Real → Real → Real → Real) (t1 gamma : Real) (k : Nat) : Real :=
  ∏ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true),
    max (Qb (section16VertexDirections e).card gamma (globalBudgetW t1 k)
      (coverPrecW t1 k)) ((3 ^ (k + 1) : Nat) : Real)

/-- The remainder density from joint vertex covers at density `t1`. -/
def coverRho1W (Qb : Nat → Real → Real → Real → Real) (t1 gamma : Real) (k : Nat) : Real :=
  globalTheta2W t1 / 2 / coverCountW Qb t1 gamma k

/-- The exponent of the remainder width at density `t1`. -/
def coverExpW (Eb : Nat → Real → Real → Real → Real) (t1 gamma : Real) (k : Nat) : Real :=
  ∏ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true),
    Eb (section16VertexDirections e).card gamma (globalBudgetW t1 k)
      (coverPrecW t1 k) / 16 ^ (k + 1 - (section16VertexDirections e).card)

/-- The remainder width at density `t1`. -/
def coverRemWidthW (Eb : Nat → Real → Real → Real → Real) (t1 gamma : Real) (k N : Nat) : Nat :=
  ⌈(N : Real) ^ coverExpW Eb t1 gamma k⌉₊

theorem globalBudgetW_printed (theta gamma : Real) (k : Nat) :
    globalBudgetW (section16ThetaOne theta gamma k) k = globalBudget theta gamma k := rfl

theorem globalTheta2W_printed (theta gamma : Real) (k : Nat) :
    globalTheta2W (section16ThetaOne theta gamma k) = globalTheta2 theta gamma k := rfl

theorem coverRho1W_printed (Qb : Nat → Real → Real → Real → Real) (theta gamma : Real) (k : Nat) :
    coverRho1W Qb (section16ThetaOne theta gamma k) gamma k = coverRho1 Qb theta gamma k := rfl

theorem coverRemWidthW_printed (Eb : Nat → Real → Real → Real → Real) (theta gamma : Real) (k N : Nat) :
    coverRemWidthW Eb (section16ThetaOne theta gamma k) gamma k N = coverRemWidth Eb theta gamma k N := rfl

theorem globalTheta2W_pos_le {t1 : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < globalTheta2W t1 ∧ globalTheta2W t1 ≤ 1 := by
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le_with ha0 haS
  exact ⟨by rw [globalTheta2W]; positivity, by rw [globalTheta2W]; linarith⟩

theorem coverPrecW_pos_le (t1 : Real) (k : Nat) (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < coverPrecW t1 k ∧ coverPrecW t1 k ≤ 1 := by
  obtain ⟨h0, h1⟩ := globalTheta2W_pos_le ha0 haS
  have h2 : (1 : Real) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  refine ⟨by unfold coverPrecW; positivity, ?_⟩
  unfold coverPrecW
  rw [div_le_one (by positivity)]
  linarith

/-- The precisions of the `2^k - 1` vertices add up to at most `θ₂(t1)/2`. -/
theorem nonTop_coverPrecW_sum_le (t1 : Real) (k : Nat) (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    ((2 : Real) ^ k - 1) * coverPrecW t1 k ≤ globalTheta2W t1 / 2 := by
  obtain ⟨h0, -⟩ := globalTheta2W_pos_le ha0 haS
  unfold coverPrecW
  have h2 : (0 : Real) < 2 ^ (k + 1) := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ h2 (by norm_num), pow_succ]
  nlinarith

theorem coverCountW_pos (Qb : Nat → Real → Real → Real → Real)
    (_hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (t1 gamma : Real) (k : Nat) : 0 < coverCountW Qb t1 gamma k := by
  unfold coverCountW
  refine Finset.prod_pos fun e _ => lt_of_lt_of_le ?_ (le_max_right _ _)
  positivity

theorem one_le_coverCountW (Qb : Nat → Real → Real → Real → Real)
    (t1 gamma : Real) (k : Nat) : 1 ≤ coverCountW Qb t1 gamma k := by
  unfold coverCountW
  calc (1 : Real) = ∏ _e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true),
        (1 : Real) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun e _ => le_trans
        (by exact_mod_cast Nat.one_le_pow _ _ (by norm_num)) (le_max_right _ _)

theorem coverRho1W_pos_le (Qb : Nat → Real → Real → Real → Real)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (t1 gamma : Real) (k : Nat) (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < coverRho1W Qb t1 gamma k ∧ coverRho1W Qb t1 gamma k ≤ 1 := by
  obtain ⟨h0, h1⟩ := globalTheta2W_pos_le ha0 haS
  have hc := one_le_coverCountW Qb t1 gamma k
  have hc0 := coverCountW_pos Qb hQb t1 gamma k
  unfold coverRho1W
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hc0]
  linarith

'''
out = HEADER + thm + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs16SinglePieceCoverGlobalWith.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
