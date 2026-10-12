"""Proofs16ClassPiecesWith: class pieces with (θ₁, ζ) as parameters."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs16ClassPieces.lean').read_text(encoding='utf-8')
i = s.index('theorem class_piece_data {k : Nat}')
j = s.rindex('end LeanProofs.GowersSzemeredi')
thm = s[i:j]


def sub(t, pairs):
    for a, b in pairs:
        assert a in t, ('missing', a[:90])
        t = t.replace(a, b)
    return t


thm = sub(thm, [
    ('theorem class_piece_data {k : Nat}', 'theorem class_piece_data_with {k : Nat}'),
    ('    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)\n'
     '    {N : Nat} [NeZero N] [Fact N.Prime] (hN : classPieceThr Thr theta gamma k ≤ N)\n',
     '    {t1 zeta gamma : Real} (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)\n'
     '    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)\n'
     '    (hz0 : 0 < zeta) (hg : 0 < gamma) (hg1 : gamma ≤ 1)\n'
     '    {N : Nat} [NeZero N] [Fact N.Prime] (hN : classPieceThrW Thr t1 gamma k ≤ N)\n'),
    ('  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds k ht ht1 hg hg1\n',
     '  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds_with ha0 haS\n'),
    ('  obtain ⟨hθ\'pos, hθ\'le⟩ := classBudget_pos_le k ht ht1 hg hg1\n',
     '  obtain ⟨hθ\'pos, hθ\'le⟩ := classBudgetW_pos_le k ha0 haS\n'),
    ('    rw [hθ\'def, classBudget]; field_simp\n', '    rw [hθ\'def, classBudgetW]; field_simp\n'),
    ('  set δ := classDelta theta gamma k with hδdef\n'
     '  have hδeq : section16Delta (section16ThetaOne theta gamma k) = δ := rfl\n'
     '  rw [hδeq] at hδpos hδle\n',
     '  set δ := section16Delta t1 with hδdef\n'),
    ('    section16_dense_induced_selection_of_arrangements (k := k) (Fact.out : N.Prime) theta gamma\n'
     '      B phi ht ht1 hg hg1 hBarr\n',
     '    section16_dense_induced_selection_with (k := k) (Fact.out : N.Prime) t1 zeta\n'
     '      B phi ha0 haS hzeta hz0 hBarr\n'),
    ('lemma_16_7_holds N k theta gamma B phi H Y phiPrime', 'lemma_16_7_with t1 zeta hθ₁pos.le B phi H Y phiPrime'),
])
thm = thm.replace('classBudget theta gamma k', 'classBudgetW t1 k')
thm = thm.replace('classDelta theta gamma k', 'section16Delta t1')
thm = thm.replace('section16ThetaOne theta gamma k', 't1').replace('section16Zeta theta gamma k', 'zeta')
bad = [l for l in thm.split('\n') if re.search(r'section16ThetaOne|section16Zeta|\btheta\b|classBudget\b|classDelta\b|\bht\b|\bht1\b', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs16ClassPieces
import GowersSzemeredi.Proofs16DenseSelectionWith
import GowersSzemeredi.Proofs16PolyPieceTwoDataWith

/-! **Class pieces with `(θ₁, ζ)` as parameters** (Notes L.16d).

`class_piece_data` (`Proofs16ClassPieces`) builds one piece of the next
uniform class from an arrangement-dense subset. It fixes the printed
`θ₁ = section16ThetaOne θ γ k` and `ζ = section16Zeta θ γ k`, through the
budget `classBudget = θ₂(θ₁)/2^(k+2)`, the spectrum parameter
`classDelta = δ(θ₁)` and the radius. Here:
* `classBudgetW t1 k = θ₂(t1)/2^(k+2)` and
  `classPieceThrW Thr t1 γ k` are the parameterized budget and threshold.
  At the printed `t1` they equal `classBudget` and `classPieceThr` by `rfl`.
* `class_piece_data_with` is the producer with `(t1, zeta)`, under
  `0 < t1/4 ≤ 1/36`, `ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6`, and
  `0 < ζ`. It is generated from the corpus proof by a script with a guard
  that no printed parameter survives.

`ClassPiece` itself is generic in the radius and the budgets. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The class budget `θ₂(t1)/2^(k+2)` at density `t1`. -/
def classBudgetW (t1 : Real) (k : Nat) : Real := section16ThetaTwo t1 / 2 ^ (k + 2)

/-- The class thresholds a piece needs, at density `t1`. -/
def classPieceThrW (Thr : Real → Real → Real) (t1 gamma : Real) (k : Nat) : Real :=
  max (Thr (classBudgetW t1 k) (section16Delta t1)) (Thr (classBudgetW t1 k) gamma)

theorem classBudgetW_printed (theta gamma : Real) (k : Nat) :
    classBudgetW (section16ThetaOne theta gamma k) k = classBudget theta gamma k := rfl

theorem classPieceThrW_printed (Thr : Real → Real → Real) (theta gamma : Real) (k : Nat) :
    classPieceThrW Thr (section16ThetaOne theta gamma k) gamma k = classPieceThr Thr theta gamma k := rfl

theorem classBudgetW_pos_le {t1 : Real} (k : Nat) (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36) :
    0 < classBudgetW t1 k ∧ classBudgetW t1 k ≤ 1 := by
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le_with ha0 haS
  have h2 : (1 : Real) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
  unfold classBudgetW
  refine ⟨div_pos h0 (by positivity), ?_⟩
  rw [div_le_one (by positivity)]
  linarith

'''
out = HEADER + thm + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs16ClassPiecesWith.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
