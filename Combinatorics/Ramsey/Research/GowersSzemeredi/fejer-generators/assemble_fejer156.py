"""Assemble Proofs15FejerProduct.lean: Lemma 15.6 from the Fejér Lemma 15.5."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
src = (GS / 'Proofs15ProductToRestriction.lean').read_text(encoding='utf-8').split('\n')


def lines(a, b):
    return '\n'.join(src[a - 1:b])


helpers = lines(22, 29) + '\n\n' + lines(57, 109)
helpers = helpers.replace('lemma156_', 'fejer156_')

proof = lines(141, len(src))
assert proof.rstrip().endswith('end LeanProofs.GowersSzemeredi')
proof = proof.rstrip()[:-len('end LeanProofs.GowersSzemeredi')]
SUBS = [
    ('theorem lemma_15_6_holds : lemma_15_6 := by\n  unfold lemma_15_6\n',
     'theorem fejer_product_restriction : FejerProductRestriction := by\n  unfold FejerProductRestriction\n'),
    ('  let S : Nat := arrangementSelectionExponent k\n  let T : Nat := 2 ^ (2 ^ (k + 5))\n',
     '  let S : Nat := fejerSelectionExponent k\n  let T : Nat := fejerProductExponent k\n'),
    ('  obtain ⟨N0, hN0⟩ := lemma_15_5_holds k alpha beta eta hk halpha\n    hbeta heta heta_one\n',
     '  obtain ⟨N0, hN0⟩ := fejer_arrangement_restriction k alpha beta eta hk halpha\n    hbeta heta heta_one\n'),
    ('    exact lemma156_beta_total_exponent k hk\n',
     '    have hS1 : 1 ≤ S := by\n'
     '      dsimp only [S, fejerSelectionExponent]\n'
     '      exact Nat.one_le_iff_ne_zero.mpr (by positivity)\n'
     '    calc A * S + 15 ≤ (A + 15) * S := by nlinarith\n'
     '      _ ≤ 2 ^ (3 * k + 7) * S := Nat.mul_le_mul_right S (fejer156_beta_base_exponent k hk)\n'
     '      _ = T := rfl\n'),
    ('    exact lemma156_gamma_total_exponent k\n',
     '    exact Nat.mul_le_mul_right S (fejer156_gamma_base_exponent k)\n'),
    ('    exact lemma156_constant_total_exponent k\n',
     '    exact Nat.mul_le_mul_right S (fejer156_constant_base_exponent k)\n'),
    ('      (beta * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) *\n',
     '      (beta * gamma / 2) ^ fejerProductExponent k *\n'),
]
for a, b in SUBS:
    assert proof.count(a) == 1, a[:60]
    proof = proof.replace(a, b)

HEADER = '''import GowersSzemeredi.Proofs15FejerSelection
import GowersSzemeredi.Proofs15ProductToRestriction

/-! **Lemma 15.6 with the Fejér exponent** (Notes L.16).

Lemma 15.6 turns the product property into a large restriction on which
almost every 8-arrangement is respected. Its arrangement density
`(βγ/2)^(2^(2^(k+5)))` is the source of the printed `θ₁` of Section 16.
The proof applies Lemma 15.5 at `α = β^(7·4^(k+1))·γ^(21k·4^(k+1))`,
`η = 2^(−44)`, and dominates every exponent by `2^(3k+7)` times the Lemma 15.5
exponent (`lemma156_scale_ratio_bound`). With the Fejér Lemma 15.5
(`fejer_arrangement_restriction`) the same proof gives the single-exponential
density `(βγ/2)^(fejerProductExponent k)`, where
`fejerProductExponent k = 2^(3k+7)·2^(k+4)·(k+6)`
(`fejer_product_restriction`). This implies the printed Lemma 15.6
(`lemma_15_6_of_fejer_product`), since
`fejerProductExponent k ≤ 2^(5k+14) ≤ 2^(2^(k+5))`. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The arrangement exponent of Lemma 15.6 after the Fejér selection. -/
def fejerProductExponent (k : Nat) : Nat := 2 ^ (3 * k + 7) * fejerSelectionExponent k

/-- **Lemma 15.6 with the Fejér exponent**: the statement of Lemma 15.6 with
`fejerProductExponent k` in place of `2^(2^(k+5))`. -/
def FejerProductRestriction : Prop :=
  ∀ (k : Nat) (beta gamma : Real),
    1 ≤ k → 0 < beta → beta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1)))
          (phi : Point N (k + 1) → ZMod N),
        (B.card : Real) = beta * (N : Real) ^ (k + 1) →
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (beta * gamma / 2) ^ fejerProductExponent k *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi

'''

TAIL = '''
/-- The Fejér exponent of Lemma 15.6 is single-exponential: at most
`2^(5k+14)`, against the printed `2^(2^(k+5))`. -/
theorem fejerProductExponent_le (k : Nat) :
    fejerProductExponent k ≤ 2 ^ (5 * k + 14) := by
  unfold fejerProductExponent fejerSelectionExponent
  have hk : k + 6 ≤ 2 ^ (k + 3) := by
    have := Nat.lt_two_pow_self (n := k)
    have e : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
    rw [e]
    have := Nat.one_le_two_pow (n := k)
    omega
  calc 2 ^ (3 * k + 7) * (2 ^ (k + 4) * (k + 6))
      ≤ 2 ^ (3 * k + 7) * (2 ^ (k + 4) * 2 ^ (k + 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hk)
    _ = 2 ^ (5 * k + 14) := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- **The Fejér Lemma 15.6 implies the printed Lemma 15.6.** -/
theorem lemma_15_6_of_fejer_product (h : FejerProductRestriction) : lemma_15_6 := by
  intro k beta gamma hk hbeta hbeta_one hgamma hgamma_one
  obtain ⟨N0, hN0⟩ := h k beta gamma hk hbeta hbeta_one hgamma hgamma_one
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd B phi hBcard hproduct
  obtain ⟨B', hB'B, hlower, hdens⟩ := hN0 N hN hprime hodd B phi hBcard hproduct
  refine ⟨B', hB'B, le_trans ?_ hlower, hdens⟩
  have hexp : fejerProductExponent k ≤ 2 ^ (2 ^ (k + 5)) := by
    refine (fejerProductExponent_le k).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    have := Nat.lt_two_pow_self (n := k)
    have e : 2 ^ (k + 5) = 32 * 2 ^ k := by rw [pow_add]; ring
    rw [e]
    omega
  have hbase0 : 0 ≤ beta * gamma / 2 := by positivity
  have hbase1 : beta * gamma / 2 ≤ 1 := by
    have := mul_le_mul hbeta_one hgamma_one hgamma.le zero_le_one
    linarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hbase0 hbase1 hexp) (by positivity)

end LeanProofs.GowersSzemeredi
'''

EXTRA = (Path(__file__).parent / 'fejer156_extra.lean').read_text(encoding='utf-8')
TAIL = TAIL.replace('\nend LeanProofs.GowersSzemeredi\n', EXTRA + '\nend LeanProofs.GowersSzemeredi\n')
assert EXTRA in TAIL
out = HEADER + helpers + '\n\n' + proof.rstrip() + '\n' + TAIL
(GS / 'Proofs15FejerProduct.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()), 'lines')
