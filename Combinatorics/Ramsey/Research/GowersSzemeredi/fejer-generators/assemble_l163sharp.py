"""Proofs16BaseCaseRestrictionSharp: Lemma 16.3's restriction with the density its proof gives."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs16BaseCaseRestriction.lean').read_text(encoding='utf-8')
a = s.index('lemma section16_product_restriction {N : Nat}')
b = s.index('@[simp] lemma candidateGraph_card')
body = s[a:b]
h0 = body.index('  have hsize : lemma163Alpha gamma theta * N ≤ B\'.card := by')
h1 = body.index('      _ ≤ A.card := hAsize\n') + len('      _ ≤ A.card := hAsize\n')
NEW = '''  have hsize : lemma163AlphaSharp gamma theta * N ≤ B'.card := by
    rw [hB'card]
    refine le_trans ?_ hAsize
    unfold lemma163AlphaSharp
    have hthetaPow : theta ^ (1165 : Nat) ≤ beta ^ (1165 : Nat) :=
      pow_le_pow_left₀ htheta.le hbetaLower 1165
    have hg : gamma ^ (9312 : Nat) = (gamma ^ (8 : Nat)) ^ (1164 : Nat) := by
      rw [← pow_mul]
    have hb : beta ^ (1165 : Nat) = beta ^ (1164 : Nat) * beta := pow_succ beta 1164
    have h2 : (0 : Real) ≤ (2 : Real) ^ (-(1882 : Real)) := Real.rpow_nonneg (by norm_num) _
    calc (2 : Real) ^ (-(1882 : Real)) * gamma ^ (9312 : Nat) * theta ^ (1165 : Nat) * N
        ≤ (2 : Real) ^ (-(1882 : Real)) * gamma ^ (9312 : Nat) * beta ^ (1165 : Nat) * N := by
          gcongr
      _ = (2 : Real) ^ (-(1882 : Real)) * (gamma ^ (8 : Nat) * beta) ^ (1164 : Nat) * beta * N := by
          rw [hg, hb, mul_pow]; ring
'''
body = body[:h0] + NEW + body[h1:]
body = body.replace('lemma section16_product_restriction {N : Nat}',
                    'lemma section16_product_restriction_sharp {N : Nat}')
body = body.replace('IsBaseCandidate Gamma (lemma163Alpha gamma theta) C', 'IsBaseCandidate Gamma (lemma163AlphaSharp gamma theta) C')
assert 'lemma163Alpha gamma' not in body, [l for l in body.split('\n') if 'lemma163Alpha gamma' in l]

HEADER = '''import GowersSzemeredi.Proofs16BaseCaseRestriction

/-! **Lemma 16.3's restriction at the density its proof gives** (Notes L.16f).

`section16_product_restriction` extracts an order-eight Freiman piece of
density `lemma163Alpha γ θ = 2^(−2000)·(γθ)^10000`. The proof (Corollary 7.6
with energy `γ^8·β`, `β ≥ θ`) gives `2^(−1882)·(γ^8 β)^1164·β`, which is at
least `lemma163AlphaSharp γ θ = 2^(−1882)·γ^9312·θ^1165`. The printed
density rounds this down (`lemma163Alpha_le_sharp`).
* `section16_product_restriction_sharp`: the restriction at
  `lemma163AlphaSharp`; the printed lemma follows by monotonicity
  (`section16_product_restriction_of_sharp`).

In the dimension-two counts of the Fejér route θ is the piece budget, so
the sharp exponent `1165` in place of `10000` would lower the dimension-two
seed from about `2^46` to about `2^43` (Notes L.16f); no headline constant
changes. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

/-- The density of Lemma 16.3's restriction, as its proof gives it. -/
def lemma163AlphaSharp (gamma theta : Real) : Real :=
  (2 : Real) ^ (-(1882 : Real)) * gamma ^ (9312 : Nat) * theta ^ (1165 : Nat)

/-- The printed density is at most the sharp one. -/
lemma lemma163Alpha_le_sharp {gamma theta : Real} (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (ht : 0 ≤ theta) (ht1 : theta ≤ 1) : lemma163Alpha gamma theta ≤ lemma163AlphaSharp gamma theta := by
  unfold lemma163Alpha lemma163AlphaSharp
  have h2 : (2 : Real) ^ (-(2000 : Real)) ≤ (2 : Real) ^ (-(1882 : Real)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hgp : gamma ^ (10000 : Nat) ≤ gamma ^ (9312 : Nat) := pow_le_pow_of_le_one hg hg1 (by norm_num)
  have htp : theta ^ (10000 : Nat) ≤ theta ^ (1165 : Nat) := pow_le_pow_of_le_one ht ht1 (by norm_num)
  rw [mul_pow, ← mul_assoc]
  have h0 : (0 : Real) ≤ (2 : Real) ^ (-(2000 : Real)) := Real.rpow_nonneg (by norm_num) _
  calc (2 : Real) ^ (-(2000 : Real)) * gamma ^ (10000 : Nat) * theta ^ (10000 : Nat)
      ≤ (2 : Real) ^ (-(1882 : Real)) * gamma ^ (9312 : Nat) * theta ^ (1165 : Nat) := by
        gcongr

'''
TAIL = '''
/-- The printed restriction follows from the sharp one. -/
lemma section16_product_restriction_of_sharp {N : Nat} [NeZero N]
    (gamma theta : Real) (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hprime : N.Prime) (Gamma : Finset (Point N 1 × ZMod N))
    (hrelation : RelationProductProperty gamma Gamma)
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N)
    (hBlarge : theta * N ≤ B.card)
    (hgraph : GraphContained B phi Gamma) :
    ∃ C : BaseCandidate N, IsBaseCandidate Gamma (lemma163Alpha gamma theta) C := by
  obtain ⟨C, hC, hrest⟩ := section16_product_restriction_sharp gamma theta hgamma hgammaOne htheta
    hthetaOne hprime Gamma hrelation B phi hBlarge hgraph
  refine ⟨C, le_trans ?_ hC, hrest⟩
  exact mul_le_mul_of_nonneg_right
    (lemma163Alpha_le_sharp hgamma.le hgammaOne htheta.le hthetaOne) (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi.BaseCase
'''
out = HEADER + body + TAIL
(GS / 'Proofs16BaseCaseRestrictionSharp.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
