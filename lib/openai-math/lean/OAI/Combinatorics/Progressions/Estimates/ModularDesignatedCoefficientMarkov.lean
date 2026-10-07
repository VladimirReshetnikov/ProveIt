import OAI.Combinatorics.Progressions.Linear.ModularDesignatedCoefficientRank
import OAI.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

noncomputable def designatedRankFailureProbability {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (N n : ℕ) [NeZero N] (S : A → Finset I)
    (Q : MvPolynomial I (ZMod N)) (unit : A → (ZMod N)ˣ) (c : A → ZMod N) : ℝ :=
  𝔼 u : Fin n → I → ZMod N,
    if polynomialLinearRow (polynomialIterDifference n
      (Q + ∑ b, ((unit b : ZMod N) * c b) • ∏ i ∈ S b, X i) u) = 0 then 1 else 0

theorem designatedRankFailureProbability_nonneg {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (N n : ℕ) [NeZero N] (S : A → Finset I)
    (Q : MvPolynomial I (ZMod N)) (unit : A → (ZMod N)ˣ) (c : A → ZMod N) :
    0 ≤ designatedRankFailureProbability N n S Q unit c :=
  Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem designatedRankFailureProbability_mean_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    {p a n s : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (hns : n + 1 ≤ s) (S : A → Finset I) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod (p ^ a))) (unit : A → (ZMod (p ^ a))ˣ) :
    (FiniteProbabilityWeights.uniform (A → ZMod (p ^ a))).mean
      (designatedRankFailureProbability (p ^ a) n S Q unit) ≤
        ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  rw [FiniteProbabilityWeights.uniform_mean]
  have h := designatedPolynomial_expected_rank_failure_le hp ha S hcard hdisjoint Q unit
  apply h.trans
  apply pow_le_pow_left₀ (by positivity)
  exact modularRank_tag_cost_le hns (by exact_mod_cast hp.one_lt.le)

theorem designatedRankFailureProbability_markov {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    {p a n s : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (hns : n + 1 ≤ s) (S : A → Finset I) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod (p ^ a))) (unit : A → (ZMod (p ^ a))ˣ) (C : ℝ) :
    (FiniteProbabilityWeights.uniform (A → ZMod (p ^ a))).eventProbability
      (fun c => ((p : ℝ) ^ a) ^ (-C) < designatedRankFailureProbability (p ^ a) n S Q unit c) ≤
        ((p : ℝ) ^ a) ^ C *
          ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  have hq : 0 < (p : ℝ) ^ a := pow_pos (by exact_mod_cast hp.pos) _
  have h := finiteProbability_rank_markov
    (FiniteProbabilityWeights.uniform (A → ZMod (p ^ a)))
    (designatedRankFailureProbability (p ^ a) n S Q unit)
    (designatedRankFailureProbability_nonneg (p ^ a) n S Q unit) (C := C) hq
  exact h.trans (mul_le_mul_of_nonneg_left
    (designatedRankFailureProbability_mean_le hp ha hns S hcard hdisjoint Q unit)
    (Real.rpow_nonneg hq.le _))

end Erdos3

end

end OAI
