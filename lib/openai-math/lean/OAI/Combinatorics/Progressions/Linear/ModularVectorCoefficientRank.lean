import OAI.Combinatorics.Progressions.Estimates.ModularDesignatedCoefficientMarkov
import OAI.Combinatorics.Progressions.Estimates.ModularVectorCoefficientDecomposition

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

noncomputable def vectorDesignatedRankFailureProbability {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N n : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (c : B → A → ZMod N) : ℝ :=
  𝔼 u : Fin n → I → ZMod N,
    if polynomialLinearRow (polynomialIterDifference n
      (∑ b, w b • designatedVectorComponent S Q c b) u) = 0 then 1 else 0

theorem vectorDesignatedRankFailureProbability_nonneg {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N n : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (c : B → A → ZMod N) :
    0 ≤ vectorDesignatedRankFailureProbability N n S Q w c :=
  Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem vectorDesignatedRankFailureProbability_mean_le_of_unit {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a n : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (w : B → ZMod (p ^ a)) (b₀ : B) (hunit : IsUnit (w b₀))
    (hcard : ∀ j, (S b₀ j).card = n + 1)
    (hdisjoint : Pairwise (fun j k => Disjoint (S b₀ j) (S b₀ k))) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (vectorDesignatedRankFailureProbability (p ^ a) n S Q w) ≤
        (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  obtain ⟨unit, hunit⟩ := hunit
  have hconditional (c : B → A → ZMod (p ^ a)) :
      (𝔼 d : A → ZMod (p ^ a), vectorDesignatedRankFailureProbability (p ^ a) n S Q w
        (Function.update c b₀ d)) ≤
        (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
    unfold vectorDesignatedRankFailureProbability
    simp_rw [designatedVectorComponent_update_row]
    have h := designatedPolynomial_expected_rank_failure_le hp ha (S b₀) hcard hdisjoint
      ((∑ b ∈ Finset.univ.erase b₀, w b • designatedVectorComponent S Q c b) + w b₀ • Q b₀)
      (fun _ => unit)
    simpa only [hunit] using h
  rw [FiniteProbabilityWeights.uniform_mean,
    ← expect_uniform_coordinate_refresh b₀ (vectorDesignatedRankFailureProbability (p ^ a) n S Q w)]
  calc
    _ ≤ 𝔼 _c : B → A → ZMod (p ^ a),
        (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A :=
      Finset.expect_le_expect (fun c _ => hconditional c)
    _ = _ := Fintype.expect_const _

theorem vectorDesignatedRankFailureProbability_mean_le {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a n s : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (hns : n + 1 ≤ s)
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ b j, (S b j).card = n + 1)
    (hdisjoint : ∀ b, Pairwise (fun j k => Disjoint (S b j) (S b k)))
    (w : B → ZMod (p ^ a)) (hprimitive : ∃ b, IsUnit (w b)) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (vectorDesignatedRankFailureProbability (p ^ a) n S Q w) ≤
        ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  obtain ⟨b, hb⟩ := hprimitive
  have h := vectorDesignatedRankFailureProbability_mean_le_of_unit hp ha S Q w b hb
    (hcard b) (hdisjoint b)
  apply h.trans
  apply pow_le_pow_left₀ (by positivity)
  exact modularRank_tag_cost_le hns (by exact_mod_cast hp.one_lt.le)

end Erdos3

end

end OAI
