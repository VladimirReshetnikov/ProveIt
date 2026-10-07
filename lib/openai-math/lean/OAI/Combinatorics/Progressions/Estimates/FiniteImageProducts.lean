import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteImageMass_pi {D : Type*} [Fintype D] [DecidableEq D]
    {X Z : D → Type*} [∀ d, Fintype (X d)] [∀ d, DecidableEq (Z d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → Z d) (z : ∀ d, Z d) :
    finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z =
      ∏ d, finiteImageMass (p d) (Y d) (z d) := by
  classical
  have h := FiniteProbabilityWeights.eventProbability_pi p (fun d x => Y d x = z d)
  have he : finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z =
      (FiniteProbabilityWeights.pi p).eventProbability (fun x => ∀ d, Y d (x d) = z d) := by
    unfold finiteImageMass FiniteProbabilityWeights.eventProbability
    congr 1
    funext x
    by_cases hx : ∀ d, Y d (x d) = z d
    · simp [hx]
    · have hf : (fun d => Y d (x d)) ≠ z := fun e => hx (fun d => congrFun e d)
      simp only [hf, hx, ite_false]
  have hr : (∏ d, (p d).eventProbability (fun x => Y d x = z d)) =
      ∏ d, finiteImageMass (p d) (Y d) (z d) := by
    apply Finset.prod_congr rfl
    intro d _
    unfold FiniteProbabilityWeights.eventProbability finiteImageMass
    congr 1
    funext x
    by_cases hx : Y d x = z d <;> simp only [hx, ite_true, ite_false]
  exact he.trans (h.trans hr)

theorem scaledImageMass_pi {D : Type*} [Fintype D] [DecidableEq D]
    {X Z : D → Type*} [∀ d, Fintype (X d)] [∀ d, DecidableEq (Z d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → Z d) (z : ∀ d, Z d) (scale : D → ℝ) :
    (∏ d, scale d) * finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z =
      ∏ d, scale d * finiteImageMass (p d) (Y d) (z d) := by
  rw [finiteImageMass_pi, Finset.prod_mul_distrib]

theorem scaledImageMass_pi_approximation {D : Type*} [Fintype D] [DecidableEq D]
    {X Z : D → Type*} [∀ d, Fintype (X d)] [∀ d, DecidableEq (Z d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → Z d) (z : ∀ d, Z d)
    (scale : D → ℝ) (approximation : D → ℂ) {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 ≤ ε)
    (hcap : ∀ d, ‖((scale d * finiteImageMass (p d) (Y d) (z d) : ℝ) : ℂ)‖ ≤ C)
    (hacap : ∀ d, ‖approximation d‖ ≤ C)
    (herror : ∀ d, ‖((scale d * finiteImageMass (p d) (Y d) (z d) : ℝ) : ℂ) - approximation d‖ ≤ ε) :
    ‖(((∏ d, scale d) * finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z : ℝ) : ℂ) -
      ∏ d, approximation d‖ ≤ Fintype.card D * ε * C ^ Fintype.card D := by
  rw [scaledImageMass_pi, Complex.ofReal_prod]
  simpa only [Finset.card_univ] using norm_finset_prod_sub_prod_le Finset.univ
    (fun d => ((scale d * finiteImageMass (p d) (Y d) (z d) : ℝ) : ℂ)) approximation hC hε
    (fun d _ => hcap d) (fun d _ => hacap d) (fun d _ => herror d)

end Erdos3

end

end OAI
