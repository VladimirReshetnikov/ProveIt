import OAI.Combinatorics.Progressions.Linear.FiniteKernelSumBound
import OAI.Combinatorics.Progressions.Linear.ProductANOVATensorChoices

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {J I : Type*} {X : I → Type*}

def finiteTaggedTupleEquiv : (J → Sigma X) ≃ Σ a : J → I, ∀ j, X (a j) where
  toFun z := ⟨fun j => (z j).1, fun j => (z j).2⟩
  invFun z j := ⟨z.1 j, z.2 j⟩
  left_inv z := by funext j; exact Sigma.eta (z j)
  right_inv z := by cases z; rfl

theorem finiteTaggedTuple_sum [Fintype I] [Fintype J] [DecidableEq J]
    [∀ i, Fintype (X i)] (F : (J → Sigma X) → ℝ) :
    (∑ z, F z) = ∑ a : J → I, ∑ v : ∀ j, X (a j), F (fun j => ⟨a j, v j⟩) := by
  classical
  calc
    (∑ z, F z) = ∑ av : Σ a : J → I, ∀ j, X (a j), F (fun j => ⟨av.1 j, av.2 j⟩) :=
      Fintype.sum_equiv finiteTaggedTupleEquiv _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem finiteProductIntegral_tagged (μ : ∀ i, FiniteProbabilityWeights (X i))
    (F : (J → Sigma X) → ℝ) :
    finiteProductIntegral (fun _ : J => coordinateUnionWeight μ) F =
      ∑ a : J → I, (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean
        (fun v => F (fun j => ⟨a j, v j⟩)) := by
  unfold finiteProductIntegral
  rw [finiteTaggedTuple_sum]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

noncomputable def orderedFamilyTensor (k : ℕ) (base : ∀ i, X i)
    (F : Finset I → (∀ i, X i) → ℝ) (z : Fin k → Sigma X) : ℝ := by
  classical
  exact if h : StrictMono (fun j => (z j).1) then
    F (Finset.univ.image (fun j => (z j).1))
      (productTuplePoint (fun j => (z j).1) h.injective (fun j => (z j).2) base)
    else 0

theorem orderedFamilyTensor_energy (μ : ∀ i, FiniteProbabilityWeights (X i))
    (k : ℕ) (base : ∀ i, X i) (F : Finset I → (∀ i, X i) → ℝ)
    (hF : ∀ S, ProductDependsOn S (F S)) :
    finiteProductIntegral (fun _ : Fin k => coordinateUnionWeight μ)
      (fun z => orderedFamilyTensor k base F z ^ 2) =
        ∑ S ∈ Finset.univ.powersetCard k, (FiniteProbabilityWeights.pi μ).mean (fun x => F S x ^ 2) := by
  classical
  unfold finiteProductIntegral
  rw [finiteTaggedTuple_sum]
  calc
    _ = ∑ a : Fin k → I, if StrictMono a then
        (FiniteProbabilityWeights.pi μ).mean (fun x => F (Finset.univ.image a) x ^ 2) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : StrictMono a
      · simp only [orderedFamilyTensor, ha, dite_true, ite_true]
        refine productMean_tuple μ a ha.injective
          (fun x => F (Finset.univ.image a) x ^ 2) ?_ base
        intro x y hxy
        exact congrArg (fun t : ℝ => t ^ 2) (hF (Finset.univ.image a) x y hxy)
      · simp only [orderedFamilyTensor, ha, dite_false, ite_false,
          zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
    _ = _ := finiteOrderedSubset_sum k (fun S => (FiniteProbabilityWeights.pi μ).mean (fun x => F S x ^ 2))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I B : Type*} [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_sum_embeddings_le (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (G : (B → Sigma X) → ℝ) (hG : ∀ z, 0 ≤ G z) :
    (∑ b : B ↪ I, (FiniteProbabilityWeights.pi μ).mean
      (fun x => G (fun j => ⟨b j, x (b j)⟩))) ≤
        finiteProductIntegral (fun _ : B => coordinateUnionWeight μ) G := by
  classical
  rw [finiteProductIntegral_tagged]
  apply Finset.sum_le_sum_of_injOn (fun b : B ↪ I => (b : B → I))
    Function.Embedding.coe_injective.injOn (Finset.subset_univ _) ?_ ?_
  · intro b _
    exact (productMean_pullback μ b b.injective base
      (fun v => G (fun j => ⟨b j, v j⟩))).le
  · intro a _ _
    exact FiniteProbabilityWeights.mean_nonneg _ (fun _ => hG _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

theorem productTensor_pattern_integral (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (r : Setoid (J × Fin k))
    [Fintype (Quotient r)] [DecidableEq (Quotient r)] [DecidableEq (Setoid (J × Fin k))]
    (A : J → (Fin k → Sigma X) → ℝ) :
    (∑ a : {a : (J × Fin k) → I // Setoid.ker a = r},
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, |A j (fun l => ⟨a.1 (j, l), x (a.1 (j, l))⟩)|)) ≤
      finiteProductIntegral (fun _ : Quotient r => coordinateUnionWeight μ)
        (fun z => ∏ j, |A j (fun l => z (Quotient.mk'' (j, l)))|) := by
  rw [finiteKernelFiber_sum r (fun a => (FiniteProbabilityWeights.pi μ).mean
    (fun x => ∏ j, |A j (fun l => ⟨a (j, l), x (a (j, l))⟩)|))]
  exact productMean_sum_embeddings_le μ base
    (fun z => ∏ j, |A j (fun l => z (Quotient.mk'' (j, l)))|)
    (fun z => Finset.prod_nonneg (fun j _ => abs_nonneg _))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

theorem productTensor_pattern_bound (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (x₀ : Sigma X) (r : Setoid (J × Fin k))
    [Fintype (Quotient r)] [DecidableEq (Quotient r)] [DecidableRel r]
    [DecidableEq (Setoid (J × Fin k))]
    (hrow : ∀ j l m, r (j, l) (j, m) → l = m)
    (hdeg : ∀ s, 2 ≤ (Finset.univ.filter (fun j => ∃ l, r (j, l) s)).card)
    (A : J → (Fin k → Sigma X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z,
      finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t (A j) z ≤ C j) :
    (∑ a : {a : (J × Fin k) → I // Setoid.ker a = r},
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        ∏ j, |A j (fun l => ⟨a.1 (j, l), x (a.1 (j, l))⟩)|)) ≤ ∏ j, C j := by
  apply (productTensor_pattern_integral μ base r A).trans
  apply finiteHypergraph_abstract_bound (coordinateUnionWeight μ) (coordinateUnionWeight_nonneg μ)
    x₀ k (fun j l => Quotient.mk'' (j, l)) ?_ ?_ A C hC hsection
  · intro j l m h
    exact hrow j l m (Quotient.exact h)
  · intro b
    induction b using Quotient.inductionOn with
    | h s => simpa only [Quotient.eq] using hdeg s

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

theorem productTensor_grouped_bound (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (x₀ : Sigma X) (T : Finset ((J × Fin k) → I))
    (hrow : ∀ a ∈ T, ∀ j, Function.Injective (fun l => a (j, l)))
    (hdeg : ∀ a ∈ T, ∀ s,
      2 ≤ (Finset.univ.filter (fun j => ∃ l, a (j, l) = a s)).card)
    (A : J → (Fin k → Sigma X) → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hsection : ∀ j t z,
      finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t (A j) z ≤ C j) :
    (∑ a ∈ T, (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, |A j (fun l => ⟨a (j, l), x (a (j, l))⟩)|)) ≤
        ((Fintype.card J * k) ^ (Fintype.card J * k) : ℕ) * ∏ j, C j := by
  classical
  let G : ((J × Fin k) → I) → ℝ := fun a =>
    (FiniteProbabilityWeights.pi μ).mean (fun x =>
      ∏ j, |A j (fun l => ⟨a (j, l), x (a (j, l))⟩)|)
  have hg : ∀ a, 0 ≤ G a := fun a =>
    FiniteProbabilityWeights.mean_nonneg _ (fun x => Finset.prod_nonneg (fun j _ => abs_nonneg _))
  have hp : ∀ r ∈ T.image Setoid.ker,
      (∑ a : {a : (J × Fin k) → I // Setoid.ker a = r}, G a.1) ≤ ∏ j, C j := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    let : Fintype (Quotient (Setoid.ker a)) := Fintype.ofFinite _
    exact productTensor_pattern_bound μ base x₀ (Setoid.ker a)
      (fun j l m h => hrow a ha j h) (hdeg a ha) A C hC hsection
  have h := finiteKernel_sum_bound T G hg (∏ j, C j)
    (Finset.prod_nonneg (fun j _ => hC j)) hp
  simpa only [Fintype.card_prod, Fintype.card_fin] using h

end Erdos3

end

end OAI
