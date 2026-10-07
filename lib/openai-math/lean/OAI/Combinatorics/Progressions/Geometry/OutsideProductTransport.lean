import OAI.Combinatorics.Progressions.Estimates.ScaledConditionedComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem conditioningCoreSupports_map_outside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (B : ℕ) :
    conditioningCoreSupports K B =
      (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card)).map
        (Finset.mapEmbedding (Function.Embedding.subtype (fun i => i ∉ K))).toEmbedding := by
  classical
  ext S
  constructor
  · intro hS
    have hs : S ⊆ Kᶜ ∧ S.card ≤ B - K.card := by
      simpa only [conditioningCoreSupports, Finset.mem_filter, Finset.mem_powerset] using hS
    let U := S.subtype (fun i => i ∉ K)
    have hu : U.map (Function.Embedding.subtype (fun i => i ∉ K)) = S :=
      Finset.subtype_map_of_mem (fun i hi => Finset.mem_compl.mp (hs.1 hi))
    have hc : U.card = S.card := by rw [← hu, Finset.card_map]
    apply Finset.mem_map.mpr
    refine ⟨U, (mem_lowDegreeCoordinateSets _ _ U).mpr (by rw [hc]; exact hs.2), ?_⟩
    exact hu
  · intro hS
    obtain ⟨U, hU, rfl⟩ := Finset.mem_map.mp hS
    change U.map (Function.Embedding.subtype (fun i => i ∉ K)) ∈ conditioningCoreSupports K B
    simp only [conditioningCoreSupports, Finset.mem_filter, Finset.mem_powerset, Finset.card_map]
    refine ⟨?_, (mem_lowDegreeCoordinateSets _ _ U).mp hU⟩
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_compl.mpr j.property

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem lowDegreeCoordinateSets_filter_outside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (b : ℕ) :
    (lowDegreeCoordinateSets ι b).filter (fun S => S ⊆ Kᶜ) = conditioningCoreSupports K (b + K.card) := by
  ext S
  have hb : b + K.card - K.card = b := by omega
  simp only [Finset.mem_filter, mem_lowDegreeCoordinateSets, conditioningCoreSupports,
    Finset.mem_powerset, hb]
  exact and_comm

theorem productANOVAEnergy_outside {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (K : Finset ι) (base : ∀ i, X i) (b : ℕ) (f : (∀ i : {i // i ∉ K}, X i.val) → ℝ) :
    productANOVAEnergy μ (lowDegreeCoordinateSets ι b) (fun x => f (fun i => x i.val)) =
      productANOVAEnergy (fun i : {i // i ∉ K} => μ i.val)
        (lowDegreeCoordinateSets {i // i ∉ K} b) f := by
  have hd : ProductDependsOn Kᶜ (fun x => f (fun i : {i // i ∉ K} => x i.val)) := by
    intro x y hxy
    exact congrArg f (funext (fun i => hxy i.val (Finset.mem_compl.mpr i.property)))
  rw [productANOVAEnergy_of_depends_filter μ Kᶜ _ hd, lowDegreeCoordinateSets_filter_outside,
    conditioningCoreSupports_map_outside]
  have hb : b + K.card - K.card = b := by omega
  rw [hb]
  exact productANOVAEnergy_embedding μ (Function.Embedding.subtype (fun i => i ∉ K)) base _ f

theorem productTruncatedPairing_outside_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
    (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i)) (K : Finset ι)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) (B : ℕ)
    (f : (∀ i : {i // i ∉ K}, X i.val) → ℝ) (g : (∀ i : {i // i ∉ K}, Y i.val) → ℝ) :
    productTruncatedPairing c (conditioningCoreSupports K B)
      (fun x => f (fun i => x i.val)) (fun y => g (fun i => y i.val)) =
      productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
        (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card)) f g := by
  rw [conditioningCoreSupports_map_outside]
  exact productTruncatedPairing_embedding c (Function.Embedding.subtype (fun i => i ∉ K)) baseX baseY _ f g

end Erdos3

end

end OAI
