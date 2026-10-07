/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.DisjointPowersetSum
import OAI.Combinatorics.Progressions.Estimates.FiniteHypergraphAbstract
import OAI.Combinatorics.Progressions.Estimates.IndependentProductMeans
import OAI.Combinatorics.Progressions.Estimates.PinnedSectionMeans
import OAI.Combinatorics.Progressions.Estimates.ProductMarginalAtomError
import OAI.Combinatorics.Progressions.Estimates.SubsetAlternatingInversion

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem alternating_powerset_sum_zero {I : Type*} [DecidableEq I]
    (S : Finset I) {i : I} (hi : i ∈ S) (g : Finset I → ℝ)
    (hpair : ∀ U ⊆ S.erase i, g (insert i U) = g U) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * g U) = 0 := by
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i S), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro U hU
  have hu := Finset.mem_powerset.mp hU
  have hni : i ∉ U := fun h => Finset.notMem_erase i S (hu h)
  rw [Finset.card_insert_of_notMem hni, pow_succ, hpair U hu]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVA (S : Finset I) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x

theorem productANOVA_inclusion_exclusion (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productANOVA μ S f x = ∑ T ∈ S.powerset,
      (-1 : ℝ) ^ (S.card - T.card) * productConditionalMean μ T f x := by
  unfold productANOVA
  apply Finset.sum_bij' (fun U _ => S \ U) (fun T _ => S \ T)
  · intro U _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro T _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro U hU
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hU)
  · intro T hT
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT)
  · intro U hU
    have hu := Finset.mem_powerset.mp hU
    have hc : S.card - (S \ U).card = U.card := by
      rw [Finset.card_sdiff_of_subset hu]
      exact Nat.sub_sub_self (Finset.card_le_card hu)
    rw [hc]

theorem productANOVA_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productANOVA μ S f) := by
  intro x y hxy
  unfold productANOVA
  apply Finset.sum_congr rfl
  intro U _
  congr 1
  exact productConditionalMean_depends μ (S \ U) f x y
    (fun i hi => hxy i (Finset.sdiff_subset hi))

theorem productConditionalMean_ANOVA (S T : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ T (productANOVA μ S f) x =
      if S ⊆ T then productANOVA μ S f x else 0 := by
  classical
  change productConditionalMean μ T (fun y => ∑ U ∈ S.powerset,
    (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f y) x =
      if S ⊆ T then (∑ U ∈ S.powerset,
        (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x) else 0
  simp only [productConditionalMean_sum, productConditionalMean_smul, productConditionalMean_comp]
  by_cases hST : S ⊆ T
  · rw [ite_eq_left hST]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.inter_eq_right.mpr (Finset.sdiff_subset.trans hST)]
  · rw [ite_eq_right hST]
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hST
    apply alternating_powerset_sum_zero S hi
    intro U _
    have he : T ∩ (S \ insert i U) = T ∩ (S \ U) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [hni]
      · simp [hj]
    rw [he]

theorem productANOVA_selfadjoint (S : Finset I) (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productANOVA μ S g x) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x * g x) := by
  let p := FiniteProbabilityWeights.pi μ
  simp only [productANOVA, Finset.mul_sum, Finset.sum_mul, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro U _
  calc
    _ = (-1 : ℝ) ^ U.card * p.mean (fun x => f x * productConditionalMean μ (S \ U) g x) := by
      rw [← p.mean_const_mul]
      congr 1
      funext x
      ring
    _ = (-1 : ℝ) ^ U.card * p.mean (fun x => productConditionalMean μ (S \ U) f x * g x) := by
      rw [productConditionalMean_selfadjoint]
    _ = _ := by
      rw [← p.mean_const_mul]
      congr 1
      funext x
      ring

theorem productANOVA_pairing_self (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x ^ 2) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productANOVA μ S f x) := by
  let p := FiniteProbabilityWeights.pi μ
  calc
    _ = p.mean (fun x => productANOVA μ S f x * productANOVA μ S f x) := by
      simp only [pow_two]
      rfl
    _ = ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
        p.mean (fun x => f x * productConditionalMean μ (S \ U) (productANOVA μ S f) x) := by
      change p.mean (fun x => (∑ U ∈ S.powerset,
        (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x) * productANOVA μ S f x) = _
      simp only [Finset.sum_mul, FiniteProbabilityWeights.mean_sum]
      apply Finset.sum_congr rfl
      intro U _
      calc
        _ = (-1 : ℝ) ^ U.card * p.mean (fun x =>
            productConditionalMean μ (S \ U) f x * productANOVA μ S f x) := by
          rw [← p.mean_const_mul]
          congr 1
          funext x
          ring
        _ = _ := by rw [← productConditionalMean_selfadjoint]
    _ = _ := by
      rw [Finset.sum_eq_single ∅]
      · simp only [Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
          productConditionalMean_ANOVA, Finset.Subset.refl, ite_true]
        rfl
      · intro U hU hUne
        have hUS := Finset.mem_powerset.mp hU
        have hn : ¬ S ⊆ S \ U := by
          obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hUne
          intro h
          exact (Finset.mem_sdiff.mp (h (hUS hi))).2 hi
        simp only [productConditionalMean_ANOVA, hn, ite_false, mul_zero, p.mean_const]
      · simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productANOVA_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : ι → Type*} [∀ i, Fintype (Y i)] (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, Y i) :
    productANOVA ν S (productANOVA ν S f) x = productANOVA ν S f x := by
  rw [productANOVA, Finset.sum_eq_single ∅]
  · simp only [Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
      productConditionalMean_ANOVA, Finset.Subset.refl, ite_true]
  · intro U hU hne
    have hUS := Finset.mem_powerset.mp hU
    have hn : ¬ S ⊆ S \ U := by
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      intro h
      exact (Finset.mem_sdiff.mp (h (hUS hi))).2 hi
    simp only [productConditionalMean_ANOVA, hn, ite_false, mul_zero]
  · simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_mul_blocks (I J A B : Finset ι) (hIJ : Disjoint I J)
    (hAI : A ⊆ I) (hBJ : B ⊆ J) (f g : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn I f) (hg : ProductDependsOn J g) (x : ∀ i, X i) :
    productANOVA μ (A ∪ B) (fun y => f y * g y) x = productANOVA μ A f x * productANOVA μ B g x := by
  have hAB := hIJ.mono hAI hBJ
  simp only [productANOVA_inclusion_exclusion]
  rw [disjoint_powerset_sum A B hAB]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hUA := Finset.mem_powerset.mp hU
  have hVB := Finset.mem_powerset.mp hV
  have hUV := hAB.mono hUA hVB
  rw [productConditionalMean_mul_disjoint μ I J (U ∪ V) hIJ f g hf hg x,
    productConditionalMean_union_irrelevant μ I U V (hIJ.mono_right (hVB.trans hBJ)) f hf x]
  have he := productConditionalMean_union_irrelevant μ J V U
    (hIJ.symm.mono_right (hUA.trans hAI)) g hg x
  rw [Finset.union_comm] at he
  rw [he]
  have hc : (A ∪ B).card - (U ∪ V).card = (A.card - U.card) + (B.card - V.card) := by
    rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hUV]
    have := Finset.card_le_card hUA
    have := Finset.card_le_card hVB
    omega
  rw [hc, pow_add]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_orthogonal_of_not_subset (S T : Finset I) (hTS : ¬ T ⊆ S)
    (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x * productANOVA μ T g x) = 0 := by
  have h := productConditionalMean_selfadjoint μ S (productANOVA μ S f) (productANOVA μ T g)
  simpa [productConditionalMean_ANOVA, hTS, FiniteProbabilityWeights.mean_const] using h.symm

theorem productANOVA_orthogonal (S T : Finset I) (hST : S ≠ T)
    (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x * productANOVA μ T g x) = 0 := by
  by_cases hTS : T ⊆ S
  · have hn : ¬ S ⊆ T := fun h => hST (Finset.Subset.antisymm h hTS)
    simpa only [mul_comm] using productANOVA_orthogonal_of_not_subset μ T S hn g f
  · exact productANOVA_orthogonal_of_not_subset μ S T hTS f g

noncomputable def productANOVATruncation (D : Finset (Finset I))
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ := ∑ S ∈ D, productANOVA μ S f x

noncomputable def productANOVAEnergy (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) : ℝ :=
  ∑ S ∈ D, (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x ^ 2)

theorem productANOVAEnergy_nonneg (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    0 ≤ productANOVAEnergy μ D f :=
  Finset.sum_nonneg (fun _ _ => (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _))

theorem productANOVAEnergy_pairing (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f =
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productANOVATruncation μ D f x) := by
  simp only [productANOVAEnergy, productANOVATruncation, Finset.mul_sum,
    FiniteProbabilityWeights.mean_sum, productANOVA_pairing_self]

theorem productANOVAEnergy_square (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVATruncation μ D f x ^ 2) =
      productANOVAEnergy μ D f := by
  simp only [productANOVATruncation, productANOVAEnergy, pow_two, Finset.sum_mul,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_eq_single S]
  · intro T _ hTS
    exact productANOVA_orthogonal μ T S hTS f f
  · exact fun h => False.elim (h hS)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ProductDependsOn.prod {I J : Type*} {X : I → Type*}
    (S : Finset I) (D : Finset J) (f : J → (∀ i, X i) → ℝ)
    (hf : ∀ j ∈ D, ProductDependsOn S (f j)) :
    ProductDependsOn S (fun x => ∏ j ∈ D, f j x) := by
  intro x y hxy
  exact Finset.prod_congr rfl (fun j hj => hf j hj x y hxy)

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_mul_zero_of_conditionalMean_zero (S : Finset I)
    (f g : (∀ i, X i) → ℝ) (hf : ProductDependsOn S f)
    (hg : ∀ x, productConditionalMean μ S g x = 0) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * g x) = 0 := by
  have h := productConditionalMean_selfadjoint μ S f g
  simpa only [hg, productConditionalMean_of_depends μ S hf, mul_zero,
    FiniteProbabilityWeights.mean_const] using h.symm

theorem productANOVA_unique_coordinate_zero {J : Type*} (D : Finset J)
    (S : J → Finset I) (f : J → (∀ i, X i) → ℝ) {j₀ : J} (hj₀ : j₀ ∈ D)
    {i : I} (hi : i ∈ S j₀) (hother : ∀ j ∈ D, j ≠ j₀ → i ∉ S j) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j ∈ D, productANOVA μ (S j) (f j) x) = 0 := by
  classical
  let T : Finset I := Finset.univ.erase i
  let g := fun x => ∏ j ∈ D.erase j₀, productANOVA μ (S j) (f j) x
  have hg : ProductDependsOn T g := by
    apply ProductDependsOn.prod
    intro j hj
    apply (productANOVA_depends μ (S j) (f j)).mono
    intro a ha
    apply Finset.mem_erase.mpr
    constructor
    · intro hai
      subst a
      exact hother j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1 ha
    · exact Finset.mem_univ _
  have hnot : ¬ S j₀ ⊆ T := by
    intro hST
    exact Finset.notMem_erase i Finset.univ (hST hi)
  have hcenter (x : ∀ i, X i) : productConditionalMean μ T (productANOVA μ (S j₀) (f j₀)) x = 0 := by
    rw [productConditionalMean_ANOVA, ite_eq_right hnot]
  calc
    (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j ∈ D, productANOVA μ (S j) (f j) x) =
        (FiniteProbabilityWeights.pi μ).mean (fun x => g x * productANOVA μ (S j₀) (f j₀) x) := by
      congr 1
      funext x
      exact (Finset.prod_erase_mul D (fun j => productANOVA μ (S j) (f j) x) hj₀).symm
    _ = 0 := productMean_mul_zero_of_conditionalMean_zero μ T g _ hg hcenter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_abs_le (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) {L : ℝ}
    (hraw : ∀ T ⊆ S, |productConditionalMean μ T f x| ≤ L) :
    |productANOVA μ S f x| ≤ (2 : ℝ) ^ S.card * L := by
  unfold productANOVA
  calc
    _ ≤ ∑ U ∈ S.powerset, |(-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ S.powerset, L := by
      apply Finset.sum_le_sum
      intro U _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        hraw (S \ U) Finset.sdiff_subset
    _ = _ := by simp

theorem productANOVA_weighted_cap (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M η : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (S : Finset I)
    (hclose : ∀ T ⊆ S, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ T r x - 1| ≤ η)
    (x : ∀ i, X i) (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    |productANOVA μ S (fun y => r y * f y) x| ≤ (2 : ℝ) ^ S.card * (M * (1 + η)) := by
  apply productANOVA_abs_le μ S _ x
  intro T hT
  have hc := productConditionalMean_weighted_cap μ r f hr hf T x
  rw [abs_of_nonneg hc.1]
  have he := (abs_le.mp (hclose T hT x hx)).2
  exact hc.2.trans (mul_le_mul_of_nonneg_left (by linarith) hM)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_sectionAverage (T A U : Finset I) (hAT : A ⊆ T)
    (hTU : Disjoint T U) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ U (productSectionAverage μ T A z f) x =
      ∑ B ∈ U.powerset, (-1 : ℝ) ^ (U.card - B.card) *
        productConditionalMean μ (A ∪ B) f (productCoordinateMix T z x) := by
  rw [productANOVA_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro B hB
  rw [productConditionalMean_sectionAverage μ T A B hAT]
  have hBT : Disjoint B T := hTU.symm.mono_left (Finset.mem_powerset.mp hB)
  rw [Finset.sdiff_eq_self_of_disjoint hBT]

theorem productANOVA_disjoint_section (T U : Finset I) (hTU : Disjoint T U)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ (T ∪ U) f (productCoordinateMix T z x) =
      ∑ A ∈ T.powerset, (-1 : ℝ) ^ (T.card - A.card) *
        productANOVA μ U (productSectionAverage μ T A z f) x := by
  rw [productANOVA_inclusion_exclusion, disjoint_powerset_sum T U hTU]
  apply Finset.sum_congr rfl
  intro A hA
  have hAT := Finset.mem_powerset.mp hA
  rw [productANOVA_sectionAverage μ T A U hAT hTU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hBU := Finset.mem_powerset.mp hB
  have hAB : Disjoint A B := hTU.mono hAT hBU
  have he : (T ∪ U).card - (A ∪ B).card = (T.card - A.card) + (U.card - B.card) := by
    rw [Finset.card_union_of_disjoint hTU, Finset.card_union_of_disjoint hAB]
    have ha := Finset.card_le_card hAT
    have hb := Finset.card_le_card hBU
    omega
  rw [he, pow_add, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productANOVAEnergy_le_mean_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (D : Finset (Finset ι)) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f ≤ (FiniteProbabilityWeights.pi μ).mean (fun x => f x ^ 2) := by
  have hcs := (FiniteProbabilityWeights.pi μ).mean_mul_sq_le f (productANOVATruncation μ D f)
  rw [productANOVAEnergy_square, ← productANOVAEnergy_pairing] at hcs
  by_cases hz : productANOVAEnergy μ D f = 0
  · rw [hz]
    exact FiniteProbabilityWeights.mean_nonneg _ (fun x => sq_nonneg (f x))
  · have hp : 0 < productANOVAEnergy μ D f :=
      lt_of_le_of_ne (productANOVAEnergy_nonneg μ D f) (Ne.symm hz)
    rw [pow_two] at hcs
    exact le_of_mul_le_mul_right hcs hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_reconstruct (S : Finset ι) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    (∑ T ∈ S.powerset, productANOVA μ T f x) = productConditionalMean μ S f x :=
  subsetAlternatingTransform_sum S (fun T => productConditionalMean μ T f x)

theorem productANOVATruncation_of_depends (S : Finset ι) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn S f) : productANOVATruncation μ S.powerset f = f := by
  funext x
  exact (productANOVA_reconstruct μ S f x).trans (productConditionalMean_of_depends μ S hf x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_conditional_commute (S T : Finset ι) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (productConditionalMean μ T f) x =
      productConditionalMean μ T (productANOVA μ S f) x := by
  change (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
      productConditionalMean μ (S \ U) (productConditionalMean μ T f) x) =
    productConditionalMean μ T (fun y => ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
      productConditionalMean μ (S \ U) f y) x
  simp only [productConditionalMean_sum, productConditionalMean_smul,
    productConditionalMean_comp, Finset.inter_comm]

theorem productANOVA_of_depends_not_subset (T : Finset ι) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn T f) (S : Finset ι) (hS : ¬S ⊆ T) (x : ∀ i, X i) :
    productANOVA μ S f x = 0 := by
  have he : productConditionalMean μ T f = f := funext (productConditionalMean_of_depends μ T hf)
  calc
    _ = productANOVA μ S (productConditionalMean μ T f) x := by rw [he]
    _ = productConditionalMean μ T (productANOVA μ S f) x := productANOVA_conditional_commute μ S T f x
    _ = 0 := by rw [productConditionalMean_ANOVA, ite_eq_right hS]

theorem productANOVAEnergy_of_depends_filter (T : Finset ι) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn T f) (D : Finset (Finset ι)) :
    productANOVAEnergy μ D f = productANOVAEnergy μ (D.filter (fun S => S ⊆ T)) f := by
  classical
  unfold productANOVAEnergy
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ⊆ T
  · rw [ite_eq_left hS]
  · simp only [ite_eq_right hS, productANOVA_of_depends_not_subset μ T f hf S hS,
      zero_pow (by decide : 2 ≠ 0), FiniteProbabilityWeights.mean_const]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_energy_le_lp (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1) :
    productANOVAEnergy μ D f ≤
      finiteWeightedLp (FiniteProbabilityWeights.pi μ).weight p f *
        finiteWeightedLp (FiniteProbabilityWeights.pi μ).weight q (productANOVATruncation μ D f) := by
  rw [productANOVAEnergy_pairing]
  exact (le_abs_self _).trans (finiteWeightedHolder_pair
    (FiniteProbabilityWeights.pi μ).weight (FiniteProbabilityWeights.pi μ).nonneg
    p q hp hq hpq f (productANOVATruncation μ D f))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVAEnergy_mono {D E : Finset (Finset I)} (hDE : D ⊆ E)
    (f : (∀ i, X i) → ℝ) : productANOVAEnergy μ D f ≤ productANOVAEnergy μ E f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hDE
  intro U _ _
  exact (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _)

theorem productANOVAEnergy_le_level (D : Finset (Finset I)) (d : ℕ)
    (hD : ∀ U ∈ D, U.card = d) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f ≤ productANOVAEnergy μ (Finset.univ.powersetCard d) f := by
  apply productANOVAEnergy_mono μ _ f
  intro U hU
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hD U hU⟩

end Erdos3

end

end OAI
