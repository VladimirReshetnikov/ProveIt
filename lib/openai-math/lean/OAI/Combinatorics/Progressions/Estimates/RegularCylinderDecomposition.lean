/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.ObservedDensityTesting

namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

noncomputable def cut (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) : ℝ := by
  classical
  exact if c.Contains (F z) then w z else 0

noncomputable def erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) : ℝ := by
  classical
  exact if c.Contains (F z) then 0 else w z

theorem cut_add_erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) :
    c.cut F w z + c.erase F w z = w z := by
  unfold cut erase
  split_ifs <;> simp

theorem cut_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.cut F w z := by
  unfold cut
  split_ifs <;> simp [hw]

theorem erase_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.erase F w z := by
  unfold erase
  split_ifs <;> simp [hw]

theorem cut_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.cut F w z ≤ w z := by
  unfold cut
  split_ifs <;> simp [hw]

theorem erase_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.erase F w z ≤ w z := by
  unfold erase
  split_ifs <;> simp [hw]

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

instance containsDecidable (c : ProductCylinder X) (x : ∀ i, X i) : Decidable (c.Contains x) := by
  unfold Contains
  infer_instance

theorem density_cut (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.cut F w) x =
      if c.Contains x then observedProductDensity μ p F w x else 0 := by
  classical
  by_cases hx : c.Contains x
  · rw [ite_eq_left hx]
    change p.fiberMean F x (c.cut F w) / _ = p.fiberMean F x w / _
    congr 1
    unfold FiniteProbabilityWeights.fiberMean
    congr 1
    funext z
    by_cases hz : F z = x
    · simp [cut, hz, hx]
    · simp [hz]
  · rw [ite_eq_right hx]
    have he : p.fiberMean F x (c.cut F w) = 0 := by
      calc
        _ = p.mean (fun _ => 0) := by
          unfold FiniteProbabilityWeights.fiberMean
          congr 1
          funext z
          by_cases hz : F z = x
          · simp [cut, hz, hx]
          · simp [hz]
        _ = 0 := p.mean_const 0
    change p.fiberMean F x (c.cut F w) / _ = 0
    rw [he, zero_div]

theorem density_erase (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.erase F w) x =
      if c.Contains x then 0 else observedProductDensity μ p F w x := by
  classical
  have he : (fun z => c.cut F w z + c.erase F w z) = w := funext (c.cut_add_erase F w)
  have hs := observedProductDensity_add μ p F (c.cut F w) (c.erase F w) x
  rw [he, c.density_cut] at hs
  by_cases hx : c.Contains x
  · rw [ite_eq_left hx] at hs ⊢
    linarith
  · rw [ite_eq_right hx] at hs ⊢
    linarith

theorem mass_erase_self (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.mass μ base (observedProductDensity μ p F (c.erase F w)) = 0 := by
  have hc (y : ∀ i, X i) : c.Contains (productCoordinateMix c.1 (c.assignment base) y) := by
    intro i
    simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property
  change (FiniteProbabilityWeights.pi μ).mean
    (fun y => observedProductDensity μ p F (c.erase F w) (productCoordinateMix c.1 (c.assignment base) y)) = 0
  have he : (fun y => observedProductDensity μ p F (c.erase F w)
      (productCoordinateMix c.1 (c.assignment base) y)) = (fun _ => 0) := by
    funext y
    rw [c.density_erase, ite_eq_left (hc y)]
  rw [he, FiniteProbabilityWeights.mean_const]

omit [∀ i, DecidableEq (X i)] in
theorem mass_erase_le (c d : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) :
    d.mass μ base (observedProductDensity μ p F (c.erase F w)) ≤
      d.mass μ base (observedProductDensity μ p F w) :=
  mass_mono μ base (observedProductDensity_mono μ p F (c.erase_le F w hw)) d

end Erdos3.ProductCylinder

end

section

namespace Erdos3

inductive CylinderRemovalChain {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (K τ : ℝ) (j r : ℕ) :
    (Ω → ℝ) → (Ω → ℝ) → List (ProductCylinder X) → Prop where
  | nil (w : Ω → ℝ) : CylinderRemovalChain μ base p F K τ j r w w []
  | cons {w v : Ω → ℝ} {cs : List (ProductCylinder X)} (c : ProductCylinder X)
      (hsize : c.1.card ≤ j)
      (hmass : τ < c.mass μ base (observedProductDensity μ p F w))
      (hbounded : ProductBoundedMarginals μ
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F w) c) K r)
      (rest : CylinderRemovalChain μ base p F K τ j r (c.erase F w) v cs) :
      CylinderRemovalChain μ base p F K τ j r w v (c :: cs)

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)

theorem mass_cut_self : c.mass μ base (observedProductDensity μ p F (c.cut F w)) =
    c.mass μ base (observedProductDensity μ p F w) := by
  unfold mass productConditionalMean
  congr 1
  funext y
  rw [c.density_cut]
  apply ite_eq_left
  intro i
  simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property

theorem section_cut (x : ∀ i, X i) :
    productSectionAverage μ c.1 c.1 (c.assignment base) (observedProductDensity μ p F (c.cut F w)) x =
      productSectionAverage μ c.1 c.1 (c.assignment base) (observedProductDensity μ p F w) x := by
  unfold productSectionAverage
  congr 1
  funext y
  rw [c.density_cut]
  apply ite_eq_left
  intro i
  simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property

theorem normalizedSection_cut :
    normalizedSection μ base (observedProductDensity μ p F (c.cut F w)) c =
      normalizedSection μ base (observedProductDensity μ p F w) c := by
  funext x
  unfold normalizedSection
  rw [c.mass_cut_self μ base p F w, c.section_cut μ base p F w x]

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] in
 theorem normalized_cut_bounds (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1)
    {m : ℝ} (hm : 0 < m) (z : Ω) : 0 ≤ c.cut F w z / m ∧ c.cut F w z / m ≤ m⁻¹ := by
  constructor
  · exact div_nonneg (c.cut_nonneg F w hw0 z) hm.le
  · simpa only [one_div] using div_le_div_of_nonneg_right ((c.cut_le F w hw0 z).trans (hw1 z)) hm.le

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

noncomputable def positiveCandidates (b : ℕ) (w : Ω → ℝ) : Finset (ProductCylinder X) := by
  classical
  exact (bounded (X := X) b).filter (fun c => 0 < c.mass μ base (observedProductDensity μ p F w))

theorem mem_positiveCandidates (b : ℕ) (w : Ω → ℝ) (c : ProductCylinder X) :
    c ∈ positiveCandidates μ base p F b w ↔
      c.1.card ≤ b ∧ 0 < c.mass μ base (observedProductDensity μ p F w) := by
  classical
  simp only [positiveCandidates, Finset.mem_filter, mem_bounded]

theorem positiveCandidates_card_le (b : ℕ) (w : Ω → ℝ) :
    (positiveCandidates μ base p F b w).card ≤ (bounded (X := X) b).card := by
  classical
  exact Finset.card_filter_le _ _

theorem positiveCandidates_erase_card_lt [∀ i, DecidableEq (X i)] (b : ℕ) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (c : ProductCylinder X) (hc : c.1.card ≤ b)
    (hm : 0 < c.mass μ base (observedProductDensity μ p F w)) :
    (positiveCandidates μ base p F b (c.erase F w)).card <
      (positiveCandidates μ base p F b w).card := by
  classical
  have hsub : positiveCandidates μ base p F b (c.erase F w) ⊆
      (positiveCandidates μ base p F b w).erase c := by
    intro d hd
    obtain ⟨hdsize, hdmass⟩ := (mem_positiveCandidates μ base p F b (c.erase F w) d).mp hd
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      subst d
      rw [c.mass_erase_self] at hdmass
      exact (lt_irrefl 0) hdmass
    · exact (mem_positiveCandidates μ base p F b w d).mpr
        ⟨hdsize, hdmass.trans_le (c.mass_erase_le d μ base p F w hw)⟩
  have hcpos := (mem_positiveCandidates μ base p F b w c).mpr ⟨hc, hm⟩
  exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hcpos)

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} {X : ι → Type*}

noncomputable def removedCylinderWeights (F : Ω → ∀ i, X i) :
    (Ω → ℝ) → List (ProductCylinder X) → List (Ω → ℝ)
  | _, [] => []
  | w, c :: cs => c.cut F w :: removedCylinderWeights F (c.erase F w) cs

theorem removedCylinderWeights_length (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (cs : List (ProductCylinder X)) : (removedCylinderWeights F w cs).length = cs.length := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih => simp only [removedCylinderWeights, List.length_cons, ih]

theorem removedCylinderWeights_zero (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (cs : List (ProductCylinder X)) {f : Ω → ℝ} (hf : f ∈ removedCylinderWeights F w cs)
    (z : Ω) (hz : w z = 0) : f z = 0 := by
  classical
  induction cs generalizing w with
  | nil => simp only [removedCylinderWeights, List.not_mem_nil] at hf
  | cons c cs ih =>
    change f ∈ c.cut F w :: removedCylinderWeights F (c.erase F w) cs at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · unfold ProductCylinder.cut
      split_ifs <;> simp [hz]
    · apply ih (c.erase F w) hf
      unfold ProductCylinder.erase
      split_ifs <;> simp [hz]

theorem removedCylinderWeights_pairwise (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (cs : List (ProductCylinder X)) :
    (removedCylinderWeights F w cs).Pairwise (fun f g => ∀ z, f z = 0 ∨ g z = 0) := by
  classical
  induction cs generalizing w with
  | nil => exact List.Pairwise.nil
  | cons c cs ih =>
    apply List.pairwise_cons.mpr
    constructor
    · intro f hf z
      by_cases hc : c.Contains (F z)
      · right
        apply removedCylinderWeights_zero F (c.erase F w) cs hf z
        simp [ProductCylinder.erase, hc]
      · left
        simp [ProductCylinder.cut, hc]
    · exact ih (c.erase F w)

end Erdos3

end

section

namespace Erdos3

open ProductCylinder

theorem exists_finite_cylinder_removal {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (K τ η : ℝ) (j r : ℕ) (hK : 1 ≤ K) (hτ : 0 ≤ τ) (hη : η ≤ 1)
    (hcut : 2 ≤ τ * K ^ (j + 1))
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r))
    (w : Ω → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
      CylinderRemovalChain μ base p F K τ j r w v cs ∧
      cs.length ≤ (ProductCylinder.bounded (X := X) (j + r)).card ∧ p.mean v ≤ τ ∧
      (∀ z, 0 ≤ v z ∧ v z ≤ 1) := by
  have aux : ∀ n : ℕ, ∀ w : Ω → ℝ, (∀ z, 0 ≤ w z) → (∀ z, w z ≤ 1) →
      (positiveCandidates μ base p F (j + r) w).card ≤ n →
      ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
        CylinderRemovalChain μ base p F K τ j r w v cs ∧ cs.length ≤ n ∧ p.mean v ≤ τ ∧
        (∀ z, 0 ≤ v z ∧ v z ≤ 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw0 hw1 hn
      by_cases hs : p.mean w ≤ τ
      · exact ⟨w, [], .nil w, by simp, hs, fun z => ⟨hw0 z, hw1 z⟩⟩
      · have hm : τ < (FiniteProbabilityWeights.pi μ).mean (observedProductDensity μ p F w) := by
          rw [observedProductDensity_mean μ p F hμ w base]
          exact lt_of_not_ge hs
        have hcap : ∀ d : ProductCylinder X, d.1.card ≤ j + r →
            d.mass μ base (observedProductDensity μ p F w) ≤ 2 := by
          intro d hd
          have hb := observedProductDensity_marginal_le μ p F hμ w hw1 hbase d.1 hd (d.assignment base)
          change productConditionalMean μ d.1 (observedProductDensity μ p F w) (d.assignment base) ≤ 2
          linarith
        obtain ⟨c, hc, hmass, hregular⟩ := ProductCylinder.exists_regular hK hτ hm hcap hcut
        have hpos : 0 < c.mass μ base (observedProductDensity μ p F w) := hτ.trans_lt hmass
        have hsize : c.1.card ≤ j + r := by omega
        have hlt := positiveCandidates_erase_card_lt μ base p F (j + r) w hw0 c hsize hpos
        have hnext : (positiveCandidates μ base p F (j + r) (c.erase F w)).card < n := hlt.trans_le hn
        obtain ⟨v, cs, hchain, hcs, hv, hvbounds⟩ := ih _ hnext (c.erase F w)
          (c.erase_nonneg F w hw0) (fun z => (c.erase_le F w hw0 z).trans (hw1 z)) le_rfl
        refine ⟨v, c :: cs, .cons c hc hmass hregular hchain, ?_, hv, hvbounds⟩
        simp only [List.length_cons]
        omega
  exact aux _ w hw0 hw1 (positiveCandidates_card_le μ base p F (j + r) w)

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}

theorem CylinderRemovalChain.decomposition (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (z : Ω) : w z = ((removedCylinderWeights F w cs).map (fun f => f z)).sum + v z := by
  induction hchain with
  | nil => simp only [removedCylinderWeights, List.map_nil, List.sum_nil, zero_add]
  | @cons w v cs c hsize hmass hbounded rest ih =>
    calc
      w z = c.cut F w z + c.erase F w z := (c.cut_add_erase F w z).symm
      _ = c.cut F w z + (((removedCylinderWeights F (c.erase F w) cs).map (fun f => f z)).sum + v z) := by rw [ih]
      _ = _ := by simp only [removedCylinderWeights, List.map_cons, List.sum_cons, add_assoc]

theorem CylinderRemovalChain.mem_mass_gt (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hw : ∀ z, 0 ≤ w z) {d : ProductCylinder X} (hd : d ∈ cs) :
    τ < d.mass μ base (observedProductDensity μ p F w) := by
  revert hw hd
  induction hchain with
  | nil => intro hw hd; simp only [List.not_mem_nil] at hd
  | @cons w v cs c hsize hmass hbounded rest ih =>
    intro hw hd
    rcases List.mem_cons.mp hd with hd | hd
    · subst d
      exact hmass
    · exact (ih (c.erase_nonneg F w hw) hd).trans_le (c.mass_erase_le d μ base p F w hw)

theorem CylinderRemovalChain.nodup [∀ i, DecidableEq (X i)]
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hτ : 0 ≤ τ) (hw : ∀ z, 0 ≤ w z) : cs.Nodup := by
  revert hw
  induction hchain with
  | nil => intro _; exact List.nodup_nil
  | @cons w v cs c hsize hmass hbounded rest ih =>
    intro hw
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (c.erase_nonneg F w hw)⟩
    intro hc
    have hm := rest.mem_mass_gt (c.erase_nonneg F w hw) hc
    rw [c.mass_erase_self] at hm
    linarith

end Erdos3

end

section

namespace Erdos3

theorem CylinderRemovalChain.removed_size_mass {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), cf.1.1.card ≤ j ∧
      τ < cf.1.mass μ base (observedProductDensity μ p F cf.2) := by
  induction hchain with
  | nil =>
    intro cf hcf
    simp only [removedCylinderWeights, List.zip_nil_left, List.not_mem_nil] at hcf
  | @cons w v cs d hsize hmass hbounded rest ih =>
    intro cf hcf
    change cf ∈ (d, d.cut F w) :: cs.zip (removedCylinderWeights F (d.erase F w) cs) at hcf
    rcases List.mem_cons.mp hcf with hcf | hcf
    · subst cf
      exact ⟨hsize, by rwa [d.mass_cut_self μ base p F w]⟩
    · exact ih cf hcf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem removedCylinderWeights_bounds {Ω ι : Type*} {X : ι → Type*}
    (F : Ω → ∀ i, X i) (w : Ω → ℝ) (cs : List (ProductCylinder X))
    (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1)
    {f : Ω → ℝ} (hf : f ∈ removedCylinderWeights F w cs) (z : Ω) :
    0 ≤ f z ∧ f z ≤ 1 := by
  induction cs generalizing w with
  | nil => simp only [removedCylinderWeights, List.not_mem_nil] at hf
  | cons c cs ih =>
    change f ∈ c.cut F w :: removedCylinderWeights F (c.erase F w) cs at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨c.cut_nonneg F w hw0 z, (c.cut_le F w hw0 z).trans (hw1 z)⟩
    · exact ih (c.erase F w) (c.erase_nonneg F w hw0)
        (fun x => (c.erase_le F w hw0 x).trans (hw1 x)) hf

theorem exists_regular_cylinder_decomposition {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (K τ η : ℝ) (j r A : ℕ) (hK : 1 ≤ K) (hτ : 0 ≤ τ) (hη : η ≤ 1)
    (hA : 1 ≤ A) (hX : ∀ i, Fintype.card (X i) ≤ A)
    (hcut : 2 ≤ τ * K ^ (j + 1))
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r))
    (w : Ω → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
      CylinderRemovalChain μ base p F K τ j r w v cs ∧ cs.Nodup ∧
      cs.length ≤ (∑ k ∈ Finset.range (j + r + 1), (Fintype.card ι).choose k) * A ^ (j + r) ∧
      (removedCylinderWeights F w cs).Pairwise (fun f g => ∀ z, f z = 0 ∨ g z = 0) ∧
      (∀ z, w z = ((removedCylinderWeights F w cs).map (fun f => f z)).sum + v z) ∧
      (∀ f ∈ removedCylinderWeights F w cs, ∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
      p.mean v ≤ τ ∧ (∀ z, 0 ≤ v z ∧ v z ≤ 1) := by
  obtain ⟨v, cs, hchain, hcount, hsmall, hv⟩ :=
    exists_finite_cylinder_removal μ hμ base p F K τ η j r hK hτ hη hcut hbase w hw0 hw1
  exact ⟨v, cs, hchain, hchain.nodup hτ hw0,
    hcount.trans (ProductCylinder.bounded_card_le (j + r) A hA hX),
    removedCylinderWeights_pairwise F w cs, hchain.decomposition,
    fun _ hf z => removedCylinderWeights_bounds F w cs hw0 hw1 hf z, hsmall, hv⟩

end Erdos3

end

end OAI
