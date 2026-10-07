import OAI.Combinatorics.Progressions.Dynamics.EarlyFiberCapBudget
import OAI.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
import OAI.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_subset_le_card_ratio {X : Type*} [DecidableEq X]
    (A B : Finset X) (hA : A.Nonempty) (hAB : A ⊆ B)
    (f : X → ℝ) (hf : ∀ x ∈ B, 0 ≤ f x) :
    (𝔼 x ∈ A, f x) ≤ ((B.card : ℝ) / A.card) * (𝔼 x ∈ B, f x) := by
  have hB0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast (hA.mono hAB).card_ne_zero
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  calc
    _ ≤ (∑ x ∈ B, f x) / (A.card : ℝ) := div_le_div_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x hx _ => hf x hx)) (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem expect_injective_le_card_ratio {X Y : Type*} [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (g : X → Y)
    (hg : Set.InjOn g A) (hB : ∀ x ∈ A, g x ∈ B)
    (f : Y → ℝ) (hf : ∀ y ∈ B, 0 ≤ f y) :
    (𝔼 x ∈ A, f (g x)) ≤ ((B.card : ℝ) / A.card) * (𝔼 y ∈ B, f y) := by
  have h := expect_subset_le_card_ratio (A.image g) B (hA.image g)
    (Finset.image_subset_iff.mpr hB) f hf
  simpa only [Finset.expect_image hg, Finset.card_image_of_injOn hg] using h

namespace FiniteProbabilityWeights

theorem mean_finset_expect {X Z : Type*} [Fintype Z] (p : FiniteProbabilityWeights Z)
    (A : Finset X) (f : Z → X → ℝ) :
    p.mean (fun z => 𝔼 x ∈ A, f z x) = 𝔼 x ∈ A, p.mean (fun z => f z x) := by
  unfold mean
  simp_rw [Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

theorem translated_subset_mixture_le {X Y Z : Type*} [Fintype Z] [DecidableEq Y]
    (p : FiniteProbabilityWeights Z) (A : Finset X) (B : Finset Y) (hA : A.Nonempty)
    (g : Z → X → Y) (hg : ∀ z, Set.InjOn (g z) A)
    (hB : ∀ z x, x ∈ A → g z x ∈ B)
    (f : Y → ℝ) (hf : ∀ y ∈ B, 0 ≤ f y) :
    (𝔼 x ∈ A, p.mean (fun z => f (g z x))) ≤
      ((B.card : ℝ) / A.card) * (𝔼 y ∈ B, f y) := by
  rw [← p.mean_finset_expect]
  exact (p.mean_mono (fun z => expect_injective_le_card_ratio A B hA
    (g z) (hg z) (hB z) f hf)).trans_eq (p.mean_const _)

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

theorem abs_expect_parent_sub_subset_le_Icc
    (S T : Finset α) (hT : T.Nonempty) (hTS : T ⊆ S)
    (f : α → ℝ) {a b : ℝ} (hf : ∀ x ∈ S, f x ∈ Set.Icc a b) :
    |(𝔼 x ∈ S, f x) - (𝔼 x ∈ T, f x)| ≤
      (b - a) * ((S.card - T.card : ℕ) : ℝ) / (S.card : ℝ) := by
  have hS : S.Nonempty := hT.mono hTS
  have hS0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hmeanlo : a ≤ 𝔼 x ∈ T, f x :=
    Finset.le_expect hT (fun x hx => (hf x (hTS hx)).1)
  have hmeanhi : (𝔼 x ∈ T, f x) ≤ b :=
    Finset.expect_le hT (fun x hx => (hf x (hTS hx)).2)
  have hsum : (∑ x ∈ S \ T, f x) + ∑ x ∈ T, f x = ∑ x ∈ S, f x :=
    Finset.sum_sdiff hTS
  have hc : ((S \ T).card : ℝ) + (T.card : ℝ) = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hTS
  have heq : (𝔼 x ∈ S, f x) - 𝔼 x ∈ T, f x =
      (∑ x ∈ S \ T, (f x - (𝔼 y ∈ T, f y))) / (S.card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [sub_div, mul_div_assoc, Finset.expect_eq_sum_div_card S]
    have hTeq := Finset.card_mul_expect T f
    field_simp
    linear_combination -hsum - hTeq + (𝔼 y ∈ T, f y) * hc
  have hbound : |∑ x ∈ S \ T, (f x - (𝔼 y ∈ T, f y))| ≤
      (b - a) * ((S \ T).card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ S \ T, |f x - (𝔼 y ∈ T, f y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ S \ T, (b - a) := by
        apply Finset.sum_le_sum
        intro x hx
        have hfx := hf x (Finset.mem_sdiff.mp hx).1
        exact abs_le.mpr ⟨by linarith [hfx.1], by linarith [hfx.2]⟩
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [heq, abs_div, abs_of_pos hSpos]
  exact (div_le_div_of_nonneg_right hbound hSpos.le).trans_eq (by rw [Finset.card_sdiff_of_subset hTS])

theorem abs_expect_parent_sub_subset_le_unit
    (S T : Finset α) (hT : T.Nonempty) (hTS : T ⊆ S)
    (f : α → ℝ) (hf : ∀ x ∈ S, f x ∈ Set.Icc (0 : ℝ) 1) :
    |(𝔼 x ∈ S, f x) - (𝔼 x ∈ T, f x)| ≤
      ((S.card - T.card : ℕ) : ℝ) / (S.card : ℝ) := by
  simpa only [sub_zero, one_mul] using abs_expect_parent_sub_subset_le_Icc S T hT hTS f hf

theorem abs_expect_parent_sub_subset_le_abs
    (S T : Finset α) (hT : T.Nonempty) (hTS : T ⊆ S)
    (f : α → ℝ) (hf : ∀ x ∈ S, |f x| ≤ 1) :
    |(𝔼 x ∈ S, f x) - (𝔼 x ∈ T, f x)| ≤
      2 * ((S.card - T.card : ℕ) : ℝ) / (S.card : ℝ) := by
  have h := abs_expect_parent_sub_subset_le_Icc S T hT hTS f
    (a := -1) (b := 1) (fun x hx => abs_le.mp (hf x hx))
  norm_num only [sub_neg_eq_add, one_add_one_eq_two] at h
  exact h

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem mass_above_double_cap_le {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) :
    q.mass (Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)) ≤
      2 * p.excessMass q C := by
  let S := Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)
  calc
    q.mass S ≤ ∑ x ∈ S, 2 * max (q.weight x - C*p.weight x) 0 := by
      apply Finset.sum_le_sum
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      have he := le_max_left (q.weight x - C*p.weight x) 0
      nlinarith
    _ = 2 * ∑ x ∈ S, max (q.weight x - C*p.weight x) 0 := by rw [Finset.mul_sum]
    _ ≤ 2 * p.excessMass q C := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => le_max_right _ _)

theorem mass_above_double_cap_le_of_excess {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) {C ε : ℝ} (h : p.excessMass q C ≤ ε) :
    q.mass (Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)) ≤ 2*ε :=
  (mass_above_double_cap_le p q C).trans (mul_le_mul_of_nonneg_left h (by norm_num))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem siteLaw_excess_le {Ω T X : Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X) (r : FiniteProbabilityWeights X)
    {C ε : ℝ}
    (hdom : ∀ t (f : X → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      p.mean (fun z => f (F z t)) ≤ C * r.mean f + ε) :
    r.excessMass (p.siteLaw F) C ≤ ε := by
  apply excessMass_le_of_mass_le
  intro S
  rw [← mean_indicator, ← mean_indicator, siteLaw_mean]
  rw [p.mean_finset_expect]
  apply Finset.expect_le Finset.univ_nonempty
  intro t _
  apply hdom t (fun x => if x ∈ S then 1 else 0)
  intro x
  split_ifs <;> constructor <;> norm_num

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {I K : Type*} [Fintype I] [Fintype K]
variable (root : K → ℤ) (stride : I → ℕ)
variable (T : Finset (ColumnResiduePattern (Option K) I stride))
variable (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z)
variable (D : (Option K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
variable (hD : 0 < selectedResidueDensityMass stride T W D) {C ε : ℝ}
variable (hdom : ∀ φ : (I → ℝ) → ℝ, (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
  (∑' z, (selectedResidueDensityPMF stride T W hW hZ D hD0 hD z).toReal * φ (physicalAffineSite root z)) ≤
    C*(∑' z, (selectedResidueSmoothPMF stride T W hW hZ z).toReal * φ (physicalAffineSite root z)) + ε)

include hdom in
theorem selectedResidue_physical_event_le (E : Set (I → ℝ)) :
    (∑' z, (selectedResidueDensityPMF stride T W hW hZ D hD0 hD z).toReal *
      (if physicalAffineSite root z ∈ E then 1 else 0)) ≤
    C*(∑' z, (selectedResidueSmoothPMF stride T W hW hZ z).toReal *
      (if physicalAffineSite root z ∈ E then 1 else 0)) + ε := by
  apply hdom (fun v => if v ∈ E then 1 else 0)
  intro v
  split_ifs <;> constructor <;> norm_num

include hdom in
theorem selectedResidue_physical_excess_le {Y : Type*} [Fintype Y] (F : (I → ℝ) → Y) :
    ((selectedResidueFiniteLaw stride T W hW hZ).fiberLaw
      (fun z => F (physicalAffineSite root z.val))).excessMass
      ((selectedResidueTiltedFiniteLaw stride T W hW hZ D hD0 hD).fiberLaw
        (fun z => F (physicalAffineSite root z.val))) C ≤ ε := by
  apply selectedResidue_fiber_excess_le stride T W hW hZ D hD0 hD
    (fun z => F (physicalAffineSite root z))
  intro S
  apply hdom (fun v => if F v ∈ S then 1 else 0)
  intro v
  split_ifs <;> constructor <;> norm_num

include hdom in
theorem selectedResidue_physical_tail_le {Y : Type*} [Fintype Y] (F : (I → ℝ) → Y) :
    let p := (selectedResidueFiniteLaw stride T W hW hZ).fiberLaw
      (fun z => F (physicalAffineSite root z.val))
    let q := (selectedResidueTiltedFiniteLaw stride T W hW hZ D hD0 hD).fiberLaw
      (fun z => F (physicalAffineSite root z.val))
    q.mass (Finset.univ.filter (fun y => 2*C*p.weight y < q.weight y)) ≤ 2*ε :=
  FiniteProbabilityWeights.mass_above_double_cap_le_of_excess _ _
    (selectedResidue_physical_excess_le root stride T W hW hZ D hD0 hD hdom F)

end Erdos3.BooleanCubeKernel

namespace Erdos3

open scoped BigOperators

theorem normalizedEarlyFiberCap_exp_bound {m : ℕ} (a n : Fin m → ℕ) (R V : Fin m → ℝ) {P : ℝ}
    (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P) (hR : ∀ j, 0 < R j) (hV : ∀ j, 0 ≤ V j)
    (ha : ∀ j, (a j : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hVP : ∀ j, V j ≤ Real.exp P) :
    2*(∏ j, earlyConstantDensityCap (a j) (n j) (R j) (V j)) ≤
      Real.exp (earlyFiberCapLog P + 2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 2 * Real.exp (earlyFiberCapLog P) := mul_le_mul_of_nonneg_left
      (earlyFiberCap_exp_bound a n R V hP hm hR hV ha hn hA hRP hVP) (by norm_num)
    _ ≤ Real.exp 2 * Real.exp (earlyFiberCapLog P) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem trimmedIntegerBox_card_ratio_le_two {I : Type*} [Fintype I] [DecidableEq I]
    (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (hloss : (∑ i, 2 * (R i : ℝ) / N i) ≤ 1/2) :
    ((integerBox N).card : ℝ) / (trimmedIntegerBox N R).card ≤ 2 := by
  have hA : (0 : ℝ) < (trimmedIntegerBox N R).card := by
    exact_mod_cast (trimmedIntegerBox_nonempty N R hR).card_pos
  have hN (i : I) : 0 < N i := lt_of_le_of_lt (Nat.zero_le _) (hR i)
  have hBnat : 0 < (integerBox N).card := by
    rw [card_integerBox]
    exact Finset.prod_pos (fun i _ => hN i)
  have hB : (0 : ℝ) < (integerBox N).card := by exact_mod_cast hBnat
  have h := (trimmedIntegerBox_card_deficit N R hN (fun i => (hR i).le)).trans hloss
  have hh : (1/2 : ℝ) ≤ ((trimmedIntegerBox N R).card : ℝ) / (integerBox N).card := by linarith
  have hm := (le_div_iff₀ hB).mp hh
  apply (div_le_iff₀ hA).mpr
  linarith

namespace BooleanCubeKernel

theorem selectedResidue_trimmed_reference_le {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (hloss : (∑ i, 2 * (R i : ℝ) / N i) ≤ 1/2)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, 0 ≤ f x) :
    (𝔼 a ∈ trimmedIntegerBox N R,
      ∑' z, (selectedResidueSmoothPMF modulus T W hW hZ z).toReal *
        f (a + integerPhysicalSite root z)) ≤ 2 * (𝔼 x ∈ integerBox N, f x) := by
  let p := selectedResidueFiniteLaw modulus T W hW hZ
  have hnoise (z : rectangularWeightIndices 0 W 1) (i : I) :
      |integerPhysicalSite root z.val i| ≤ (R i : ℤ) := by
    have h := (integerPhysicalSite_abs_bound root W z.val
      (rectangularWeightIndices_zero_bound W z.property) i).trans (hwidth i)
    exact_mod_cast h
  have h := p.translated_subset_mixture_le (trimmedIntegerBox N R) (integerBox N)
    (trimmedIntegerBox_nonempty N R hR) (fun z a => a + integerPhysicalSite root z.val)
    (fun _ _ _ _ _ he => add_right_cancel he)
    (fun z _ ha => trimmedIntegerBox_add_mem N R (fun i => (hR i).le) ha _ (hnoise z)) f hf
  have hb := h.trans (mul_le_mul_of_nonneg_right (trimmedIntegerBox_card_ratio_le_two N R hR hloss)
    (Finset.expect_nonneg hf))
  dsimp only [p] at hb
  have he (a : I → ℤ) := selectedResidueFiniteLaw_mean modulus T W hW hZ
    (fun z => f (a + integerPhysicalSite root z))
  simpa only [he] using hb

theorem selectedResidue_trimmed_domination_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (hloss : (∑ i, 2 * (R i : ℝ) / N i) ≤ 1/2)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, 0 ≤ f x)
    (L : (I → ℤ) → ℝ) {M ε : ℝ} (hM : 0 ≤ M)
    (hL : ∀ a ∈ trimmedIntegerBox N R,
      L a ≤ M * (∑' z, (selectedResidueSmoothPMF modulus T W hW hZ z).toReal *
        f (a + integerPhysicalSite root z)) + ε) :
    (𝔼 a ∈ trimmedIntegerBox N R, L a) ≤ 2*M*(𝔼 x ∈ integerBox N, f x) + ε := by
  have h := Finset.expect_le_expect hL
  rw [Finset.expect_add_distrib, Finset.expect_const (trimmedIntegerBox_nonempty N R hR),
    ← Finset.mul_expect] at h
  have hb := selectedResidue_trimmed_reference_le root N R hR hloss modulus T W hW hZ hwidth f hf
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hb hM])

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem selectedResidue_anchored_trimmed_reference_le {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (anchor : Option K × I → ℤ)
    (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (hloss : (∑ i, 2 * (R i : ℝ) / N i) ≤ 1/2)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hnoise : ∀ u ∈ rectangularWeightIndices 0 W 1, ∀ i,
      |integerPhysicalSite root (anchor + u) i| ≤ (R i : ℤ))
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, 0 ≤ f x) :
    (𝔼 b ∈ trimmedIntegerBox N R,
      ∑' u, (selectedResidueSmoothPMF modulus T W hW hZ u).toReal *
        f (b + integerPhysicalSite root (anchor + u))) ≤
      2 * (𝔼 x ∈ integerBox N, f x) := by
  let p := selectedResidueFiniteLaw modulus T W hW hZ
  have h := p.translated_subset_mixture_le (trimmedIntegerBox N R) (integerBox N)
    (trimmedIntegerBox_nonempty N R hR)
    (fun u b => b + integerPhysicalSite root (anchor + u.val))
    (fun _ _ _ _ _ he => add_right_cancel he)
    (fun u _ hb => trimmedIntegerBox_add_mem N R (fun i => (hR i).le) hb _
      (hnoise u.val u.property)) f hf
  have hb := h.trans (mul_le_mul_of_nonneg_right
    (trimmedIntegerBox_card_ratio_le_two N R hR hloss) (Finset.expect_nonneg hf))
  dsimp only [p] at hb
  have he (b : I → ℤ) := selectedResidueFiniteLaw_mean modulus T W hW hZ
    (fun u => f (b + integerPhysicalSite root (anchor + u)))
  simpa only [he] using hb

theorem selectedResidue_anchored_trimmed_domination_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (anchor : Option K × I → ℤ)
    (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (hloss : (∑ i, 2 * (R i : ℝ) / N i) ≤ 1/2)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hnoise : ∀ u ∈ rectangularWeightIndices 0 W 1, ∀ i,
      |integerPhysicalSite root (anchor + u) i| ≤ (R i : ℤ))
    (φ : (I → ℝ) → ℝ) (hφ : ∀ v, 0 ≤ φ v)
    (L : (I → ℤ) → ℝ) {M ε : ℝ} (hM : 0 ≤ M)
    (hL : ∀ b ∈ trimmedIntegerBox N R,
      L b ≤ M * (∑' u, (selectedResidueSmoothPMF modulus T W hW hZ u).toReal *
        φ (physicalAffineSite root ((integerBaseTranslation b + anchor) + u))) + ε) :
    (𝔼 b ∈ trimmedIntegerBox N R, L b) ≤
      2*M*(𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + ε := by
  let f := fun x : I → ℤ => φ (fun i => (x i : ℝ))
  have he (b : I → ℤ) (u : Option K × I → ℤ) :
      φ (physicalAffineSite root ((integerBaseTranslation b + anchor) + u)) =
        f (b + integerPhysicalSite root (anchor + u)) := by
    congr 1
    funext i
    rw [add_assoc]
    simp only [← integerPhysicalSite_cast_apply, integerPhysicalSite_baseTranslation_add,
      Pi.add_apply]
  have h := Finset.expect_le_expect hL
  simp_rw [he] at h
  rw [Finset.expect_add_distrib, Finset.expect_const (trimmedIntegerBox_nonempty N R hR),
    ← Finset.mul_expect] at h
  have hb := selectedResidue_anchored_trimmed_reference_le root anchor N R hR hloss
    modulus T W hW hZ hnoise f (fun x _ => hφ _)
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hb hM])

end Erdos3.BooleanCubeKernel

end

end OAI
