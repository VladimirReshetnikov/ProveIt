/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.SelectedCollisionBudget
import OAI.Combinatorics.Progressions.Lattices.ResidueLinearPointCap
import OAI.Combinatorics.Progressions.Probability.AnchoredMixtureBoxTail

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def noninjectivityIndicator {J Y : Type*} (f : J → Y) : ℝ :=
  if Function.Injective f then 0 else 1

theorem noninjectivityIndicator_nonneg {J Y : Type*} (f : J → Y) :
    0 ≤ noninjectivityIndicator f := by
  unfold noninjectivityIndicator
  split_ifs <;> norm_num

theorem noninjectivityIndicator_postcompose {J Y Z : Type*} (f : J → Y) (g : Y → Z)
    (hg : Function.Injective g) :
    noninjectivityIndicator (fun j => g (f j)) = noninjectivityIndicator f := by
  have hi : Function.Injective (fun j => g (f j)) ↔ Function.Injective f :=
    ⟨fun h _ _ he => h (congrArg g he), fun h => hg.comp h⟩
  simp only [noninjectivityIndicator, hi]

theorem noninjectivityIndicator_le_pairs {J Y : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq Y] (f : J → Y) :
    noninjectivityIndicator f ≤ ∑ j, ∑ k, if j = k then 0 else if f j = f k then (1 : ℝ) else 0 := by
  have hn (j k : J) : 0 ≤ (if j = k then 0 else if f j = f k then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  by_cases hf : Function.Injective f
  · simp only [noninjectivityIndicator, ite_eq_left hf]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hn j k))
  · have hpair : ∃ j k, j ≠ k ∧ f j = f k := by
      by_contra h
      apply hf
      intro j k he
      by_contra hne
      exact h ⟨j,k,hne,he⟩
    obtain ⟨j,k,hjk,he⟩ := hpair
    simp only [noninjectivityIndicator, ite_eq_right hf]
    calc
      (1 : ℝ) = (if j = k then 0 else if f j = f k then 1 else 0) := by simp [hjk,he]
      _ ≤ ∑ l, if j = l then 0 else if f j = f l then (1 : ℝ) else 0 :=
        Finset.single_le_sum (fun l _ => hn j l) (Finset.mem_univ k)
      _ ≤ _ := Finset.single_le_sum
        (fun l _ => Finset.sum_nonneg (fun k _ => hn l k)) (Finset.mem_univ j)

namespace FiniteProbabilityWeights

theorem mean_fintype_sum {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : FiniteProbabilityWeights Ω) (f : J → Ω → ℝ) :
    p.mean (fun x => ∑ j, f j x) = ∑ j, p.mean (f j) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem noninjectivity_le {Ω J Y : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    [DecidableEq Y] (p : FiniteProbabilityWeights Ω) (F : Ω → J → Y)
    {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ j k, j ≠ k → p.mean (fun x => if F x j = F x k then 1 else 0) ≤ C) :
    p.mean (fun x => noninjectivityIndicator (F x)) ≤ (Fintype.card J : ℝ)^2*C := by
  have hm := p.mean_mono (fun x => noninjectivityIndicator_le_pairs (F x))
  simp_rw [mean_fintype_sum] at hm
  refine hm.trans ?_
  calc
    _ ≤ ∑ _j : J, ∑ _k : J, C := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases he : j = k
      · simpa only [ite_eq_left he, mean_const] using hC
      · simpa only [ite_eq_right he] using hp j k he
    _ = _ := by simp [pow_two, mul_assoc]

theorem reweightPositive_noninjectivity_le {Ω J Y : Type*} [Fintype Ω] [Fintype J]
    [DecidableEq J] [DecidableEq Y] (p : FiniteProbabilityWeights Ω) (F : Ω → J → Y)
    (D : Ω → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < p.mean D)
    {M C : ℝ} (hM : 0 ≤ M) (hcap : ∀ x, D x ≤ M) (hlower : 1/2 ≤ p.mean D)
    (hC : 0 ≤ C)
    (hp : ∀ j k, j ≠ k → p.mean (fun x => if F x j = F x k then 1 else 0) ≤ C) :
    (p.reweightPositive D hD0 hD).mean (fun x => noninjectivityIndicator (F x)) ≤
      2*M*((Fintype.card J : ℝ)^2*C) := by
  have hb : p.mean (fun x => D x * noninjectivityIndicator (F x)) ≤
      M * p.mean (fun x => noninjectivityIndicator (F x)) := by
    rw [← mean_const_mul]
    exact p.mean_mono (fun x => mul_le_mul_of_nonneg_right (hcap x) (noninjectivityIndicator_nonneg _))
  have ht := p.reweightPositive_test_le D hD0 hD (fun x => noninjectivityIndicator (F x))
    (fun x => noninjectivityIndicator_nonneg _) (a := 1/2) (ε := 0) (by norm_num) hlower
    (by simpa only [add_zero] using hb)
  have hpair := p.noninjectivity_le F hC hp
  have hmul := mul_le_mul_of_nonneg_left hpair (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
  exact (ht.trans_eq (by ring)).trans hmul

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

def jointIntegerPhysicalSite {K I : Type*} [Fintype K] (root : K → ℤ)
    (z : (I → ℤ) × (Option K × I → ℤ)) : I → ℤ :=
  z.1 + integerPhysicalSite root z.2

theorem jointIntegerPhysicalSite_cast {K I : Type*} [Fintype K]
    (root : K → ℤ) (z : (I → ℤ) × (Option K × I → ℤ)) :
    (fun i => (jointIntegerPhysicalSite root z i : ℝ)) =
      (fun i => (z.1 i : ℝ)) + physicalAffineSite root z.2 := by
  funext i
  simp only [jointIntegerPhysicalSite, Pi.add_apply, Int.cast_add,
    integerPhysicalSite_cast_apply]

theorem jointIntegerPhysicalSite_mem_box {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i ≤ N i)
    (W : Option K × I → ℝ) (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) :
    jointIntegerPhysicalSite root (z.1.val, z.2.val) ∈ integerBox N := by
  apply trimmedIntegerBox_add_mem N R hR z.1.property
  intro i
  have h := (integerPhysicalSite_abs_bound root W z.2.val
    (rectangularWeightIndices_zero_bound W z.2.property) i).trans (hwidth i)
  exact_mod_cast h

theorem noninjectivityIndicator_joint {K I S : Type*} [Fintype K]
    (site : S → K → ℤ) (z : (I → ℤ) × (Option K × I → ℤ)) :
    noninjectivityIndicator (fun s => jointIntegerPhysicalSite (site s) z) =
      noninjectivityIndicator (fun s => integerPhysicalSite (site s) z.2) :=
  noninjectivityIndicator_postcompose _ (fun x => z.1 + x)
    (fun _ _ h => add_left_cancel h)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

def rowDifferenceCoefficients {K I : Type*} [DecidableEq I]
    (r s : K → ℤ) (i : I) (z : Option K × I) : ℤ :=
  if z.2 = i then z.1.elim 0 (fun k => r k - s k) else 0

theorem rowDifferenceCoefficients_linear {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (i : I) (z : Option K × I → ℤ) :
    integerArrayLinearForm (rowDifferenceCoefficients r s i) z =
      integerPhysicalSite r z i - integerPhysicalSite s z i := by
  have he : integerArrayLinearForm (rowDifferenceCoefficients r s i) z =
      ∑ k, (r k - s k) * z (some k,i) := by
    simp [integerArrayLinearForm, rowDifferenceCoefficients, Fintype.sum_prod_type,
      Fintype.sum_option, ite_mul]
  rw [he]
  simp only [integerPhysicalSite, sub_mul, Finset.sum_sub_distrib]
  ring

theorem selectedResidue_site_collision_le {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (k : K) (hk : r k ≠ s k) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) ≤
        2*(modulus i : ℝ)/W (some k,i) := by
  let c := rowDifferenceCoefficients r s i
  have hc : c (some k,i) ≠ 0 := by
    simpa [c, rowDifferenceCoefficients] using sub_ne_zero.mpr hk
  have hp := selectedResidueSmoothPMF_linear_cap c modulus hmodulus T hT W hW hZ hscale (some k,i) hc 0
  have he : (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerArrayLinearForm c z.val = 0 then 1 else 0) ≤
        2*(modulus i : ℝ)/W (some k,i) :=
    (selectedResidueFiniteLaw_mean modulus T W hW hZ
      (fun z => if integerArrayLinearForm c z = 0 then 1 else 0)).trans_le
      ((pmf_map_toReal_indicator _ (integerArrayLinearForm c) 0).symm.trans_le hp)
  refine le_trans ((selectedResidueFiniteLaw modulus T W hW hZ).mean_mono ?_) he
  intro z
  by_cases h : integerPhysicalSite r z.val = integerPhysicalSite s z.val
  · have hz : integerArrayLinearForm c z.val = 0 := by
      rw [rowDifferenceCoefficients_linear, congrFun h i, sub_self]
    simp only [ite_eq_left h, ite_eq_left hz, le_refl]
  · simp only [ite_eq_right h]
    split_ifs <;> norm_num

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerArrayLinearForm_add {D : Type*} [Fintype D] (c a z : D → ℤ) :
    integerArrayLinearForm c (a + z) =
      integerArrayLinearForm c a + integerArrayLinearForm c z := by
  simp only [integerArrayLinearForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

namespace BooleanCubeKernel

theorem anchored_selectedResidue_site_collision_le {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (anchor : Option K × I → ℤ) (r s : K → ℤ) (k : K) (hk : r k ≠ s k) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r (anchor + z.val) =
        integerPhysicalSite s (anchor + z.val) then 1 else 0) ≤
          2*(modulus i : ℝ)/W (some k,i) := by
  let c := rowDifferenceCoefficients r s i
  have hc : c (some k,i) ≠ 0 := by
    simpa [c, rowDifferenceCoefficients] using sub_ne_zero.mpr hk
  let target := -integerArrayLinearForm c anchor
  have hp := selectedResidueSmoothPMF_linear_cap c modulus hmodulus T hT W hW hZ
    hscale (some k,i) hc target
  have he : (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerArrayLinearForm c z.val = target then 1 else 0) ≤
        2*(modulus i : ℝ)/W (some k,i) :=
    (selectedResidueFiniteLaw_mean modulus T W hW hZ
      (fun z => if integerArrayLinearForm c z = target then 1 else 0)).trans_le
      ((pmf_map_toReal_indicator _ (integerArrayLinearForm c) target).symm.trans_le hp)
  refine le_trans ((selectedResidueFiniteLaw modulus T W hW hZ).mean_mono ?_) he
  intro z
  by_cases h : integerPhysicalSite r (anchor + z.val) = integerPhysicalSite s (anchor + z.val)
  · have hz : integerArrayLinearForm c z.val = target := by
      have hs : integerArrayLinearForm c (anchor + z.val) = 0 := by
        rw [rowDifferenceCoefficients_linear, congrFun h i, sub_self]
      rw [integerArrayLinearForm_add] at hs
      dsimp only [target]
      omega
    simp only [ite_eq_left h, ite_eq_left hz, le_refl]
  · simp only [ite_eq_right h]
    split_ifs <;> norm_num

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem noninjectivityIndicator_centered {K I S : Type*} [Fintype K]
    (site : S → K → ℤ) (N : I → ℕ) (z : Option K × I → ℤ) :
    noninjectivityIndicator (fun s => centeredIntegerPhysicalSite (site s) N z) =
      noninjectivityIndicator (fun s => integerPhysicalSite (site s) z) := by
  exact noninjectivityIndicator_postcompose _ (fun x => integerBoxCenter N + x)
    (by intro x y h; exact add_left_cancel h)

theorem selectedResidue_distinct_collision_le {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (hrs : r ≠ s) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i)) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) ≤
        2*(modulus i : ℝ)/L := by
  have hdiff : ∃ k, r k ≠ s k := by
    by_contra h
    apply hrs
    funext k
    by_contra hk
    exact h ⟨k,hk⟩
  obtain ⟨k,hk⟩ := hdiff
  exact (selectedResidue_site_collision_le r s k hk i modulus hmodulus T hT W hW hZ hscale).trans
    (div_le_div_of_nonneg_left (by positivity) hL (hwidth k))

theorem selectedResidue_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i)) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => noninjectivityIndicator (fun s => integerPhysicalSite (site s) z.val)) ≤
        (Fintype.card S : ℝ)^2*(2*(modulus i : ℝ)/L) := by
  apply FiniteProbabilityWeights.noninjectivity_le _ _ (by positivity)
  intro s t hst
  exact selectedResidue_distinct_collision_le (site s) (site t) (fun h => hst (hsite h)) i
    modulus hmodulus T hT W hW hZ hscale hL hwidth

theorem selectedResidue_tilted_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i))
    (D : (Option K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (hlower : 1/2 ≤ selectedResidueDensityMass modulus T W D)
    {M : ℝ} (hM : 0 ≤ M) (hcap : ∀ z, D z ≤ M) :
    (∑' z, (selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal *
      noninjectivityIndicator (fun s => integerPhysicalSite (site s) z)) ≤
        2*M*((Fintype.card S : ℝ)^2*(2*(modulus i : ℝ)/L)) := by
  rw [← selectedResidueTiltedFiniteLaw_mean modulus T W hW hZ D hD0 hD
    (fun z => noninjectivityIndicator (fun s => integerPhysicalSite (site s) z))]
  rw [selectedResidueTiltedFiniteLaw]
  apply FiniteProbabilityWeights.reweightPositive_noninjectivity_le
    (selectedResidueFiniteLaw modulus T W hW hZ)
    (fun z s => integerPhysicalSite (site s) z.val)
    (fun z => D z.val) (fun z => hD0 z.val)
    (by rw [selectedResidueFiniteLaw_densityMass]; exact hD) hM (fun z => hcap z.val)
  · rwa [selectedResidueFiniteLaw_densityMass]
  · positivity
  · intro s t hst
    exact selectedResidue_distinct_collision_le (site s) (site t) (fun h => hst (hsite h)) i
      modulus hmodulus T hT W hW hZ hscale hL hwidth

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem anchored_selectedResidue_distinct_collision_le {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (anchor : Option K × I → ℤ) (r s : K → ℤ) (hrs : r ≠ s) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i)) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r (anchor + z.val) = integerPhysicalSite s (anchor + z.val) then 1 else 0) ≤
        2*(modulus i : ℝ)/L := by
  have hdiff : ∃ k, r k ≠ s k := by
    by_contra h
    apply hrs
    funext k
    by_contra hk
    exact h ⟨k,hk⟩
  obtain ⟨k,hk⟩ := hdiff
  exact (anchored_selectedResidue_site_collision_le anchor r s k hk i modulus hmodulus T hT W hW hZ hscale).trans
    (div_le_div_of_nonneg_left (by positivity) hL (hwidth k))

theorem anchored_selectedResidue_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (anchor : Option K × I → ℤ) (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i)) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => noninjectivityIndicator (fun s => integerPhysicalSite (site s) (anchor + z.val))) ≤
        (Fintype.card S : ℝ)^2*(2*(modulus i : ℝ)/L) := by
  apply FiniteProbabilityWeights.noninjectivity_le _ _ (by positivity)
  intro s t hst
  exact anchored_selectedResidue_distinct_collision_le anchor (site s) (site t) (fun h => hst (hsite h)) i
    modulus hmodulus T hT W hW hZ hscale hL hwidth

theorem anchored_selectedResidue_tilted_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (anchor : Option K × I → ℤ) (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i))
    (D : (Option K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W (fun z => D (anchor + z)))
    (hlower : 1/2 ≤ selectedResidueDensityMass modulus T W (fun z => D (anchor + z)))
    {M : ℝ} (hM : 0 ≤ M) (hcap : ∀ z, D z ≤ M) :
    (∑' z, (translatedSelectedResidueDensityPMF anchor modulus T W hW hZ D hD0 hD z).toReal *
      noninjectivityIndicator (fun s => integerPhysicalSite (site s) z)) ≤
        2*M*((Fintype.card S : ℝ)^2*(2*(modulus i : ℝ)/L)) := by
  rw [translatedSelectedResidueDensityPMF_mean]
  rw [← selectedResidueTiltedFiniteLaw_mean modulus T W hW hZ
    (fun z => D (anchor + z)) (fun _ => hD0 _) hD
    (fun z => noninjectivityIndicator (fun s => integerPhysicalSite (site s) (anchor + z)))]
  rw [selectedResidueTiltedFiniteLaw]
  apply FiniteProbabilityWeights.reweightPositive_noninjectivity_le
    (selectedResidueFiniteLaw modulus T W hW hZ)
    (fun z s => integerPhysicalSite (site s) (anchor + z.val))
    (fun z => D (anchor + z.val)) (fun z => hD0 (anchor + z.val))
    (by rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (fun z => D (anchor + z))]; exact hD)
    hM (fun z => hcap (anchor + z.val))
  · rwa [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (fun z => D (anchor + z))]
  · positivity
  · intro s t hst
    exact anchored_selectedResidue_distinct_collision_le anchor (site s) (site t) (fun h => hst (hsite h)) i
      modulus hmodulus T hT W hW hZ hscale hL hwidth

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem anchored_selectedResidue_tilted_collision_small {K X S : Type*}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (m : ℕ) (anchor : Option K × X → ℤ) (site : S → K → ℤ) (hsite : Function.Injective site) (i : X)
    {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i) (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (T : Finset (ColumnResiduePattern (Option K) X modulus)) (hT : T.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (selectedCollisionLog m P) ≤ N) (hwidth : ∀ k, ρ*N ≤ W (some k,i))
    (D : (Option K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W (fun z => D (anchor + z)))
    (hlower : 1/2 ≤ selectedResidueDensityMass modulus T W (fun z => D (anchor + z)))
    (hcap : ∀ z, D z ≤ Real.exp (selectedDensityLog m P)) :
    (∑' z, (translatedSelectedResidueDensityPMF anchor modulus T W hW hZ D hD0 hD z).toReal *
      noninjectivityIndicator (fun s => integerPhysicalSite (site s) z)) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hcollision := anchored_selectedResidue_tilted_noninjectivity_le anchor site hsite i
    modulus hmodulus T hT W hW hZ hscale (mul_pos hρ hN0) hwidth D hD0 hD hlower
    (Real.exp_pos _).le hcap
  exact hcollision.trans (collision_error_of_exp_size m (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hρ hδ (integerSites_card_le_exp site hsite hP hK hbound)
    hmodP hρP hδP hN)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedResidue_tilted_collision_small {K X S : Type*}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (m : ℕ) (site : S → K → ℤ) (hsite : Function.Injective site) (i : X)
    {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i) (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (T : Finset (ColumnResiduePattern (Option K) X modulus)) (hT : T.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (selectedCollisionLog m P) ≤ N) (hwidth : ∀ k, ρ*N ≤ W (some k,i))
    (D : (Option K × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D)
    (hlower : 1/2 ≤ selectedResidueDensityMass modulus T W D)
    (hcap : ∀ z, D z ≤ Real.exp (selectedDensityLog m P)) :
    (∑' z, (selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal *
      noninjectivityIndicator (fun s => integerPhysicalSite (site s) z)) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hcollision := selectedResidue_tilted_noninjectivity_le site hsite i
    modulus hmodulus T hT W hW hZ hscale (mul_pos hρ hN0) hwidth D hD0 hD hlower
    (Real.exp_pos _).le hcap
  exact hcollision.trans (collision_error_of_exp_size m (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hρ hδ (integerSites_card_le_exp site hsite hP hK hbound)
    hmodP hρP hδP hN)

end Erdos3.BooleanCubeKernel

end

end OAI
