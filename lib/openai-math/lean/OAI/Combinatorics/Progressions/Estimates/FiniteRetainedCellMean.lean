/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxControl

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

theorem residuePhysicalTruncation_cap (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (a : I → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta b) (x : I → ℤ) :
    |residuePhysicalTruncation lo N M a hne q b f x| ≤ residueTruncationCap ι b eta := by
  let := hne
  let p := FiniteProbabilityWeights.uniform
    (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a)
  let F := fun z : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a =>
    primeCoordinateObservation q (fun i => (z i).val)
  let w := fun z : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) a => f (fun i => (z i).val)
  have hw (z) : 0 ≤ w z ∧ w z ≤ 1 := by
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro i
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z i).property).1
  have hcap (S : Finset ι) (hS : S ∈ lowDegreeCoordinateSets ι b) :
      |productANOVA (primeCoordinateReference (σ := I) q) S
        (residuePrimeCoordinateDensity lo N M a hne q f) (primeCoordinateObservation q x)| ≤
      (2 : ℝ) ^ b * (1 + eta) := by
    have h := observedProductDensity_component_cap (primeCoordinateReference (σ := I) q) p F
      (primeCoordinateReference_weight_pos q) w zero_le_one heta hw hclose S
      ((mem_lowDegreeCoordinateSets ι b S).mp hS) (primeCoordinateObservation q x)
    simpa only [mul_one, residuePrimeCoordinateDensity, p, F, w] using h
  unfold residuePhysicalTruncation productANOVATruncation
  calc
    _ ≤ ∑ S ∈ lowDegreeCoordinateSets ι b,
        |productANOVA (primeCoordinateReference (σ := I) q) S
          (residuePrimeCoordinateDensity lo N M a hne q f) (primeCoordinateObservation q x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ lowDegreeCoordinateSets ι b, (2 : ℝ) ^ b * (1 + eta) :=
      Finset.sum_le_sum hcap
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, residueTruncationCap]; ring

theorem physicalBoxTruncation_cap (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ∀ c : (∀ i, (P i).Label), ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c)
        q (fun _ => 1)) eta b) (x : I → ℤ) :
    |physicalBoxTruncation lo N P hpos q b f x| ≤ residueTruncationCap ι b eta := by
  by_cases hx : x ∈ translatedIntegerBox lo N
  · simp only [physicalBoxTruncation, dite_eq_left hx]
    apply residuePhysicalTruncation_cap _ _ _ _ _ q b f _ heta
      (hclose (physicalBoxCell lo N P ⟨x, hx⟩)) x
    intro z hz
    exact hf z (physicalBoxCell_subset lo N P hstep hpos _ hz)
  · simp only [physicalBoxTruncation, dite_eq_right hx, abs_zero]
    unfold residueTruncationCap
    positivity

theorem weighted_event_discard_error {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (bad : X → Prop) (v g : X → ℝ)
    (hv : ∀ x, 0 ≤ v x ∧ v x ≤ 1) {C beta : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x, bad x → |g x| ≤ C) (hbad : p.eventProbability bad ≤ beta) :
    |p.mean (fun x => v x * g x) - p.mean (fun x => if bad x then 0 else v x * g x)| ≤ C * beta := by
  have heq : p.mean (fun x => v x * g x) - p.mean (fun x => if bad x then 0 else v x * g x) =
      p.mean (fun x => if bad x then v x * g x else 0) := by
    rw [← p.mean_sub]
    congr 1
    funext x
    split_ifs <;> simp
  rw [heq]
  apply (p.abs_mean_le_mean_abs _).trans
  calc
    _ ≤ p.mean (fun x => C * (if bad x then 1 else 0)) := by
      apply p.mean_mono
      intro x
      by_cases hx : bad x
      · simp only [ite_eq_left hx, abs_mul, abs_of_nonneg (hv x).1, mul_one]
        exact (mul_le_mul (hv x).2 (hg x hx) (abs_nonneg _) zero_le_one).trans_eq (one_mul C)
      · simp only [ite_eq_right hx, abs_zero, mul_zero]
        rfl
    _ = C * p.eventProbability bad := p.mean_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbad hC

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_mean_le_of_retained_cells {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (cell : X → A) (bad : X → Prop) (f : X → ℝ)
    (hsat : ∀ x y, cell x = cell y → (bad x ↔ bad y))
    {R C beta : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbad : p.eventProbability bad ≤ beta) (hcap : ∀ x, bad x → |f x| ≤ C)
    (hcell : ∀ x, ¬ bad x → finiteCellMean p cell f (cell x) ≤
      R * (finiteCellWeights p cell).weight (cell x)) :
    p.mean f ≤ R + C * beta := by
  let kept := fun x => if bad x then 0 else f x
  have hlocal (a : A) : finiteCellMean p cell kept a ≤ R * (finiteCellWeights p cell).weight a := by
    by_cases ha : ∃ x, cell x = a ∧ ¬ bad x
    · obtain ⟨x, hxa, hx⟩ := ha
      have he : finiteCellMean p cell kept a = finiteCellMean p cell f a := by
        unfold finiteCellMean
        congr 1
        funext y
        by_cases hy : cell y = a
        · have hn : ¬ bad y := fun h => hx ((hsat y x (hy.trans hxa.symm)).mp h)
          simp only [kept, ite_eq_left hy, ite_eq_right hn]
        · simp only [ite_eq_right hy]
      rw [he, ← hxa]
      exact hcell x hx
    · have he : finiteCellMean p cell kept a = 0 := by
        unfold finiteCellMean
        have hp (x : X) : (if cell x = a then kept x else 0) = 0 := by
          by_cases hx : cell x = a
          · have hb : bad x := by by_contra hn; exact ha ⟨x, hx, hn⟩
            simp only [kept, ite_eq_left hx, ite_eq_left hb]
          · exact ite_eq_right hx
        simp only [hp, p.mean_const]
      rw [he]
      exact mul_nonneg hR ((finiteCellWeights p cell).nonneg a)
  have hk : p.mean kept ≤ R := by
    rw [← finiteCellMean_sum p cell kept]
    calc
      _ ≤ ∑ a, R * (finiteCellWeights p cell).weight a := Finset.sum_le_sum (fun a _ => hlocal a)
      _ = R := by rw [← Finset.mul_sum, (finiteCellWeights p cell).total, mul_one]
  have he := weighted_event_discard_error p bad (fun _ => 1) f (fun _ => ⟨zero_le_one, le_rfl⟩)
    hC hcap hbad
  simp only [one_mul] at he
  have hu := (abs_le.mp he).2
  change p.mean f - p.mean kept ≤ C * beta at hu
  linarith

end Erdos3

end

end OAI
