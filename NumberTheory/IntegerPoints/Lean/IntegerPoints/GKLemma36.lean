import IntegerPoints.GKLemma34
import IntegerPoints.GKLemma35

/-!
# Graham–Kolesnik, Lemma 3.6 (B-process asymptotic): reusable foundations

This module develops the proof of Graham–Kolesnik Lemma 3.6.  The first layer records the
structural facts shared by the raw Poisson/stationary-phase estimate and the later B-process:

* subtracting the integer-frequency linear phase preserves all derivatives of order at least two;
* negative second derivative makes `f'` antitone, with a quantitative endpoint-drop bound;
* the Poisson interval with two padding frequencies at each end splits exactly into two outer
  two-point intervals and the stationary interval; and
* the number of stationary frequencies is bounded directly by the derivative span.

The interval and cardinality statements deliberately cover the one-past case
`⌈α⌉ = ⌊β⌋ + 1`, where the stationary interval is empty.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace GK36

/-- The phase `f(x) - νx` occurring after Poisson summation. -/
noncomputable def phase (f : ℝ → ℝ) (ν : ℤ) (x : ℝ) : ℝ := f x - (ν : ℝ) * x

/-- Subtracting a linear phase preserves the differentiability class of `f`. -/
theorem phase_contDiff {n : WithTop ℕ∞} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (ν : ℤ) :
    ContDiff ℝ n (phase f ν) := by
  unfold phase
  exact hf.sub (contDiff_const.mul contDiff_id)

/-- The first derivative of `f(x) - νx` is `f'(x) - ν`. -/
theorem deriv_phase {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (ν : ℤ) :
    deriv (phase f ν) = fun x => deriv f x - (ν : ℝ) := by
  funext x
  unfold phase
  simpa only [id_eq, deriv_const_mul_id] using
    (deriv_fun_sub hf.differentiable_one.differentiableAt
      (differentiableAt_id.const_mul (ν : ℝ)))

/-- A linear phase has no effect on any iterated derivative of order at least two. -/
theorem iteratedDeriv_phase {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (hn : 2 ≤ n)
    (ν : ℤ) : iteratedDeriv n (phase f ν) = iteratedDeriv n f := by
  have hlin : ContDiff ℝ n (fun x : ℝ => (ν : ℝ) * x) := contDiff_const.mul contDiff_id
  funext x
  change iteratedDeriv n (f - fun y : ℝ => (ν : ℝ) * y) x = iteratedDeriv n f x
  rw [iteratedDeriv_sub hf.contDiffAt hlin.contDiffAt]
  have hlinear :
      iteratedDeriv n (fun y : ℝ => (ν : ℝ) * y) x =
        (ν : ℝ) * iteratedDeriv n id x := by
    simpa only [id_eq] using
      (iteratedDeriv_const_mul_field (n := n) (x := x) (ν : ℝ) id)
  rw [hlinear, iteratedDeriv_id]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega]

/-- A nonpositive second derivative makes the first derivative antitone on an interval. -/
theorem deriv_antitoneOn {a b : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h2 : ∀ x ∈ Set.Icc a b, iteratedDeriv 2 f x ≤ 0) :
    AntitoneOn (deriv f) (Set.Icc a b) := by
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hf1.continuous.continuousOn
    (hf1.differentiable one_ne_zero).differentiableOn ?_
  intro x hx
  rw [← GK34.iteratedDeriv_two]
  exact h2 x (interior_subset hx)

/-- If `-f'' ≤ M`, the first derivative drops by at most `M` times the distance. -/
theorem deriv_sub_deriv_le {a b M x y : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hM : ∀ z ∈ Set.Icc a b, -iteratedDeriv 2 f z ≤ M)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x ≤ y) :
    deriv f x - deriv f y ≤ M * (y - x) := by
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hmv := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a b)
    hf1.continuous.continuousOn
    (hf1.differentiable one_ne_zero).differentiableOn
    (C := -M)
    (fun z hz => by
      have hzI : z ∈ Set.Icc a b := interior_subset hz
      rw [← GK34.iteratedDeriv_two]
      linarith [hM z hzI])
    x hx y hy hxy
  linarith

/-- The derivative-drop estimate specialized to the two sides of an interior point. -/
theorem deriv_endpoint_gaps {a b M x : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hM : ∀ z ∈ Set.Icc a b, -iteratedDeriv 2 f z ≤ M) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) :
    deriv f a - deriv f x ≤ M * (x - a) ∧
      deriv f x - deriv f b ≤ M * (b - x) := by
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  exact ⟨deriv_sub_deriv_le hf hM haI hx hx.1,
    deriv_sub_deriv_le hf hM hx hbI hx.2⟩

/-- Padding the stationary interval by two frequencies on each side gives three exact pieces. -/
theorem Icc_expand_two {A B : ℤ} (hAB : A ≤ B + 1) :
    Finset.Icc (A - 2) (B + 2) =
      Finset.Icc (A - 2) (A - 1) ∪
        (Finset.Icc A B ∪ Finset.Icc (B + 1) (B + 2)) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_union]
  omega

/-- The left padding interval is disjoint from the stationary interval. -/
theorem disjoint_left_middle (A B : ℤ) :
    Disjoint (Finset.Icc (A - 2) (A - 1)) (Finset.Icc A B) := by
  rw [Finset.disjoint_left]
  intro x hxL hxM
  simp only [Finset.mem_Icc] at hxL hxM
  omega

/-- The stationary interval is disjoint from the right padding interval. -/
theorem disjoint_middle_right (A B : ℤ) :
    Disjoint (Finset.Icc A B) (Finset.Icc (B + 1) (B + 2)) := by
  rw [Finset.disjoint_left]
  intro x hxM hxR
  simp only [Finset.mem_Icc] at hxM hxR
  omega

/-- Under the one-past condition, the two padding intervals are disjoint. -/
theorem disjoint_left_right {A B : ℤ} (hAB : A ≤ B + 1) :
    Disjoint (Finset.Icc (A - 2) (A - 1)) (Finset.Icc (B + 1) (B + 2)) := by
  rw [Finset.disjoint_left]
  intro x hxL hxR
  simp only [Finset.mem_Icc] at hxL hxR
  omega

/-- Sum form of `Icc_expand_two`, including an empty stationary interval. -/
theorem sum_Icc_expand_two {R : Type*} [AddCommMonoid R] (F : ℤ → R) {A B : ℤ}
    (hAB : A ≤ B + 1) :
    ∑ ν ∈ Finset.Icc (A - 2) (B + 2), F ν =
      (∑ ν ∈ Finset.Icc (A - 2) (A - 1), F ν) +
        ((∑ ν ∈ Finset.Icc A B, F ν) +
          ∑ ν ∈ Finset.Icc (B + 1) (B + 2), F ν) := by
  rw [Icc_expand_two hAB]
  have hLM := disjoint_left_middle A B
  have hLR := disjoint_left_right hAB
  have hMR := disjoint_middle_right A B
  have hL_MR : Disjoint (Finset.Icc (A - 2) (A - 1))
      (Finset.Icc A B ∪ Finset.Icc (B + 1) (B + 2)) :=
    Finset.disjoint_union_right.mpr ⟨hLM, hLR⟩
  rw [Finset.sum_union hL_MR, Finset.sum_union hMR]

/-- The stationary integer interval has at most derivative span plus one elements. -/
theorem card_Icc_ceil_floor_le {α β : ℝ} (hαβ : α ≤ β) :
    ((Finset.Icc ⌈α⌉ ⌊β⌋).card : ℝ) ≤ β - α + 1 := by
  have hAB : ⌈α⌉ ≤ ⌊β⌋ + 1 :=
    (Int.ceil_le_ceil hαβ).trans (Int.ceil_le_floor_add_one β)
  calc
    ((Finset.Icc ⌈α⌉ ⌊β⌋).card : ℝ) = ((⌊β⌋ + 1 - ⌈α⌉ : ℤ) : ℝ) := by
      exact_mod_cast (Int.card_Icc_of_le ⌈α⌉ ⌊β⌋ hAB)
    _ = (⌊β⌋ : ℝ) + 1 - (⌈α⌉ : ℝ) := by push_cast; ring
    _ ≤ β - α + 1 := by linarith [Int.floor_le β, Int.le_ceil α]

end GK36

end LeanProofs.IntegerPoints
