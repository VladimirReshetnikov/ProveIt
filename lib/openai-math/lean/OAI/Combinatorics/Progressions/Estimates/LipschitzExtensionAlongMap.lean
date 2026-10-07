/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem exists_real_lipschitz_extension_interval (f : X → ℝ) (S : Set X) (L : ℝ≥0)
    (hf : LipschitzOnWith L f S) (a b : ℝ) (hab : a ≤ b)
    (hbound : ∀ x ∈ S, a ≤ f x ∧ f x ≤ b) :
    ∃ g : X → ℝ, LipschitzWith L g ∧ Set.EqOn f g S ∧ ∀ x, a ≤ g x ∧ g x ≤ b := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  refine ⟨fun x => max a (min b (g x)), (hg.const_min b).const_max a, ?_, ?_⟩
  · intro x hx
    change f x = max a (min b (g x))
    rw [← heq hx, min_eq_right (hbound x hx).2, max_eq_right (hbound x hx).1]
  · intro x
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem exists_complex_bounded_lipschitz_extension (f : X → ℂ) (S : Set X) (L B : ℝ≥0)
    (hf : LipschitzOnWith L f S) (hbound : ∀ x ∈ S, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith (2 * L) g ∧ Set.EqOn f g S ∧ ∀ x, ‖g x‖ ≤ 2 * B := by
  have hre : LipschitzOnWith L (fun x => (f x).re) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |(f x - f y).re| ≤ L * dist x y
    exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy)
  have him : LipschitzOnWith L (fun x => (f x).im) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |(f x - f y).im| ≤ L * dist x y
    exact (Complex.abs_im_le_norm _).trans (by simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy)
  obtain ⟨u, hu, heu, hub⟩ := exists_real_lipschitz_extension_interval (fun x => (f x).re) S L hre
    (-B) B (neg_le_self B.coe_nonneg) (fun x hx => abs_le.mp ((Complex.abs_re_le_norm _).trans (hbound x hx)))
  obtain ⟨v, hv, hev, hvb⟩ := exists_real_lipschitz_extension_interval (fun x => (f x).im) S L him
    (-B) B (neg_le_self B.coe_nonneg) (fun x hx => abs_le.mp ((Complex.abs_im_le_norm _).trans (hbound x hx)))
  let g : X → ℂ := fun x => ⟨u x, v x⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hu' := hu.dist_le_mul x y
    have hv' := hv.dist_le_mul x y
    rw [Real.dist_eq] at hu' hv'
    calc
      dist (g x) (g y) = ‖g x - g y‖ := dist_eq_norm _ _
      _ ≤ |(g x - g y).re| + |(g x - g y).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (L : ℝ) * dist x y + L * dist x y := add_le_add hu' hv'
      _ = ((2 * L : ℝ≥0) : ℝ) * dist x y := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  · intro x hx
    exact Complex.ext (heu hx) (hev hx)
  · intro x
    exact (Complex.norm_le_abs_re_add_abs_im (g x)).trans
      (by have h1 := abs_le.mpr (hub x); have h2 := abs_le.mpr (hvb x); change |u x| + |v x| ≤ _; linarith)

theorem exists_complex_extension_from_subset (S : Set X) (f : S → ℂ) (L B : ℝ≥0)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith (2 * L) g ∧ (∀ x : S, g x = f x) ∧ ∀ x, ‖g x‖ ≤ 2 * B := by
  classical
  let F : X → ℂ := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have hF (x : S) : F x = f x := by simp only [F, dite_eq_left x.property]
  have hLip : LipschitzOnWith L F S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [F, dite_eq_left hx, dite_eq_left hy, Subtype.dist_eq] using hf.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨g, hg, heq, hb⟩ := exists_complex_bounded_lipschitz_extension F S L B hLip
    (fun x hx => (congrArg norm (hF ⟨x, hx⟩)).le.trans (hbound ⟨x, hx⟩))
  exact ⟨g, hg, fun x => (heq x.property).symm.trans (hF x), hb⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem complex_half_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 2) : ‖z / 2‖ ≤ 1 := by
  rw [norm_div]
  norm_num
  linarith

theorem lipschitz_complex_half {X : Type*} [PseudoMetricSpace X]
    (g : X → ℂ) (L : ℝ≥0) (hg : LipschitzWith (2 * L) g) :
    LipschitzWith L (fun x => g x / 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hg.dist_le_mul x y
  rw [dist_eq_norm] at h ⊢
  rw [← sub_div, norm_div]
  have hn : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hn]
  simp only [NNReal.coe_mul, NNReal.coe_ofNat] at h
  linarith

theorem complex_prod_halves {T : Type*} [Fintype T] (g : T → ℂ) :
    (∏ t, g t) = (2 : ℂ) ^ Fintype.card T * ∏ t, g t / 2 := by
  calc
    _ = ∏ t, (2 : ℂ) * (g t / 2) := Finset.prod_congr rfl (fun _ _ => by ring)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_complex_extension_along_map {X Y : Type*} [PseudoMetricSpace Y]
    (f : X → Y) (u : X → ℂ) (K B : ℝ≥0)
    (hdist : ∀ x y, dist (u x) (u y) ≤ K * dist (f x) (f y))
    (hbound : ∀ x, ‖u x‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * K) g ∧ (∀ x, g (f x) = u x) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  classical
  let S := Set.range f
  let pre (y : S) : X := Classical.choose y.property
  have hpre (y : S) : f (pre y) = y.val := Classical.choose_spec y.property
  let v (y : S) : ℂ := u (pre y)
  have hv : LipschitzWith K v := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [v, hpre, Subtype.dist_eq] using hdist (pre x) (pre y)
  have hvx (x : X) : v ⟨f x, ⟨x, rfl⟩⟩ = u x := by
    apply dist_le_zero.mp
    have h := hdist (pre ⟨f x, ⟨x, rfl⟩⟩) x
    simpa only [hpre, dist_self, mul_zero] using h
  obtain ⟨g, hg, hge, hgb⟩ := exists_complex_extension_from_subset S v K B hv (fun y => hbound (pre y))
  exact ⟨g, hg, fun x => (hge ⟨f x, ⟨x, rfl⟩⟩).trans (hvx x), hgb⟩

end Erdos3

end

end OAI
