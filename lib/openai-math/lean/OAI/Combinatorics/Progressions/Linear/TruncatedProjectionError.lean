/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.DenseProductApproximation

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_sum {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (f : J → X → ℂ) :
    p.complexMean (fun x => ∑ j, f j x) = ∑ j, p.complexMean (f j) := by
  simp only [complexMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem norm_weighted_complexMean_sub_le_mean_norm {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (w f g : X → ℂ) {ρ : ℝ}
    (he : ∀ x, p.weight x ≠ 0 → ‖f x - g x‖ ≤ ρ) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤
      ρ * p.mean (fun x => ‖w x‖) := by
  apply (p.norm_complexMean_sub_le _ _ (fun x => ρ * ‖w x‖) ?_).trans_eq
    (p.mean_const_mul ρ _)
  intro x hx
  rw [← mul_sub, norm_mul, mul_comm ρ]
  exact mul_le_mul_of_nonneg_left (he x hx) (norm_nonneg _)

theorem complexMean_weighted_expansion {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ) :
    p.complexMean (fun x => w x * ∑ j, c j * u j x) =
      ∑ j, c j * p.complexMean (fun x => w x * u j x) := by
  simp only [Finset.mul_sum]
  rw [p.complexMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← p.complexMean_mul_left]
  congr 1
  funext x
  ring

theorem weighted_expansion_discard_error {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * u j x)‖ ≤ τ) :
    ‖p.complexMean (fun x => w x * ∑ j, c j * u j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  have he : (fun x => w x * ∑ j, if keep j then c j * u j x else 0) =
      (fun x => w x * ∑ j, (if keep j then c j else 0) * u j x) := by
    funext x
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : keep j <;> simp [hj]
  rw [he, p.complexMean_weighted_expansion, p.complexMean_weighted_expansion,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, ‖c j‖ * τ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : keep j
      · simp only [hj, ite_true, sub_self, norm_zero]
        exact mul_nonneg (norm_nonneg _) hτ
      · simp only [hj, ite_false, zero_mul, sub_zero, norm_mul]
        exact mul_le_mul_of_nonneg_left (hdiscard j hj) (norm_nonneg _)
    _ = (∑ j, ‖c j‖) * τ := (Finset.sum_mul _ _ _).symm
    _ ≤ C * τ := mul_le_mul_of_nonneg_right hc hτ

theorem weighted_projection_tested_error {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (w f projected : X → ℂ)
    (c : J → ℂ) (u : J → X → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B C ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hw : p.mean (fun x => ‖w x‖) ≤ B) (hc : (∑ j, ‖c j‖) ≤ C)
    (hfull : ∀ x, p.weight x ≠ 0 → ‖f x - ∑ j, c j * u j x‖ ≤ ρ)
    (hprojected : ∀ x, p.weight x ≠ 0 → ‖(∑ j, if keep j then c j * u j x else 0) - projected x‖ ≤ ρ)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * u j x)‖ ≤ τ) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * projected x)‖ ≤
      2 * B * ρ + C * τ := by
  have hfirst := (p.norm_weighted_complexMean_sub_le_mean_norm w f (fun x => ∑ j, c j * u j x) hfull).trans
    (mul_le_mul_of_nonneg_left hw hρ)
  have hlast := (p.norm_weighted_complexMean_sub_le_mean_norm w
    (fun x => ∑ j, if keep j then c j * u j x else 0) projected hprojected).trans
      (mul_le_mul_of_nonneg_left hw hρ)
  have hmid := p.weighted_expansion_discard_error w c u keep hc hτ hdiscard
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * f x))
    (p.complexMean (fun x => w x * ∑ j, c j * u j x))
    (p.complexMean (fun x => w x * projected x))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * ∑ j, c j * u j x))
    (p.complexMean (fun x => w x * ∑ j, if keep j then c j * u j x else 0))
    (p.complexMean (fun x => w x * projected x))
  linarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

noncomputable def projectionApproxTolerance (W δ : ℝ) : ℝ := min 1 (δ / (2 * (W + 1)))

noncomputable def projectionModeTolerance (C δ : ℝ) : ℝ := δ / (2 * (C + 1))

theorem projectionErrorBudget_spec {W C δ : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) (hδ : 0 < δ) :
    0 < projectionApproxTolerance W δ ∧ projectionApproxTolerance W δ ≤ 1 ∧
      0 < projectionModeTolerance C δ ∧
      W * projectionApproxTolerance W δ + C * projectionModeTolerance C δ ≤ δ := by
  have hWp : 0 < 2 * (W + 1) := by positivity
  have hCp : 0 < 2 * (C + 1) := by positivity
  have hρ : 0 < projectionApproxTolerance W δ := lt_min (by norm_num) (div_pos hδ hWp)
  have hρ1 : projectionApproxTolerance W δ ≤ 1 := min_le_left _ _
  have hρδ : projectionApproxTolerance W δ * (2 * (W + 1)) ≤ δ :=
    (le_div_iff₀ hWp).mp (min_le_right _ _)
  have hτ : 0 < projectionModeTolerance C δ := div_pos hδ hCp
  have hτδ : projectionModeTolerance C δ * (2 * (C + 1)) = δ := by
    unfold projectionModeTolerance
    exact div_mul_cancel₀ _ hCp.ne'
  refine ⟨hρ, hρ1, hτ, ?_⟩
  nlinarith

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem weighted_projection_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (w f F G g : X → ℂ) {B η ε : ℝ}
    (hη : 0 ≤ η) (hw : p.mean (fun x => ‖w x‖) ≤ B)
    (hF : ∀ x, p.weight x ≠ 0 → ‖f x - F x‖ ≤ η)
    (hG : ∀ x, p.weight x ≠ 0 → ‖G x - g x‖ ≤ η)
    (hprojection : ‖p.complexMean (fun x => w x * F x) -
      p.complexMean (fun x => w x * G x)‖ ≤ ε) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤
      2 * B * η + ε := by
  have hfirst := (p.norm_weighted_complexMean_sub_le_mean_norm w f F hF).trans
    (mul_le_mul_of_nonneg_left hw hη)
  have hlast := (p.norm_weighted_complexMean_sub_le_mean_norm w G g hG).trans
    (mul_le_mul_of_nonneg_left hw hη)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * f x)) (p.complexMean (fun x => w x * F x))
    (p.complexMean (fun x => w x * g x))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * F x)) (p.complexMean (fun x => w x * G x))
    (p.complexMean (fun x => w x * g x))
  linarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteAverageMap {H X : Type*} [Fintype H]
    (p : FiniteProbabilityWeights H) (T : H → X → X) (f : X → ℂ) (x : X) : ℂ :=
  p.complexMean (fun h => f (T h x))

theorem finiteAverageMap_sub_norm_le {H X : Type*} [Fintype H]
    (p : FiniteProbabilityWeights H) (T : H → X → X) (f g : X → ℂ) {ρ : ℝ}
    (he : ∀ x, ‖f x - g x‖ ≤ ρ) (x : X) :
    ‖finiteAverageMap p T f x - finiteAverageMap p T g x‖ ≤ ρ := by
  exact (p.norm_complexMean_sub_le _ _ (fun _ => ρ) (fun h _ => he (T h x))).trans_eq (p.mean_const ρ)

theorem finiteAverageMap_ofReal {H X : Type*} [Fintype H]
    (p : FiniteProbabilityWeights H) (T : H → X → X) (f : X → ℝ) (x : X) :
    finiteAverageMap p T (fun y => (f y : ℂ)) x = (p.mean (fun h => f (T h x)) : ℂ) :=
  p.complexMean_ofReal _

theorem finiteAverageMap_real_unit_interval {H X : Type*} [Fintype H]
    (p : FiniteProbabilityWeights H) (T : H → X → X) (f : X → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : X) :
    (finiteAverageMap p T (fun y => (f y : ℂ)) x).im = 0 ∧
      (finiteAverageMap p T (fun y => (f y : ℂ)) x).re ∈ Set.Icc (0 : ℝ) 1 := by
  rw [finiteAverageMap_ofReal]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, Set.mem_Icc]
  exact ⟨p.mean_nonneg (fun h => (hf (T h x)).1),
    (p.mean_mono (fun h => (hf (T h x)).2)).trans_eq (p.mean_const 1)⟩

theorem finiteAverageMap_expansion {H X J : Type*} [Fintype H] [Fintype J]
    (p : FiniteProbabilityWeights H) (T : H → X → X) (c : J → ℂ) (u : J → X → ℂ)
    (χ : J → H → ℂ) (keep : J → Prop) [DecidablePred keep]
    (heigen : ∀ j h x, u j (T h x) = χ j h * u j x)
    (hχ : ∀ j, p.complexMean (χ j) = if keep j then 1 else 0) (x : X) :
    finiteAverageMap p T (fun y => ∑ j, c j * u j y) x =
      ∑ j, if keep j then c j * u j x else 0 := by
  unfold finiteAverageMap
  rw [p.complexMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun h => c j * u j (T h x)) = (fun h => (c j * u j x) * χ j h) := by
    funext h
    rw [heigen]
    ring
  rw [he, p.complexMean_mul_left, hχ]
  by_cases hj : keep j <;> simp [hj]

theorem finiteAverageMap_tested_error {H X G J : Type*} [Fintype H] [Fintype G] [Fintype J]
    (p : FiniteProbabilityWeights G) (q : FiniteProbabilityWeights H) (T : H → X → X)
    (f : X → ℂ) (path : G → X) (w : G → ℂ) (c : J → ℂ) (u : J → X → ℂ)
    (χ : J → H → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B C ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hw : p.mean (fun x => ‖w x‖) ≤ B) (hc : (∑ j, ‖c j‖) ≤ C)
    (happrox : ∀ x, ‖f x - ∑ j, c j * u j x‖ ≤ ρ)
    (heigen : ∀ j h x, u j (T h x) = χ j h * u j x)
    (hχ : ∀ j, q.complexMean (χ j) = if keep j then 1 else 0)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * u j (path x))‖ ≤ τ) :
    ‖p.complexMean (fun x => w x * f (path x)) -
      p.complexMean (fun x => w x * finiteAverageMap q T f (path x))‖ ≤ 2 * B * ρ + C * τ := by
  apply p.weighted_projection_tested_error w (fun x => f (path x))
    (fun x => finiteAverageMap q T f (path x)) c (fun j x => u j (path x)) keep hρ hτ hw hc
    (fun x _ => happrox (path x)) _ hdiscard
  intro x _
  rw [← finiteAverageMap_expansion q T c u χ keep heigen hχ (path x), norm_sub_rev]
  exact finiteAverageMap_sub_norm_le q T f (fun y => ∑ j, c j * u j y) happrox (path x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_complexMean_addChar {H : Type*} [AddGroup H] [Fintype H] (χ : AddChar H ℂ) :
    (FiniteProbabilityWeights.uniform H).complexMean χ = if χ = 1 then 1 else 0 := by
  rw [FiniteProbabilityWeights.uniform_complexMean, Fintype.expect_eq_sum_div_card]
  by_cases hχ : χ = 1
  · simp only [hχ, ite_true, AddChar.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card H : ℂ) ≠ 0)
  · rw [ite_eq_right hχ, AddChar.sum_eq_zero_of_ne_one hχ, zero_div]

noncomputable def finiteCosetAverage {H X : Type*} [AddCommGroup H] [Fintype H] [AddCommGroup X]
    (ι : H →+ X) (f : X → ℂ) : X → ℂ :=
  finiteAverageMap (FiniteProbabilityWeights.uniform H) (fun h x => x + ι h) f

theorem finiteCosetAverage_invariant {H X : Type*} [AddCommGroup H] [Fintype H] [AddCommGroup X]
    (ι : H →+ X) (f : X → ℂ) (h₀ : H) (x : X) :
    finiteCosetAverage ι f (x + ι h₀) = finiteCosetAverage ι f x := by
  unfold finiteCosetAverage finiteAverageMap
  rw [FiniteProbabilityWeights.uniform_complexMean, FiniteProbabilityWeights.uniform_complexMean]
  apply Fintype.expect_equiv (Equiv.addLeft h₀)
  intro h
  change f ((x + ι h₀) + ι h) = f (x + ι (h₀ + h))
  rw [map_add, add_assoc]

theorem finiteCosetAverage_idempotent {H X : Type*} [AddCommGroup H] [Fintype H] [AddCommGroup X]
    (ι : H →+ X) (f : X → ℂ) (x : X) :
    finiteCosetAverage ι (finiteCosetAverage ι f) x = finiteCosetAverage ι f x := by
  change (FiniteProbabilityWeights.uniform H).complexMean
    (fun h => finiteCosetAverage ι f (x + ι h)) = _
  simp_rw [finiteCosetAverage_invariant]
  exact (FiniteProbabilityWeights.uniform H).complexMean_const _

theorem finiteCosetAverage_character {H X : Type*} [AddCommGroup H] [Fintype H] [AddCommGroup X]
    (ι : H →+ X) (χ : AddChar X ℂ) (x : X) :
    finiteCosetAverage ι χ x = if χ.compAddMonoidHom ι = 1 then χ x else 0 := by
  change (FiniteProbabilityWeights.uniform H).complexMean (fun h => χ (x + ι h)) = _
  simp only [AddChar.map_add_eq_mul]
  rw [FiniteProbabilityWeights.complexMean_mul_left]
  change χ x * (FiniteProbabilityWeights.uniform H).complexMean (χ.compAddMonoidHom ι) = _
  rw [uniform_complexMean_addChar]
  split_ifs <;> simp

theorem finiteCosetAverage_expansion {H X J : Type*}
    [AddCommGroup H] [Fintype H] [AddCommGroup X] [Fintype J]
    (ι : H →+ X) (c : J → ℂ) (χ : J → AddChar X ℂ) (x : X) :
    finiteCosetAverage ι (fun y => ∑ j, c j * χ j y) x =
      ∑ j, if (χ j).compAddMonoidHom ι = 1 then c j * χ j x else 0 := by
  apply finiteAverageMap_expansion (FiniteProbabilityWeights.uniform H)
    (fun h x => x + ι h) c (fun j x => χ j x)
    (fun j h => χ j (ι h)) (fun j => (χ j).compAddMonoidHom ι = 1) _ _ x
  · intro j h y
    rw [AddChar.map_add_eq_mul, mul_comm]
  · intro j
    exact uniform_complexMean_addChar ((χ j).compAddMonoidHom ι)

theorem finiteCosetAverage_tested_error {H X G J : Type*}
    [AddCommGroup H] [Fintype H] [AddCommGroup X] [Fintype G] [Fintype J]
    (p : FiniteProbabilityWeights G) (ι : H →+ X) (f : X → ℂ) (path : G → X)
    (w : G → ℂ) (c : J → ℂ) (χ : J → AddChar X ℂ) {B C ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (hw : p.mean (fun x => ‖w x‖) ≤ B)
    (hc : (∑ j, ‖c j‖) ≤ C) (happrox : ∀ x, ‖f x - ∑ j, c j * χ j x‖ ≤ ρ)
    (hdiscard : ∀ j, (χ j).compAddMonoidHom ι ≠ 1 →
      ‖p.complexMean (fun x => w x * χ j (path x))‖ ≤ τ) :
    ‖p.complexMean (fun x => w x * f (path x)) -
      p.complexMean (fun x => w x * finiteCosetAverage ι f (path x))‖ ≤ 2 * B * ρ + C * τ := by
  apply finiteAverageMap_tested_error p (FiniteProbabilityWeights.uniform H) (fun h x => x + ι h)
    f path w c (fun j x => χ j x) (fun j h => χ j (ι h))
    (fun j => (χ j).compAddMonoidHom ι = 1) hρ hτ hw hc happrox _ _ hdiscard
  · intro j h x
    rw [AddChar.map_add_eq_mul, mul_comm]
  · intro j
    exact uniform_complexMean_addChar ((χ j).compAddMonoidHom ι)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def finiteKernelAverage {X Y : Type*} [AddCommGroup X] [Fintype X] [AddCommGroup Y]
    (E : X →+ Y) (f : X → ℂ) : X → ℂ := finiteCosetAverage E.ker.subtype f

theorem finiteKernelAverage_eq_of_map_eq {X Y : Type*}
    [AddCommGroup X] [Fintype X] [AddCommGroup Y]
    (E : X →+ Y) (f : X → ℂ) (x y : X) (hxy : E x = E y) :
    finiteKernelAverage E f x = finiteKernelAverage E f y := by
  have hz : y - x ∈ E.ker := by
    change E (y - x) = 0
    rw [map_sub, hxy, sub_self]
  have h := finiteCosetAverage_invariant E.ker.subtype f ⟨y - x, hz⟩ x
  change finiteKernelAverage E f (x + (y - x)) = finiteKernelAverage E f x at h
  have he : x + (y - x) = y := by abel
  rw [he] at h
  exact h.symm

theorem finiteKernelAverage_factors {X Y : Type*}
    [AddCommGroup X] [Fintype X] [AddCommGroup Y] (E : X →+ Y) (f : X → ℂ) :
    ∃ g : Set.range E → ℂ, ∀ x,
      finiteKernelAverage E f x = g ⟨E x, x, rfl⟩ := by
  refine ⟨fun y => finiteKernelAverage E f (Classical.choose y.property), ?_⟩
  intro x
  apply finiteKernelAverage_eq_of_map_eq E f
  exact (Classical.choose_spec (show E x ∈ Set.range E from ⟨x, rfl⟩)).symm

theorem character_trivial_on_kernel_iff {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (E : X →+ Y) (χ : AddChar X ℂ) :
    χ.compAddMonoidHom E.ker.subtype = 1 ↔ ∀ x, E x = 0 → χ x = 1 := by
  rw [AddChar.eq_one_iff]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x.val x.property

theorem finiteKernelAverage_character {X Y : Type*}
    [AddCommGroup X] [Fintype X] [AddCommGroup Y] (E : X →+ Y) (χ : AddChar X ℂ) (x : X) :
    finiteKernelAverage E χ x = if ∀ y, E y = 0 → χ y = 1 then χ x else 0 := by
  simp only [finiteKernelAverage, finiteCosetAverage_character, character_trivial_on_kernel_iff]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem FiniteProbabilityWeights.weighted_projection_truncation_error {X J : Type*}
    [Fintype X] [Fintype J] (p : FiniteProbabilityWeights X)
    (w f : X → ℂ) (c : J → ℂ) (u : J → X → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B C ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hw : p.mean (fun x => ‖w x‖) ≤ B) (hc : (∑ j, ‖c j‖) ≤ C)
    (happrox : ∀ x, p.weight x ≠ 0 → ‖f x - ∑ j, c j * u j x‖ ≤ ρ)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * u j x)‖ ≤ τ) :
    ‖p.complexMean (fun x => w x * f x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ B * ρ + C * τ := by
  have hfirst := (p.norm_weighted_complexMean_sub_le_mean_norm w f (fun x => ∑ j, c j * u j x) happrox).trans
    (mul_le_mul_of_nonneg_left hw hρ)
  have hmid := p.weighted_expansion_discard_error w c u keep hc hτ hdiscard
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * f x))
    (p.complexMean (fun x => w x * ∑ j, c j * u j x))
    (p.complexMean (fun x => w x * ∑ j, if keep j then c j * u j x else 0))
  linarith

theorem finiteCosetAverage_truncation_tested_error {H X G J : Type*}
    [AddCommGroup H] [Fintype H] [AddCommGroup X] [Fintype G] [Fintype J]
    (p : FiniteProbabilityWeights G) (ι : H →+ X) (f : G → ℂ) (path : G → X)
    (w : G → ℂ) (c : J → ℂ) (χ : J → AddChar X ℂ) {B C ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (hw : p.mean (fun x => ‖w x‖) ≤ B)
    (hc : (∑ j, ‖c j‖) ≤ C)
    (happrox : ∀ x, p.weight x ≠ 0 → ‖f x - ∑ j, c j * χ j (path x)‖ ≤ ρ)
    (hdiscard : ∀ j, (χ j).compAddMonoidHom ι ≠ 1 →
      ‖p.complexMean (fun x => w x * χ j (path x))‖ ≤ τ) :
    ‖p.complexMean (fun x => w x * f x) -
      p.complexMean (fun x => w x * finiteCosetAverage ι (fun y => ∑ j, c j * χ j y) (path x))‖ ≤
        B * ρ + C * τ := by
  simp_rw [finiteCosetAverage_expansion]
  exact p.weighted_projection_truncation_error w f c (fun j x => χ j (path x))
    (fun j => (χ j).compAddMonoidHom ι = 1) hρ hτ hw hc happrox hdiscard

end Erdos3

end

end OAI
