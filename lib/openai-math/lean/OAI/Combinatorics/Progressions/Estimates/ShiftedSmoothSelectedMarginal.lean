/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
import OAI.Combinatorics.Progressions.Probability.ShiftedSmoothLawBounds
import OAI.Combinatorics.Progressions.Probability.ShiftedSmoothProductLaw
import OAI.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_finite_sum {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (y : Y) :
    (p.map F y).toReal = ∑ x ∈ S, (p x).toReal * (if F x = y then 1 else 0) := by
  rw [pmf_map_toReal_indicator]
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq

theorem pmf_image_finite_expectation {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T) (φ : Y → ℂ) :
    (∑' x, ((p x).toReal : ℂ) * φ (F x)) =
      ∑ y ∈ T, ((p.map F y).toReal : ℂ) * φ y := by
  have hs : (∑' x, ((p x).toReal : ℂ) * φ (F x)) =
      ∑ x ∈ S, ((p x).toReal : ℂ) * φ (F x) :=
    (hasSum_sum_of_ne_finset_zero (fun x hx => by
      rw [hp x hx, Complex.ofReal_zero, zero_mul])).tsum_eq
  rw [hs]
  simp_rw [pmf_map_finite_sum p S hp F, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (F x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact (hn (hT x hx)).elim

theorem pmf_image_finite_test_error {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T)
    (ψ φ : Y → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ y ∈ T, ‖((A * (p.map F y).toReal : ℝ) : ℂ) - ψ y‖ ≤ E) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (F x)) -
      ∑ y ∈ T, (ψ y / (A : ℂ)) * φ y‖ ≤
        (E / A) * ∑ y ∈ T, ‖φ y‖ := by
  rw [pmf_image_finite_expectation p S hp F T hT φ, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ y ∈ T, (E / A) * ‖φ y‖ := by
      apply Finset.sum_le_sum
      intro y hy
      have hid : ((p.map F y).toReal : ℂ) - ψ y / (A : ℂ) =
          (((A * (p.map F y).toReal : ℝ) : ℂ) - ψ y) / (A : ℂ) := by
        rw [Complex.ofReal_mul, sub_div, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hA.ne')]
      rw [← sub_mul, norm_mul, hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (he y hy) hA.le) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_image_finite_real_mean {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T) (φ : Y → ℝ) :
    (∑' x, (p x).toReal * φ (F x)) = ∑ y ∈ T, (p.map F y).toReal * φ y := by
  have hs : (∑' x, (p x).toReal * φ (F x)) = ∑ x ∈ S, (p x).toReal * φ (F x) :=
    (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq
  rw [hs]
  simp_rw [pmf_map_finite_sum p S hp F, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (F x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact (hn (hT x hx)).elim

theorem pmf_image_energy_of_point_cap {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (e : Y → ℝ) (he : ∀ y ∉ T, e y = 0)
    {C : ℝ} (hcap : ∀ y, (p.map F y).toReal ≤ C) :
    (∑' x, (p x).toReal * e (F x) ^ 2) ≤ C * ∑ y ∈ T, e y ^ 2 := by
  let U := T ∪ S.image F
  have hU : ∀ x ∈ S, F x ∈ U := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hsum : (∑ y ∈ U, e y ^ 2) = ∑ y ∈ T, e y ^ 2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro y _ hy
    rw [he y hy, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [pmf_image_finite_real_mean p S hp F U hU (fun y => e y ^ 2)]
  calc
    _ ≤ ∑ y ∈ U, C * e y ^ 2 :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hcap y) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, hsum]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_add_right {Y : Type*} [AddGroup Y] (p : PMF Y) (s y : Y) :
    p.map (fun v => v + s) y = p (y - s) := by
  have h := pmf_map_injective_at p (fun v => v + s) (fun _ _ h => add_right_cancel h) (y-s)
  simpa only [sub_add_cancel] using h

theorem pmf_map_image_add_right {X Y : Type*} [AddGroup Y]
    (p : PMF X) (F : X → Y) (s y : Y) :
    p.map (fun x => F x + s) y = p.map F (y-s) := by
  rw [show (fun x => F x + s) = (fun v => v+s) ∘ F from rfl, ← PMF.map_comp]
  exact pmf_map_add_right (p.map F) s y

theorem pmf_image_shifted_finite_expectation {X Y : Type*} [AddGroup Y] [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (s : Y) (T : Finset Y) (hT : ∀ x ∈ S, F x + s ∈ T) (φ : Y → ℂ) :
    (∑' x, ((p x).toReal : ℂ) * φ (F x + s)) =
      ∑ y ∈ T, ((p.map F (y-s)).toReal : ℂ) * φ y := by
  simpa only [pmf_map_image_add_right] using
    pmf_image_finite_expectation p S hp (fun x => F x+s) T hT φ

theorem pmf_image_shifted_finite_test_error {X Y : Type*} [AddGroup Y] [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (s : Y) (T : Finset Y) (hT : ∀ x ∈ S, F x + s ∈ T)
    (ψ φ : Y → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ y ∈ T, ‖((A * (p.map F (y-s)).toReal : ℝ) : ℂ) - ψ y‖ ≤ E) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (F x+s)) -
      ∑ y ∈ T, (ψ y / (A : ℂ)) * φ y‖ ≤ (E/A) * ∑ y ∈ T, ‖φ y‖ := by
  apply pmf_image_finite_test_error p S hp (fun x => F x+s) T hT ψ φ hA
  simpa only [pmf_map_image_add_right] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductMass_coordinate_pos {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) (i : I) :
    0 < shiftedSmoothSampleSum (a i) (S i) := by
  have hp : (∏ j, shiftedSmoothSampleSum (a j) (S j)) ≠ 0 := by
    rw [← shiftedSmoothProductMass_eq_prod a S hS]
    exact hZ.ne'
  have hn := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have h0 : 0 ≤ shiftedSmoothSampleSum (a i) (S i) :=
    tsum_nonneg (fun k => (smoothProbabilityProfile_range _).1)
  exact lt_of_le_of_ne h0 hn.symm

theorem shiftedSmoothProductPMF_eq_independent {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    shiftedSmoothProductPMF a S hS hZ = independentProductPMF
      (fun i => shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
        (shiftedSmoothProductMass_coordinate_pos a S hS hZ i)) := by
  ext x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [shiftedSmoothProductPMF_toReal, independentProductPMF_toReal]
  simp_rw [shiftedSmoothCoefficientPMF_apply]
  rw [Finset.prod_div_distrib, ← shiftedSmoothProductMass_eq_prod a S hS]
  rfl

theorem shiftedSmoothProductPMF_base_cap {K I Y : Type*} [Fintype K] [Fintype I]
    (a S : Option K × I → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (Option K × I → ℤ) → Y)
    (hf : ∀ tail, Function.Injective (fun base => f (baseArrayJoin tail base)))
    (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ S (none,i)) (y : Y) :
    ((shiftedSmoothProductPMF a S hS hZ).map f y).toReal ≤ ∏ i, 2 / S (none,i) := by
  rw [shiftedSmoothProductPMF_eq_independent]
  apply independentProductPMF_base_cap _ f hf (fun i => 2 / S (none,i))
    (fun i => div_nonneg (by norm_num) (hS (none,i)).le)
  intro i k
  exact shiftedSmoothCoefficientPMF_le (a (none,i)) (hbase i) k

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem smoothProbabilityProfile_inner_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ smoothProbabilityProfile x := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have hi := probabilityProfileBump.integral_le_measure_closedBall volume
  norm_num [probabilityProfileBump] at hi
  change (∫ y, probabilityProfileBump y) ≤ 3 / 2 at hi
  change (1 / 2 : ℝ) ≤ probabilityProfileBump x / ∫ y, probabilityProfileBump y
  rw [hx']
  apply (le_div_iff₀ probabilityProfileBump.integral_pos).mpr
  linarith

theorem shiftedSmoothCoefficientPMF_inner_lower (a : ℝ) {S : ℝ}
    (hscale : 8 * (probabilityProfileLipschitz : ℝ) ≤ S)
    (hS : 0 < S) (hZ : 0 < shiftedSmoothSampleSum a S) (k : ℤ)
    (hk : |(k : ℝ) - a| ≤ S / 2) :
    1 / (3 * S) ≤ (shiftedSmoothCoefficientPMF a S hS hZ k).toReal := by
  have hk' : |((k : ℝ) - a) / S| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hS]
    exact (div_le_iff₀ hS).mpr (by linarith)
  rw [shiftedSmoothCoefficientPMF_apply]
  have hp := smoothProbabilityProfile_inner_lower _ hk'
  have hb := (shiftedSmoothSampleSum_bounds a hscale).2
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * S) hZ).mpr
  nlinarith

theorem shiftedSmoothProductPMF_inner_lower {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    (∏ i, 1 / (3 * S i)) ≤ (shiftedSmoothProductPMF a S hS hZ z).toReal := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_toReal]
  apply Finset.prod_le_prod₀
  · intro i _
    exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (hS i).le)
  · intro i _
    exact shiftedSmoothCoefficientPMF_inner_lower (a i) (hscale i) (hS i)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ i) (z i) (hz i)

theorem shiftedSmoothProductPMF_inner_mass {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (z : I → ℤ) (hz : ∀ i, |(z i : ℝ) - a i| ≤ S i / 2) :
    1 ≤ (∏ i, 3 * S i) * (shiftedSmoothProductPMF a S hS hZ z).toReal := by
  have hprod : 0 < ∏ i, 3 * S i :=
    Finset.prod_pos (fun i _ => mul_pos (by norm_num) (hS i))
  have h := shiftedSmoothProductPMF_inner_lower a S hS hZ hscale z hz
  rw [Finset.prod_div_distrib] at h
  simp only [Finset.prod_const_one] at h
  exact (div_le_iff₀ hprod).mp h |>.trans_eq (mul_comm _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductPMF_eq_independent {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    smoothProductPMF S hS = independentProductPMF (fun i => smoothCoefficientPMF (S i) (hS i)) := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothProductPMF_apply, independentProductPMF_toReal]

theorem smoothProductPMF_rows {J I : Type*} [Fintype J] [Fintype I]
    (S : J × I → ℝ) (hS : ∀ i, 0 < S i) :
    (smoothProductPMF S hS).map independentArrayRows =
      independentProductPMF (fun i => smoothProductPMF (fun j => S (j, i)) (fun j => hS (j, i))) := by
  simp only [smoothProductPMF_eq_independent]
  exact independentProductPMF_rows _

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem shiftedSmoothProductMass_restrict_pos {A J : Type*} [Fintype A] [Fintype J]
    (e : A → J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    0 < shiftedSmoothProductMass (fun i => a (e i)) (fun i => S (e i)) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (fun i => hS (e i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothProductMass_coordinate_pos a S hS hZ (e i))

theorem shiftedSmoothProductPMF_selected_factorization
    {A J : Type*} [Fintype A] [Fintype J]
    (e : A ↪ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    shiftedSmoothProductPMF a S hS hZ =
      (shiftedSmoothProductPMF
        (fun k : SelectedCoefficientComplement e => a k.val)
        (fun k : SelectedCoefficientComplement e => S k.val)
        (fun k => hS k.val)
        (shiftedSmoothProductMass_restrict_pos Subtype.val a S hS hZ)).bind
      (fun tail =>
        (shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
          (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ)).map
          (selectedCoefficientJoin e (0 : ℤ) tail)) := by
  simp only [shiftedSmoothProductPMF_eq_independent]
  rw [Subsingleton.elim (unselectedColumnFintype e)
    (Subtype.fintype (fun j => j ∉ Set.range e))]
  exact independentProductPMF_selected_split e (0 : ℤ)
    (fun j => shiftedSmoothCoefficientPMF (a j) (S j) (hS j)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def smoothInputSplit {I J D X : Type*} (e : (I ⊕ J) ≃ D) (z : D → X) :
    (I → X) × (J → X) := (fun i => z (e (.inl i)), fun j => z (e (.inr j)))

def smoothInputJoin {I J D X : Type*} (e : (I ⊕ J) ≃ D) (p : (I → X) × (J → X)) : D → X :=
  fun d => Sum.elim p.1 p.2 (e.symm d)

theorem smoothInputSplit_join {I J D X : Type*} (e : (I ⊕ J) ≃ D) (p : (I → X) × (J → X)) :
    smoothInputSplit e (smoothInputJoin e p) = p := by
  ext <;> simp [smoothInputSplit, smoothInputJoin]

theorem smoothInputJoin_split {I J D X : Type*} (e : (I ⊕ J) ≃ D) (z : D → X) :
    smoothInputJoin e (smoothInputSplit e z) = z := by
  funext d
  obtain ⟨c, rfl⟩ := e.surjective d
  cases c <;> simp [smoothInputSplit, smoothInputJoin]

theorem smoothInputSplit_injective {I J D X : Type*} (e : (I ⊕ J) ≃ D) :
    Function.Injective (smoothInputSplit (X := X) e) := by
  intro x y h
  have h' := congrArg (smoothInputJoin e) h
  simpa only [smoothInputJoin_split] using h'

theorem smoothInputSplit_law {I J D : Type*} [Fintype I] [Fintype J] [Fintype D]
    (e : (I ⊕ J) ≃ D) (S : D → ℝ) (hS : ∀ d, 0 < S d)
    (hM : 0 < scaledInputMass (splitSmoothProductProfile J I)
      (fun i => S (e (.inl i))) (fun j => S (e (.inr j)))) :
    (smoothProductPMF S hS).map (smoothInputSplit e) =
      scaledInputPMF (splitSmoothProductProfile J I)
        (fun z => (splitSmoothProductProfile_range J I z).1)
        (fun i => S (e (.inl i))) (fun j => S (e (.inr j)))
        (fun i => hS (e (.inl i))) (fun j => hS (e (.inr j)))
        (splitSmoothProductProfile_zero_outside J I) hM := by
  ext p
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  nth_rw 1 [← smoothInputSplit_join e p]
  rw [pmf_map_injective_at _ _ (smoothInputSplit_injective e),
    scaledInputPMF_splitSmoothProductProfile, smoothProductPMF_apply,
    smoothProductPMF_apply, smoothProductPMF_apply]
  rw [← e.prod_comp]
  simp only [Fintype.prod_sum_type, smoothInputJoin, Equiv.symm_apply_apply, Sum.elim_inl,
    Sum.elim_inr]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_map_finite_expectation {X Y : Type*}
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (φ : Y → ℂ) :
    (∑' y, ((p.map F y).toReal : ℂ) * φ y) =
      ∑' x, ((p x).toReal : ℂ) * φ (F x) := by
  rw [pmf_image_finite_expectation p S hp F (S.image F)
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) φ]
  apply (hasSum_sum_of_ne_finset_zero _).tsum_eq
  intro y hy
  have hz : (p.map F y).toReal = 0 := by
    rw [pmf_map_finite_sum p S hp F]
    apply Finset.sum_eq_zero
    intro x hx
    have hxy : F x ≠ y := fun he => hy (Finset.mem_image.mpr ⟨x, hx, he⟩)
    simp only [hxy, ite_false, mul_zero]
  rw [hz, Complex.ofReal_zero, zero_mul]

theorem shiftedSmoothProductPMF_selected_marginal
    {A J : Type*} [Fintype A] [Fintype J]
    (e : A ↪ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z i => z (e i)) =
      shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ) := by
  simp only [shiftedSmoothProductPMF_eq_independent]
  exact independentProductPMF_marginal _ e e.injective

theorem shiftedSmoothProductPMF_selected_map
    {A J Y : Type*} [Fintype A] [Fintype J]
    (e : A ↪ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (f : (A → ℤ) → Y) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z => f (fun i => z (e i))) =
      (shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ)).map f := by
  rw [← shiftedSmoothProductPMF_selected_marginal e a S hS hZ, PMF.map_comp]
  rfl

theorem shiftedSmoothProductPMF_selected_expectation
    {A J : Type*} [Fintype A] [Fintype J]
    (e : A ↪ J) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (φ : (A → ℤ) → ℂ) :
    (∑' z, ((shiftedSmoothProductPMF a S hS hZ z).toReal : ℂ) *
      φ (fun i => z (e i))) =
      ∑' z, ((shiftedSmoothProductPMF (fun i => a (e i)) (fun i => S (e i))
        (fun i => hS (e i)) (shiftedSmoothProductMass_restrict_pos e a S hS hZ) z).toReal : ℂ) *
          φ z := by
  rw [← shiftedSmoothProductPMF_selected_marginal e a S hS hZ]
  exact (pmf_map_finite_expectation (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (fun z i => z (e i)) φ).symm

end Erdos3

end

end OAI
