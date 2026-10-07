-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.AddCircle.Real
import OAI.Compat.Core

namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open Finset Function MeasureTheory Set

namespace Erdos3.CircleFourier

noncomputable section

abbrev Circle := UnitAddCircle

abbrev circleHaar : Measure Circle := AddCircle.haarAddCircle

theorem circleHaar_eq_volume : circleHaar = (volume : Measure Circle) := by
  symm
  simpa [circleHaar] using
    (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

def integerDistance (x : Circle) : ℝ := ‖x‖

theorem integerDistance_nonneg (x : Circle) : 0 ≤ integerDistance x := norm_nonneg x

theorem integerDistance_le_half (x : Circle) : integerDistance x ≤ 1 / 2 := by
  simpa [integerDistance] using AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero (x := x)

@[simp]
theorem integerDistance_zero : integerDistance (0 : Circle) = 0 := by
  simp [integerDistance]

@[simp]
theorem integerDistance_neg (x : Circle) : integerDistance (-x) = integerDistance x := by
  simp [integerDistance]

@[simp]
theorem integerDistance_coe (x : ℝ) :
    integerDistance (x : Circle) = |x - round x| := by
  simp [integerDistance, UnitAddCircle.norm_eq]

def character (x : Circle) : ℂ := AddCircle.toCircle x

@[simp]
theorem character_zero : character 0 = 1 := by
  simp [character]

@[simp]
theorem character_add (x y : Circle) : character (x + y) = character x * character y := by
  unfold character
  rw [AddCircle.toCircle_add]
  rfl

@[simp]
theorem character_neg (x : Circle) : character (-x) = star (character x) := by
  unfold character
  rw [AddCircle.toCircle_neg, _root_.Circle.coe_inv, Complex.inv_def,
    _root_.Circle.normSq_coe]
  simp

@[simp]
theorem character_nsmul (n : ℕ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_nsmul]
  rfl

@[simp]
theorem character_zsmul (n : ℤ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_zsmul]
  rfl

@[simp]
theorem character_finset_sum {I : Type*} (s : Finset I) (f : I → Circle) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, character_add]

@[simp]
theorem character_fintype_sum {I : Type*} [Fintype I] (f : I → Circle) :
    character (∑ i, f i) = ∏ i, character (f i) := by
  simp

@[simp]
theorem norm_character (x : Circle) : ‖character x‖ = 1 := by
  exact Circle.norm_coe _

theorem character_eq_one_iff (x : Circle) : character x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [character] using h
  · rintro rfl
    exact character_zero

def geometricCharacterSum (N : ℕ) (x : Circle) : ℂ :=
  ∑ n ∈ range N, character (n • x)

theorem geometricCharacterSum_mul (N : ℕ) (x : Circle) :
    geometricCharacterSum N x * (character x - 1) = character (N • x) - 1 := by
  simp only [geometricCharacterSum, character_nsmul]
  exact geom_sum_mul (character x) N

theorem norm_character_sub_one_le_two (x : Circle) : ‖character x - 1‖ ≤ 2 := by
  calc
    ‖character x - 1‖ ≤ ‖character x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

theorem four_mul_integerDistance_le_norm_character_sub_one (x : Circle) :
    4 * integerDistance x ≤ ‖character x - 1‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  let y : ℝ := r - round r
  have hyabs : |y| ≤ 1 / 2 := by
    simpa [y] using abs_sub_round r
  have hypi_abs : |π * y| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin : 2 * |y| ≤ |Real.sin (π * y)| := by
    have h := Real.mul_abs_le_abs_sin hypi_abs
    calc
      2 * |y| = (2 / π) * |π * y| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (π * y)| := h
  have hry : (r : Circle) = (y : Circle) := by
    simp [y, sub_eq_add_neg]
  have hcharacter :
      character (y : Circle) = Complex.exp (Complex.I * (2 * π * y : ℝ)) := by
    unfold character
    rw [AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [integerDistance_coe]
  change 4 * |y| ≤ _
  rw [hry, hcharacter, Complex.norm_exp_I_mul_ofReal_sub_one]
  change 4 * |y| ≤ |2 * Real.sin ((2 * π * y) / 2)|
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    4 * |y| = 2 * (2 * |y|) := by ring
    _ ≤ 2 * |Real.sin (π * y)| :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    _ = 2 * |Real.sin ((2 * π * y) / 2)| := by ring_nf

theorem two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one
    (N : ℕ) (x : Circle) :
    2 * integerDistance x * ‖geometricCharacterSum N x‖ ≤ 1 := by
  have hprod :
      ‖geometricCharacterSum N x‖ * ‖character x - 1‖ ≤ 2 := by
    rw [← norm_mul, geometricCharacterSum_mul]
    exact norm_character_sub_one_le_two _
  have hden := four_mul_integerDistance_le_norm_character_sub_one x
  have hnorm : 0 ≤ ‖geometricCharacterSum N x‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hden hnorm]

theorem norm_geometricCharacterSum_le (N : ℕ) {x : Circle} (hx : x ≠ 0) :
    ‖geometricCharacterSum N x‖ ≤ (2 * integerDistance x)⁻¹ := by
  have hdist : 0 < integerDistance x := by
    simpa [integerDistance, norm_pos_iff] using hx
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x

theorem geometricCharacterSum_eq_sum_fin (N : ℕ) (x : Circle) :
    geometricCharacterSum N x = ∑ n : Fin N, character ((n : ℕ) • x) := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [geometricCharacterSum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Finset.mem_range.mp hn]

end
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped Real NNReal

noncomputable def characterLipConstant : ℝ≥0 := ⟨2 * Real.pi, by positivity⟩

theorem coe_characterLipConstant : (characterLipConstant : ℝ) = 2 * Real.pi := rfl

theorem character_coe_exp (r : ℝ) :
    character (r : Circle) = Complex.exp (Complex.I * (2 * Real.pi * r : ℝ)) := by
  unfold character
  rw [AddCircle.toCircle, Function.Periodic.lift_coe, _root_.Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem norm_character_sub_one_le (x : Circle) :
    ‖character x - 1‖ ≤ 2 * Real.pi * ‖x‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  let y : ℝ := r - round r
  have hry : (r : Circle) = (y : Circle) := by simp [y, sub_eq_add_neg]
  change ‖character (r : Circle) - 1‖ ≤ 2 * Real.pi * integerDistance (r : Circle)
  rw [integerDistance_coe]
  change ‖character (r : Circle) - 1‖ ≤ 2 * Real.pi * |y|
  rw [hry, character_coe_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : (2 * Real.pi * y) / 2 = Real.pi * y := by ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * |Real.pi * y| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

theorem character_lipschitz : LipschitzWith characterLipConstant character := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : character (x - y) * character y = character x := by
    rw [← character_add, sub_add_cancel]
  have heq : (character (x - y) - 1) * character y = character x - character y := by
    rw [sub_mul, one_mul, hxy]
  have hnorm : ‖character x - character y‖ = ‖character (x - y) - 1‖ := by
    rw [← heq, norm_mul, norm_character, mul_one]
  rw [dist_eq_norm, hnorm, dist_eq_norm]
  exact norm_character_sub_one_le (x - y)

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def cyclicIntegerCharacter (M : ℕ) [NeZero M] (z : ℤ) : AddChar (ZMod M) ℂ where
  toFun r := character (ZMod.toAddCircle (r * (z : ZMod M)))
  map_zero_eq_one' := by simp only [zero_mul, map_zero, character_zero]
  map_add_eq_mul' r s := by
    simp only [add_mul, map_add, character_add]

theorem cyclicIntegerCharacter_intCast (M : ℕ) [NeZero M] (r z : ℤ) :
    cyclicIntegerCharacter M z (r : ZMod M) =
      character (((r : ℝ) * (z : ℝ) / M : ℝ) : CircleFourier.Circle) := by
  change character (ZMod.toAddCircle ((r : ZMod M) * (z : ZMod M))) = _
  rw [← Int.cast_mul, ZMod.toAddCircle_intCast]
  simp only [Int.cast_mul]

theorem cyclicIntegerCharacter_eq_zero_iff (M : ℕ) [NeZero M] (z : ℤ) :
    cyclicIntegerCharacter M z = 0 ↔ (z : ZMod M) = 0 := by
  constructor
  · intro h
    have he := DFunLike.congr_fun h (1 : ZMod M)
    change character (ZMod.toAddCircle ((1 : ZMod M) * (z : ZMod M))) = 1 at he
    rw [one_mul, character_eq_one_iff, ZMod.toAddCircle_eq_zero] at he
    exact he
  · intro h
    apply AddChar.ext
    intro r
    change character (ZMod.toAddCircle (r * (z : ZMod M))) = 1
    simp only [h, mul_zero, map_zero, character_zero]

theorem cyclicIntegerCharacter_sum (M : ℕ) [NeZero M] (z : ℤ) :
    (∑ r : ZMod M, cyclicIntegerCharacter M z r) =
      if (z : ZMod M) = 0 then (M : ℂ) else 0 := by
  classical
  simpa only [cyclicIntegerCharacter_eq_zero_iff, ZMod.card] using
    AddChar.sum_eq_ite (cyclicIntegerCharacter M z)

noncomputable def gridResidueEquiv (M : ℕ) [NeZero M] : Fin M ≃ ZMod M where
  toFun k := (k.val : ZMod M)
  invFun r := ⟨r.val, ZMod.val_lt r⟩
  left_inv k := by
    apply Fin.ext
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]
  right_inv r := ZMod.natCast_zmod_val r

noncomputable def integerGridCharacter (M : ℕ) [NeZero M] (k : Fin M) (z : ℤ) : ℂ :=
  cyclicIntegerCharacter M z (gridResidueEquiv M k)

theorem integerGridCharacter_eq (M : ℕ) [NeZero M] (k : Fin M) (z : ℤ) :
    integerGridCharacter M k z =
      character ((((k.val : ℝ) / M) * z : ℝ) : CircleFourier.Circle) := by
  have h := cyclicIntegerCharacter_intCast M (k.val : ℤ) z
  simpa only [integerGridCharacter, gridResidueEquiv, Equiv.coe_fn_mk,
    Int.cast_natCast, div_mul_eq_mul_div] using h

theorem integerGridCharacter_sum (M : ℕ) [NeZero M] (z : ℤ) :
    (∑ k : Fin M, integerGridCharacter M k z) =
      if (z : ZMod M) = 0 then (M : ℂ) else 0 := by
  rw [← cyclicIntegerCharacter_sum M z]
  exact (Equiv.sum_comp (gridResidueEquiv M) (cyclicIntegerCharacter M z))

end Erdos3

end

section

namespace Erdos3

open CircleFourier

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def linearCircleHom (L : E →ₗ[ℝ] ℝ) : E →+ CircleFourier.Circle :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp L.toAddMonoidHom

theorem integral_subgroup_le_linearCircleHom_ker (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) : Γ ≤ (linearCircleHom L).ker := by
  intro x hx
  change (L x : CircleFourier.Circle) = 0
  obtain ⟨n, hn⟩ := hint x hx
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simp [hn]⟩

noncomputable def quotientLinearPhase (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) : (E ⧸ Γ) →+ CircleFourier.Circle :=
  QuotientAddGroup.lift Γ (linearCircleHom L) (integral_subgroup_le_linearCircleHom_ker Γ L hint)

noncomputable def quotientLinearCharacter (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E ⧸ Γ) : ℂ :=
  character (quotientLinearPhase Γ L hint x)

theorem quotientLinearCharacter_mk (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E) :
    quotientLinearCharacter Γ L hint (QuotientAddGroup.mk' Γ x) =
      character (L x : CircleFourier.Circle) := rfl

theorem quotientLinearCharacter_add (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x y : E ⧸ Γ) :
    quotientLinearCharacter Γ L hint (x + y) =
      quotientLinearCharacter Γ L hint x * quotientLinearCharacter Γ L hint y := by
  simp only [quotientLinearCharacter, map_add, character_add]

theorem quotientLinearCharacter_norm (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : E ⧸ Γ) :
    ‖quotientLinearCharacter Γ L hint x‖ = 1 := norm_character _

theorem quotientLinearCharacter_zero (Γ : AddSubgroup E)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, (0 : E →ₗ[ℝ] ℝ) x = n) (x : E ⧸ Γ) :
    quotientLinearCharacter Γ 0 hint x = 1 := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective Γ x
  simp only [quotientLinearCharacter_mk, LinearMap.zero_apply, AddCircle.coe_zero, character_zero]

theorem quotientLinearCharacter_continuous [TopologicalSpace E]
    (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (hL : Continuous L) :
    Continuous (quotientLinearCharacter Γ L hint) := by
  apply (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  change Continuous (fun x : E => character (L x : CircleFourier.Circle))
  exact (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp
    ((AddCircle.continuous_mk' (1 : ℝ)).comp hL)

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

theorem linear_site_sum {S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (v : S → W) :
    M v = ∑ s, M (Pi.single s (v s)) := by
  have hv : v = ∑ s, Pi.single s (v s) := by
    funext s
    simp [Pi.single_apply]
  exact (congrArg M hv).trans (map_sum M _ _)

theorem character_real_sum {S : Type*} (s : Finset S) (f : S → ℝ) :
    character ((∑ t ∈ s, f t : ℝ) : CircleFourier.Circle) =
      ∏ t ∈ s, character (f t : CircleFourier.Circle) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert t s ht ih =>
    simp only [Finset.sum_insert ht, AddCircle.coe_add, character_add, Finset.prod_insert ht, ih]

noncomputable def siteFunctionalCharacter {S W : Type*} [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (s : S) (w : W) : ℂ :=
  character (M (Pi.single s w) : CircleFourier.Circle)

theorem siteFunctionalCharacter_norm {S W : Type*} [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (s : S) (w : W) :
    ‖siteFunctionalCharacter M s w‖ = 1 := norm_character _

theorem character_linear_site_sum {S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (M : (S → W) →ₗ[ℝ] ℝ) (v : S → W) :
    character (M v : CircleFourier.Circle) = ∏ s, siteFunctionalCharacter M s (v s) := by
  rw [linear_site_sum M v]
  exact character_real_sum _ _

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators NNReal

theorem abs_linearMap_le_basis_bound {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (η : V →ₗ[ℝ] ℝ)
    (A : ℝ≥0) (hη : ∀ i, |η (e i)| ≤ A) (x : V) :
    |η x| ≤ (Fintype.card ι : ℝ) * A * ‖e.equivFun x‖ := by
  have hx : η x = ∑ i, e.repr x i * η (e i) := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hx]
  calc
    _ ≤ ∑ i, |e.repr x i * η (e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖e.equivFun x‖ * A := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he : |e.repr x i| ≤ ‖e.equivFun x‖ := by
        simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using (norm_le_pi_norm (e.equivFun x) i)
      exact mul_le_mul he (hη i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem norm_character_real_sub_one_le (r : ℝ) :
    ‖CircleFourier.character (r : CircleFourier.Circle) - 1‖ ≤
      (CircleFourier.characterLipConstant : ℝ) * |r| := by
  apply (CircleFourier.norm_character_sub_one_le _).trans
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using
      (show ‖(r : CircleFourier.Circle)‖ ≤ ‖r‖ from QuotientAddGroup.norm_mk_le_norm))
    (by positivity : 0 ≤ 2 * Real.pi)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem circle_coe_fintype_sum {J : Type*} [Fintype J] (f : J → ℝ) :
    ((∑ j, f j : ℝ) : CircleFourier.Circle) = ∑ j, (f j : CircleFourier.Circle) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ

noncomputable def rectangularGridCharacter {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) : ℂ :=
  ∏ j, integerGridCharacter M (k j) (y j)

def integerGridResidue {J : Type*} (M : ℕ) (y : J → ℤ) : J → ZMod M := fun j => (y j : ZMod M)

theorem rectangularGridCharacter_eq {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    rectangularGridCharacter M k y =
      character ((∑ j, (((k j).val : ℝ) / M) * (y j : ℝ) : ℝ) : CircleFourier.Circle) := by
  simp only [rectangularGridCharacter, integerGridCharacter_eq, circle_coe_fintype_sum, character_fintype_sum]

theorem rectangularGridCharacter_norm {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    ‖rectangularGridCharacter M k y‖ = 1 := by
  rw [rectangularGridCharacter_eq, norm_character]

theorem rectangularGridCharacter_add {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y z : J → ℤ) :
    rectangularGridCharacter M k (y + z) =
      rectangularGridCharacter M k y * rectangularGridCharacter M k z := by
  simp only [rectangularGridCharacter_eq, Pi.add_apply, Int.cast_add, mul_add,
    Finset.sum_add_distrib, AddCircle.coe_add, character_add]

theorem rectangularGridCharacter_sub {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y z : J → ℤ) :
    rectangularGridCharacter M k (y - z) =
      rectangularGridCharacter M k y * star (rectangularGridCharacter M k z) := by
  simp only [rectangularGridCharacter_eq, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
  rw [AddCircle.coe_sub, sub_eq_add_neg, character_add, character_neg]

theorem rectangularGridCharacter_fintype_sum {J B : Type*} [Fintype J] [Fintype B]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : B → J → ℤ) :
    rectangularGridCharacter M k (∑ b, y b) = ∏ b, rectangularGridCharacter M k (y b) := by
  classical
  simp only [rectangularGridCharacter_eq, Finset.sum_apply, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [circle_coe_fintype_sum, character_fintype_sum]

theorem rectangularGridCharacter_sum {J : Type*} [Fintype J] [DecidableEq J]
    (M : ℕ) [NeZero M] (y : J → ℤ) :
    (∑ k : J → Fin M, rectangularGridCharacter M k y) =
      if integerGridResidue M y = 0 then (M : ℂ) ^ Fintype.card J else 0 := by
  classical
  change (∑ k : J → Fin M, ∏ j, integerGridCharacter M (k j) (y j)) = _
  rw [← Fintype.prod_sum (fun j (k : Fin M) => integerGridCharacter M k (y j))]
  simp only [integerGridCharacter_sum]
  by_cases hy : integerGridResidue M y = 0
  · have hz j : (y j : ZMod M) = 0 := congrFun hy j
    simp only [hz, ite_true, Finset.prod_const, Finset.card_univ, hy]
  · have hz : ∃ j, (y j : ZMod M) ≠ 0 := by
      by_contra! h
      exact hy (funext h)
    obtain ⟨j, hj⟩ := hz
    rw [ite_eq_right hy]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem rectangularGridCharacter_orthogonality {J : Type*} [Fintype J] [DecidableEq J]
    (M : ℕ) [NeZero M] (y z : J → ℤ) :
    (∑ k : J → Fin M, rectangularGridCharacter M k y * star (rectangularGridCharacter M k z)) =
      if integerGridResidue M y = integerGridResidue M z then
        (M : ℂ) ^ Fintype.card J else 0 := by
  simp only [← rectangularGridCharacter_sub, rectangularGridCharacter_sum]
  have h : integerGridResidue M (y - z) = 0 ↔ integerGridResidue M y = integerGridResidue M z := by
    simp only [funext_iff, integerGridResidue, Pi.sub_apply, Pi.zero_apply, Int.cast_sub, sub_eq_zero]
  simp only [h]

end Erdos3

end

end OAI
