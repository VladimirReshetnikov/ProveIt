import Surreal.HahnSeries.ExponentialAddition
import Surreal.HahnSeries.StandardPart
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Exponentiation of finite complex Hahn series

The ordinary complex exponential of the standard part times the infinitesimal
Hahn exponential gives the finite exponential of `e:prop-polar`. The domain
is the proved nonnegative-order subring. The map is onto its units, and its
kernel consists exactly of the ordinary integral multiples of `2πi`.
No exponential on infinite inputs
or evaluation in the actual surcomplex field is assumed.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- Removing standard part is an additive map into the infinitesimals. -/
def infinitesimalPart : nonnegativeSubring Γ K →+ positiveOrderAddSubgroup Γ K where
  toFun z := ⟨(z : K⟦Γ⟧) - single 0 (standardPart Γ K z), orderTop_sub_standardPart_pos z⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' z w := by
    apply Subtype.ext
    change ((z : K⟦Γ⟧) + (w : K⟦Γ⟧)) - single 0 (standardPart Γ K (z + w)) = _
    rw [map_add, single_add]
    change (z : K⟦Γ⟧) + (w : K⟦Γ⟧) - (single 0 (standardPart Γ K z) + single 0 (standardPart Γ K w)) =
      ((z : K⟦Γ⟧) - single 0 (standardPart Γ K z)) +
        ((w : K⟦Γ⟧) - single 0 (standardPart Γ K w))
    abel

@[simp] theorem coe_infinitesimalPart (z : nonnegativeSubring Γ K) :
    (infinitesimalPart z : K⟦Γ⟧) = (z : K⟦Γ⟧) - single 0 (standardPart Γ K z) := rfl

/-- The finite exponential is defined on the actual nonnegative-order ring. -/
def finiteExp (z : nonnegativeSubring Γ ℂ) : ℂ⟦Γ⟧ :=
  single 0 (Complex.exp (standardPart Γ ℂ z)) *
    infExp (infinitesimalPart z).val (infinitesimalPart z).property

@[simp] theorem finiteExp_zero : finiteExp (0 : nonnegativeSubring Γ ℂ) = 1 := by
  simp [finiteExp]

/-- The finite exponential converts addition to multiplication. -/
theorem finiteExp_add (z w : nonnegativeSubring Γ ℂ) :
    finiteExp (z + w) = finiteExp z * finiteExp w := by
  have he : infExp (infinitesimalPart (z + w)).val (infinitesimalPart (z + w)).property =
      infExp (infinitesimalPart z).val (infinitesimalPart z).property *
        infExp (infinitesimalPart w).val (infinitesimalPart w).property := by
    calc
      _ = infExp (infinitesimalPart z + infinitesimalPart w).val
          (infinitesimalPart z + infinitesimalPart w).property :=
        congrArg (fun q : positiveOrderAddSubgroup Γ ℂ => infExp q.val q.property)
          (infinitesimalPart.map_add z w)
      _ = _ := infExp_add _ _ _ _
  unfold finiteExp
  rw [he, map_add, Complex.exp_add]
  rw [show single (0 : Γ) (Complex.exp (standardPart Γ ℂ z) * Complex.exp (standardPart Γ ℂ w)) =
      single 0 (Complex.exp (standardPart Γ ℂ z)) * single 0 (Complex.exp (standardPart Γ ℂ w)) by
    rw [single_mul_single, zero_add]]
  ring

/-- The image is a finite unit, with precisely order zero. -/
@[simp] theorem orderTop_finiteExp (z : nonnegativeSubring Γ ℂ) :
    (finiteExp z).orderTop = 0 := by
  rw [finiteExp, orderTop_mul, infExp_orderTop, add_zero,
    orderTop_single (Complex.exp_ne_zero _), WithTop.coe_zero]

/-- Standard part is the ordinary complex exponential of standard part. -/
@[simp] theorem coeff_zero_finiteExp (z : nonnegativeSubring Γ ℂ) :
    (finiteExp z).coeff 0 = Complex.exp (standardPart Γ ℂ z) := by
  rw [finiteExp, coeff_zero_mul_of_nonnegative _ _ orderTop_single_le
    (by rw [infExp_orderTop]), coeff_single_same, coeff_zero_infExp, mul_one]

/-- The finite exponential as a homomorphism into the units of the finite ring. -/
def finiteExpHom : Multiplicative (nonnegativeSubring Γ ℂ) →* (nonnegativeSubring Γ ℂ)ˣ :=
  MonoidHom.toHomUnits
    { toFun z := ⟨finiteExp z.toAdd, by rw [mem_nonnegativeSubring, orderTop_finiteExp]⟩
      map_one' := by apply Subtype.ext; exact finiteExp_zero
      map_mul' z w := by apply Subtype.ext; exact finiteExp_add z.toAdd w.toAdd }

@[simp] theorem coe_finiteExpHom (z : Multiplicative (nonnegativeSubring Γ ℂ)) :
    ((finiteExpHom z : nonnegativeSubring Γ ℂ) : ℂ⟦Γ⟧) = finiteExp z.toAdd := rfl

/-- A constant Hahn input has the ordinary complex exponential. -/
@[simp] theorem finiteExp_constant (c : ℂ) :
    finiteExp (⟨single 0 c, orderTop_single_le⟩ : nonnegativeSubring Γ ℂ) =
      single 0 (Complex.exp c) := by
  simp [finiteExp, infinitesimalPart]

/-- On positive-order inputs, finite exponentiation is the infinitesimal exponential. -/
theorem finiteExp_of_orderTop_pos (x : ℂ⟦Γ⟧) (hx : 0 < x.orderTop) :
    finiteExp (⟨x, hx.le⟩ : nonnegativeSubring Γ ℂ) = infExp x hx := by
  have hc : x.coeff 0 = 0 := coeff_eq_zero_of_lt_orderTop hx
  simp [finiteExp, infinitesimalPart, hc]

/-- Finite exponentials never vanish. -/
theorem finiteExp_ne_zero (z : nonnegativeSubring Γ ℂ) : finiteExp z ≠ 0 := by
  intro h
  have hc := coeff_zero_finiteExp z
  rw [h, coeff_zero] at hc
  exact Complex.exp_ne_zero _ hc.symm

/-- Dividing a finite unit by its nonzero residue produces a principal unit. -/
theorem orderTop_residue_normalization_sub_one_pos (y : nonnegativeSubring Γ ℂ)
    (hy : standardPart Γ ℂ y ≠ 0) :
    0 < (single 0 (standardPart Γ ℂ y)⁻¹ * (y : ℂ⟦Γ⟧) - 1).orderTop := by
  have hn : 0 ≤ (single 0 (standardPart Γ ℂ y)⁻¹ * (y : ℂ⟦Γ⟧)).orderTop := by
    rw [orderTop_mul]
    exact add_nonneg orderTop_single_le y.property
  apply (coeff_zero_eq_zero_iff_orderTop_pos _
    ((le_min hn (by simp)).trans min_orderTop_le_orderTop_sub)).mp
  rw [coeff_sub, coeff_zero_mul_of_nonnegative _ _ orderTop_single_le y.property,
    coeff_single_same, coeff_one, if_pos rfl, ← standardPart_apply, inv_mul_cancel₀ hy, sub_self]

/-- Every finite series with nonzero residue has a finite exponential preimage.
The constant part is an ordinary complex logarithm, and the remainder is
constructed by the strongly summable infinitesimal logarithm. -/
theorem exists_finiteExp_eq (y : nonnegativeSubring Γ ℂ)
    (hy : standardPart Γ ℂ y ≠ 0) :
    ∃ z : nonnegativeSubring Γ ℂ, finiteExp z = (y : ℂ⟦Γ⟧) := by
  let c := standardPart Γ ℂ y
  let ε : ℂ⟦Γ⟧ := single 0 c⁻¹ * (y : ℂ⟦Γ⟧) - 1
  have hε : 0 < ε.orderTop := orderTop_residue_normalization_sub_one_pos y hy
  let a : nonnegativeSubring Γ ℂ := ⟨single 0 (Complex.log c), orderTop_single_le⟩
  let b : nonnegativeSubring Γ ℂ := ⟨infLog ε hε, (infLog_orderTop_pos ε hε).le⟩
  refine ⟨a + b, ?_⟩
  rw [finiteExp_add]
  have ha : finiteExp a = single 0 c := by
    rw [show a = ⟨single 0 (Complex.log c), orderTop_single_le⟩ from rfl,
      finiteExp_constant, Complex.exp_log hy]
  have hb : finiteExp b = 1 + ε := by
    exact (finiteExp_of_orderTop_pos _ (infLog_orderTop_pos ε hε)).trans
      (infExp_infLog ε hε)
  rw [ha, hb]
  change single 0 c * (1 + (single 0 c⁻¹ * (y : ℂ⟦Γ⟧) - 1)) = _
  rw [← add_sub_assoc, add_sub_cancel_left, ← mul_assoc, single_mul_single, zero_add,
    mul_inv_cancel₀ hy, single_zero_one, one_mul]

/-- The finite exponential homomorphism is onto all units of the finite ring. -/
theorem finiteExpHom_surjective :
    Function.Surjective (finiteExpHom (Γ := Γ)) := by
  intro y
  have hy : standardPart Γ ℂ (y : nonnegativeSubring Γ ℂ) ≠ 0 :=
    ((Units.isUnit y).map (standardPart Γ ℂ)).ne_zero
  obtain ⟨z, hz⟩ := exists_finiteExp_eq (y : nonnegativeSubring Γ ℂ) hy
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  apply Units.ext
  apply Subtype.ext
  exact hz

/-- The exact kernel consists of ordinary integral multiples of `2πi`.
In particular there is no nonzero infinitesimal period. -/
theorem finiteExp_eq_one_iff (z : nonnegativeSubring Γ ℂ) :
    finiteExp z = 1 ↔ ∃ n : ℤ,
      (z : ℂ⟦Γ⟧) = single 0 ((n : ℂ) * (2 * Real.pi * Complex.I)) := by
  constructor
  · intro hz
    have hc : Complex.exp (standardPart Γ ℂ z) = 1 := by
      have h := congrArg (fun x : ℂ⟦Γ⟧ => x.coeff 0) hz
      simpa using h
    have he : infExp (infinitesimalPart z).val (infinitesimalPart z).property = 1 := by
      simpa only [finiteExp, hc, single_zero_one, one_mul] using hz
    have hzero : (infinitesimalPart z).val = 0 := by
      apply infExp_injective (infinitesimalPart z).property (by simp)
      simpa only [infExp_zero] using he
    have hzconst : (z : ℂ⟦Γ⟧) = single 0 (standardPart Γ ℂ z) :=
      sub_eq_zero.mp hzero
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hc
    exact ⟨n, hzconst.trans (congrArg (single 0) hn)⟩
  · rintro ⟨n, hn⟩
    have hz : z = ⟨single 0 ((n : ℂ) * (2 * Real.pi * Complex.I)), orderTop_single_le⟩ :=
      Subtype.ext hn
    rw [hz, finiteExp_constant, Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩, single_zero_one]

/-- Subtraction of finite inputs corresponds to division of their exponentials. -/
theorem finiteExp_sub (z w : nonnegativeSubring Γ ℂ) :
    finiteExp (z - w) = finiteExp z / finiteExp w := by
  apply (eq_div_iff (finiteExp_ne_zero w)).mpr
  simpa only [sub_add_cancel] using (finiteExp_add (z - w) w).symm

/-- Two finite inputs have the same exponential exactly when their difference
is an ordinary integral multiple of `2πi`. -/
theorem finiteExp_eq_finiteExp_iff (z w : nonnegativeSubring Γ ℂ) :
    finiteExp z = finiteExp w ↔ ∃ n : ℤ,
      (z : ℂ⟦Γ⟧) - (w : ℂ⟦Γ⟧) = single 0 ((n : ℂ) * (2 * Real.pi * Complex.I)) := by
  rw [← div_eq_one_iff_eq (finiteExp_ne_zero w), ← finiteExp_sub]
  exact finiteExp_eq_one_iff (z - w)

end

end Surreal.HahnSeries
