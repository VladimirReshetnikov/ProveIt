import Surreal.Surcomplex.ExpLogEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The exponential on actual finite surcomplex numbers

The ordinary complex exponential of standard part times the strong
infinitesimal exponential defines the finite exponential of `e:prop-polar`.
It is an additive-to-multiplicative homomorphism onto the units of the
actual finite subring. Its kernel is exactly the ordinary integral
multiples of `2πi`. No exponential on infinite inputs is defined here.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Removing the ordinary complex part is an additive map into actual infinitesimals. -/
def infinitesimalPart : finiteSubring.{u} →+ infinitesimalAddSubgroup.{u} where
  toFun z := ⟨(z : Surcomplex.{u}) - ofComplex (standardPartHom z),
    infinitesimal_sub_standardPart z.property⟩
  map_zero' := by
    apply Subtype.ext
    change (0 : Surcomplex.{u}) - ofComplex (standardPartHom 0) = 0
    rw [map_zero, map_zero, sub_self]
  map_add' z w := by
    apply Subtype.ext
    change ((z : Surcomplex.{u}) + (w : Surcomplex.{u})) -
      ofComplex (standardPartHom (z + w)) = _
    rw [map_add, map_add]
    change (z : Surcomplex.{u}) + (w : Surcomplex.{u}) -
      (ofComplex (standardPartHom z) + ofComplex (standardPartHom w)) =
        ((z : Surcomplex.{u}) - ofComplex (standardPartHom z)) +
          ((w : Surcomplex.{u}) - ofComplex (standardPartHom w))
    abel

@[simp] theorem coe_infinitesimalPart (z : finiteSubring.{u}) :
    (infinitesimalPart z : Surcomplex.{u}) =
      (z : Surcomplex.{u}) - ofComplex (standardPartHom z) := rfl

/-- The actual finite exponential, with its finite-input domain explicit. -/
def finiteExp (z : finiteSubring.{u}) : Surcomplex.{u} :=
  ofComplex (Complex.exp (standardPartHom z)) *
    infExp (infinitesimalPart z).val (infinitesimalPart z).property

@[simp] theorem finiteExp_zero : finiteExp (0 : finiteSubring.{u}) = 1 := by
  unfold finiteExp
  rw [map_zero, Complex.exp_zero, map_one]
  simp only [map_zero, ZeroMemClass.coe_zero, infExp_zero, mul_one]

/-- Actual finite exponentiation converts addition to multiplication. -/
theorem finiteExp_add (z w : finiteSubring.{u}) :
    finiteExp (z + w) = finiteExp z * finiteExp w := by
  have he : infExp (infinitesimalPart (z + w)).val (infinitesimalPart (z + w)).property =
      infExp (infinitesimalPart z).val (infinitesimalPart z).property *
        infExp (infinitesimalPart w).val (infinitesimalPart w).property := by
    calc
      _ = infExp (infinitesimalPart z + infinitesimalPart w).val
          (infinitesimalPart z + infinitesimalPart w).property :=
        congrArg (fun q : infinitesimalAddSubgroup.{u} => infExp q.val q.property)
          (infinitesimalPart.map_add z w)
      _ = _ := infExp_add _ _ _ _
  unfold finiteExp
  rw [he, map_add, Complex.exp_add, map_mul]
  ring

/-- Every value of the finite exponential is finite. -/
theorem isFinite_finiteExp (z : finiteSubring.{u}) : IsFinite (finiteExp z) :=
  finiteSubring.mul_mem (finite_ofComplex _)
    (isFinite_infExp (infinitesimalPart z).val (infinitesimalPart z).property)

/-- Standard part is the ordinary complex exponential of the input's standard part. -/
@[simp] theorem standardPart_finiteExp (z : finiteSubring.{u}) :
    standardPart (finiteExp z) = Complex.exp (standardPartHom z) := by
  rw [finiteExp, standardPart_mul (finite_ofComplex _) (isFinite_infExp _ _),
    standardPart_ofComplex, standardPart_infExp, mul_one]

/-- Finite exponentiation takes values in the units of the actual finite subring. -/
def finiteExpHom : Multiplicative finiteSubring.{u} →* finiteSubring.{u}ˣ :=
  MonoidHom.toHomUnits
    { toFun z := ⟨finiteExp z.toAdd, isFinite_finiteExp z.toAdd⟩
      map_one' := by apply Subtype.ext; exact finiteExp_zero
      map_mul' z w := by apply Subtype.ext; exact finiteExp_add z.toAdd w.toAdd }

@[simp] theorem coe_finiteExpHom (z : Multiplicative finiteSubring.{u}) :
    ((finiteExpHom z : finiteSubring.{u}) : Surcomplex.{u}) = finiteExp z.toAdd := rfl

theorem isUnit_finiteExp (z : finiteSubring.{u}) :
    IsUnit (⟨finiteExp z, isFinite_finiteExp z⟩ : finiteSubring.{u}) :=
  (finiteExpHom (Multiplicative.ofAdd z)).isUnit

/-- Ordinary complex inputs retain their ordinary exponentials. -/
@[simp] theorem finiteExp_constant (c : ℂ) :
    finiteExp (⟨ofComplex c, finite_ofComplex c⟩ : finiteSubring.{u}) =
      ofComplex (Complex.exp c) := by
  simp [finiteExp, infinitesimalPart]

/-- On infinitesimal inputs the finite and infinitesimal exponentials agree. -/
theorem finiteExp_of_isInfinitesimal (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    finiteExp (⟨x, finite_of_infinitesimal hx⟩ : finiteSubring.{u}) = infExp x hx := by
  have hc : standardPart x = 0 := (standardPart_eq_zero_iff (finite_of_infinitesimal hx)).mpr hx
  simp [finiteExp, infinitesimalPart, hc]

/-- The finite exponential is never zero. -/
theorem finiteExp_ne_zero (z : finiteSubring.{u}) : finiteExp z ≠ 0 :=
  mul_ne_zero ((map_ne_zero ofComplex).mpr (Complex.exp_ne_zero _)) (infExp_ne_zero _ _)

/-- Dividing a finite value by its nonzero ordinary part gives a value near one. -/
theorem infinitesimal_residue_normalization_sub_one (y : finiteSubring.{u})
    (hy : standardPartHom y ≠ 0) :
    IsInfinitesimal (ofComplex ((standardPartHom y)⁻¹) * (y : Surcomplex.{u}) - 1) := by
  let a : finiteSubring.{u} := ⟨ofComplex ((standardPartHom y)⁻¹), finite_ofComplex _⟩
  change IsInfinitesimal ((a * y - 1 : finiteSubring.{u}) : Surcomplex.{u})
  apply (standardPart_eq_zero_iff (a * y - 1).property).mp
  change standardPartHom (a * y - 1) = 0
  rw [map_sub, map_mul, map_one]
  have ha : standardPartHom a = (standardPartHom y)⁻¹ := by
    change standardPart (ofComplex ((standardPartHom y)⁻¹)) = _
    exact standardPart_ofComplex _
  rw [ha, inv_mul_cancel₀ hy, sub_self]

/-- Every finite value with nonzero standard part is a finite exponential. -/
theorem exists_finiteExp_eq (y : finiteSubring.{u}) (hy : standardPartHom y ≠ 0) :
    ∃ z : finiteSubring.{u}, finiteExp z = (y : Surcomplex.{u}) := by
  let c := standardPartHom y
  let ε : Surcomplex.{u} := ofComplex (c⁻¹) * (y : Surcomplex.{u}) - 1
  have hε : IsInfinitesimal ε := infinitesimal_residue_normalization_sub_one y hy
  let a : finiteSubring.{u} := ⟨ofComplex (Complex.log c), finite_ofComplex _⟩
  let b : finiteSubring.{u} := ⟨infLog ε hε, finite_of_infinitesimal (infinitesimal_infLog ε hε)⟩
  refine ⟨a + b, ?_⟩
  rw [finiteExp_add]
  have ha : finiteExp a = ofComplex c := by
    rw [show a = ⟨ofComplex (Complex.log c), finite_ofComplex _⟩ from rfl,
      finiteExp_constant, Complex.exp_log hy]
  have hb : finiteExp b = 1 + ε := by
    exact (finiteExp_of_isInfinitesimal _ (infinitesimal_infLog ε hε)).trans (infExp_infLog ε hε)
  rw [ha, hb]
  change ofComplex c * (1 + (ofComplex (c⁻¹) * (y : Surcomplex.{u}) - 1)) = _
  rw [add_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hy, map_one, one_mul]

/-- Finite exponentiation is onto the units of the actual finite subring. -/
theorem finiteExpHom_surjective : Function.Surjective (finiteExpHom.{u}) := by
  intro y
  have hy : standardPartHom (y : finiteSubring.{u}) ≠ 0 :=
    ((Units.isUnit y).map standardPartHom).ne_zero
  obtain ⟨z, hz⟩ := exists_finiteExp_eq (y : finiteSubring.{u}) hy
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  apply Units.ext
  apply Subtype.ext
  exact hz

/-- The kernel is exactly the ordinary integral multiples of `2πi`. -/
theorem finiteExp_eq_one_iff (z : finiteSubring.{u}) :
    finiteExp z = 1 ↔ ∃ n : ℤ,
      (z : Surcomplex.{u}) = ofComplex ((n : ℂ) * (2 * Real.pi * Complex.I)) := by
  constructor
  · intro hz
    have hc : Complex.exp (standardPartHom z) = 1 := by
      have h := congrArg standardPart hz
      simpa only [standardPart_finiteExp,
        show standardPart (1 : Surcomplex.{u}) = 1 from standardPartHom.map_one] using h
    have he : infExp (infinitesimalPart z).val (infinitesimalPart z).property = 1 := by
      simpa only [finiteExp, hc, map_one, one_mul] using hz
    have hzero : (infinitesimalPart z).val = 0 := by
      apply infExp_injective (infinitesimalPart z).property infinitesimalAddSubgroup.zero_mem
      simpa only [infExp_zero] using he
    have hzconst : (z : Surcomplex.{u}) = ofComplex (standardPartHom z) := sub_eq_zero.mp hzero
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hc
    exact ⟨n, hzconst.trans (congrArg ofComplex hn)⟩
  · rintro ⟨n, hn⟩
    have hz : z = ⟨ofComplex ((n : ℂ) * (2 * Real.pi * Complex.I)), finite_ofComplex _⟩ :=
      Subtype.ext hn
    rw [hz, finiteExp_constant, Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩, map_one]

/-- Subtraction of finite inputs corresponds to division of exponentials. -/
theorem finiteExp_sub (z w : finiteSubring.{u}) :
    finiteExp (z - w) = finiteExp z / finiteExp w := by
  apply (eq_div_iff (finiteExp_ne_zero w)).mpr
  simpa only [sub_add_cancel] using (finiteExp_add (z - w) w).symm

theorem finiteExp_neg (z : finiteSubring.{u}) : finiteExp (-z) = (finiteExp z)⁻¹ := by
  simpa only [zero_sub, finiteExp_zero, one_div] using finiteExp_sub 0 z

/-- Equal finite exponentials differ by precisely an ordinary integral period. -/
theorem finiteExp_eq_finiteExp_iff (z w : finiteSubring.{u}) :
    finiteExp z = finiteExp w ↔ ∃ n : ℤ,
      (z : Surcomplex.{u}) - (w : Surcomplex.{u}) =
        ofComplex ((n : ℂ) * (2 * Real.pi * Complex.I)) := by
  rw [← div_eq_one_iff_eq (finiteExp_ne_zero w), ← finiteExp_sub]
  exact finiteExp_eq_one_iff (z - w)

end

end Surreal.Surcomplex
