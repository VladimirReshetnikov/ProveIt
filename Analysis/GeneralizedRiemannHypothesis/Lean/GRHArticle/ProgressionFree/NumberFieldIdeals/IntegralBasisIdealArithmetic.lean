import GRHArticle.ProgressionFree.NumberFieldIdeals.ComputableIdealDensity
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Explicit ideal computations from integral-basis coordinates

An integral basis with executable coordinate extraction and the integer
coefficients of the unit and basis products gives executable residue-ring arithmetic. Reduction of the
basis coordinates has exactly the required principal-ideal kernel.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal Finset Module

universe u

/-- An explicit integral basis with exact coordinate extraction and its
certified multiplication table. -/
structure IntegralBasisIdealArithmetic (K : Type u) [Field K] [NumberField K] where
  degree : ℕ
  coordinates : 𝓞 K → Fin degree → ℤ
  oneCoordinates : Fin degree → ℤ
  multiplyCoordinates : Fin degree → Fin degree → Fin degree → ℤ
  basisCertificate : ∃ b : Basis (Fin degree) ℤ (𝓞 K),
    (∀ x i, coordinates x i = b.repr x i) ∧
    (∀ i, b.repr 1 i = oneCoordinates i) ∧
    (∀ i j k, b.repr (b i * b j) k = multiplyCoordinates i j k)
  degree_eq : degree = Module.finrank ℚ K

namespace IntegralBasisIdealArithmetic

variable {K : Type u} [Field K] [NumberField K] (A : IntegralBasisIdealArithmetic K)

private noncomputable def basis : Basis (Fin A.degree) ℤ (𝓞 K) := A.basisCertificate.choose

private theorem coordinates_eq (x : 𝓞 K) (i : Fin A.degree) : A.coordinates x i = A.basis.repr x i :=
  A.basisCertificate.choose_spec.1 x i

private theorem one_eq (i : Fin A.degree) : A.basis.repr 1 i = A.oneCoordinates i :=
  A.basisCertificate.choose_spec.2.1 i

private theorem multiply_eq (i j k : Fin A.degree) :
    A.basis.repr (A.basis i * A.basis j) k = A.multiplyCoordinates i j k :=
  A.basisCertificate.choose_spec.2.2 i j k

private def Coordinates (degree H : ℕ) := Fin degree → ZMod (H.factorial^2)

private instance (degree H : ℕ) : Zero (Coordinates degree H) where
  zero := fun _ ↦ 0

private instance (degree H : ℕ) : Add (Coordinates degree H) where
  add x y := fun i ↦ x i + y i

private instance (degree H : ℕ) : Neg (Coordinates degree H) where
  neg x := fun i ↦ -x i

private instance (degree H : ℕ) : Sub (Coordinates degree H) where
  sub x y := fun i ↦ x i - y i

private instance (degree H : ℕ) : SMul ℕ (Coordinates degree H) where
  smul n x := fun i ↦ n • x i

private instance (degree H : ℕ) : SMul ℤ (Coordinates degree H) where
  smul n x := fun i ↦ n • x i

private instance (degree H : ℕ) [NeZero (H.factorial^2)] : Fintype (Coordinates degree H) :=
  inferInstanceAs (Fintype (Fin degree → ZMod (H.factorial^2)))

private instance (degree H : ℕ) : DecidableEq (Coordinates degree H) :=
  inferInstanceAs (DecidableEq (Fin degree → ZMod (H.factorial^2)))

private def coordinateOne (H : ℕ) : Coordinates A.degree H := fun i ↦ (A.oneCoordinates i : ZMod _)

private def coordinateMul (H : ℕ) (x y : Coordinates A.degree H) : Coordinates A.degree H :=
  fun k ↦ ∑ i, ∑ j, x i * y j * (A.multiplyCoordinates i j k : ZMod _)

private def coordinatePow (H : ℕ) (x : Coordinates A.degree H) (n : ℕ) : Coordinates A.degree H :=
  Nat.rec (A.coordinateOne H) (fun _ y ↦ A.coordinateMul H y x) n

/-- Reduce the integral coordinates modulo the common ideal modulus. -/
private def reduce (H : ℕ) (x : 𝓞 K) : Coordinates A.degree H :=
  fun i ↦ (A.coordinates x i : ZMod _)

private theorem reduce_apply_basis (H : ℕ) (x : 𝓞 K) (i : Fin A.degree) :
    A.reduce H x i = (A.basis.equivFun x i : ZMod (H.factorial^2)) := by
  simp only [reduce, A.coordinates_eq, Basis.equivFun_apply]

private theorem reduce_surjective (H : ℕ) : Function.Surjective (A.reduce H) := by
  letI : NeZero (H.factorial^2) := ⟨pow_ne_zero _ (Nat.factorial_ne_zero _)⟩
  intro x
  refine ⟨A.basis.equivFun.symm (fun i ↦ ((x i).val : ℤ)),?_⟩
  funext i
  rw [A.reduce_apply_basis, LinearEquiv.apply_symm_apply, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]

private theorem reduce_zero (H : ℕ) : A.reduce H 0 = 0 := by
  funext i
  change A.reduce H 0 i = 0
  simp only [A.reduce_apply_basis, map_zero, Pi.zero_apply, Int.cast_zero]

private theorem reduce_one (H : ℕ) : A.reduce H 1 = A.coordinateOne H := by
  funext i
  simp [A.reduce_apply_basis, coordinateOne, A.one_eq]

private theorem reduce_add (H : ℕ) (x y : 𝓞 K) : A.reduce H (x+y) = A.reduce H x + A.reduce H y := by
  funext i
  change A.reduce H (x+y) i = A.reduce H x i + A.reduce H y i
  simp only [A.reduce_apply_basis, map_add, Pi.add_apply, Int.cast_add]

private theorem reduce_neg (H : ℕ) (x : 𝓞 K) : A.reduce H (-x) = -A.reduce H x := by
  funext i
  change A.reduce H (-x) i = -A.reduce H x i
  simp only [A.reduce_apply_basis, map_neg, Pi.neg_apply, Int.cast_neg]

private theorem reduce_sub (H : ℕ) (x y : 𝓞 K) : A.reduce H (x-y) = A.reduce H x - A.reduce H y := by
  funext i
  change A.reduce H (x-y) i = A.reduce H x i - A.reduce H y i
  simp only [A.reduce_apply_basis, map_sub, Pi.sub_apply, Int.cast_sub]

private theorem reduce_nsmul (H n : ℕ) (x : 𝓞 K) : A.reduce H (n • x) = n • A.reduce H x := by
  funext i
  change A.reduce H (n • x) i = n • A.reduce H x i
  simp only [A.reduce_apply_basis, map_nsmul, Pi.smul_apply]
  simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

private theorem reduce_zsmul (H : ℕ) (n : ℤ) (x : 𝓞 K) : A.reduce H (n • x) = n • A.reduce H x := by
  funext i
  change A.reduce H (n • x) i = n • A.reduce H x i
  simp only [A.reduce_apply_basis, map_zsmul, Pi.smul_apply]
  simp [zsmul_eq_mul, Int.cast_mul]

private theorem basis_mul_coordinates (x y : 𝓞 K) (k : Fin A.degree) :
    A.basis.equivFun (x*y) k = ∑ i, ∑ j,
      A.basis.equivFun x i * A.basis.equivFun y j * A.multiplyCoordinates i j k := by
  let a := A.basis.equivFun x
  let b := A.basis.equivFun y
  have hx := A.basis.sum_equivFun x
  have hy := A.basis.sum_equivFun y
  have he : x*y = ∑ i, ∑ j, (a i * b j) • (A.basis i * A.basis j) := by
    calc
      x*y = (∑ i, a i • A.basis i) * (∑ j, b j • A.basis j) := by rw [hx,hy]
      _ = _ := by
        rw [Finset.sum_mul]
        apply sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j _
        simp [zsmul_eq_mul, Int.cast_mul]
        ring
  change A.basis.equivFun (x*y) k = ∑ i, ∑ j, a i * b j * A.multiplyCoordinates i j k
  rw [he]
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
    Basis.equivFun_apply, A.multiply_eq]

private theorem reduce_mul (H : ℕ) (x y : 𝓞 K) :
    A.reduce H (x*y) = A.coordinateMul H (A.reduce H x) (A.reduce H y) := by
  funext k
  simp only [coordinateMul, A.reduce_apply_basis, A.basis_mul_coordinates, Int.cast_sum, Int.cast_mul]

private theorem reduce_pow (H : ℕ) (x : 𝓞 K) (n : ℕ) : A.reduce H (x^n) = A.coordinatePow H (A.reduce H x) n := by
  induction n with
  | zero => rw [pow_zero]; exact A.reduce_one H
  | succ n ih => rw [pow_succ, A.reduce_mul, ih]; rfl

/-- Transport the ring laws to the executable coordinate operations. -/
@[reducible] private def residueRing (H : ℕ) : CommRing (Coordinates A.degree H) := by
  letI : One (Coordinates A.degree H) := ⟨A.coordinateOne H⟩
  letI : Mul (Coordinates A.degree H) := ⟨A.coordinateMul H⟩
  letI : Pow (Coordinates A.degree H) ℕ := ⟨A.coordinatePow H⟩
  letI : NatCast (Coordinates A.degree H) := ⟨fun n ↦ n • A.coordinateOne H⟩
  letI : IntCast (Coordinates A.degree H) := ⟨fun n ↦ n • A.coordinateOne H⟩
  apply (A.reduce_surjective H).commRing (A.reduce H) (A.reduce_zero H) (A.reduce_one H)
    (A.reduce_add H) (A.reduce_mul H) (A.reduce_neg H) (A.reduce_sub H) (A.reduce_nsmul H)
    (A.reduce_zsmul H) (A.reduce_pow H)
  · intro n
    change A.reduce H (n : 𝓞 K) = n • A.coordinateOne H
    rw [← nsmul_one, A.reduce_nsmul, A.reduce_one]
  · intro n
    change A.reduce H (n : 𝓞 K) = n • A.coordinateOne H
    rw [← zsmul_one, A.reduce_zsmul, A.reduce_one]

private theorem reduce_eq_zero_iff (H : ℕ) (x : 𝓞 K) :
    A.reduce H x = 0 ↔ x ∈ boundedIdealModulus K H := by
  let M := H.factorial^2
  constructor
  · intro hx
    have hd (i : Fin A.degree) : (M : ℤ) ∣ A.basis.equivFun x i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
      rw [← A.reduce_apply_basis H x i]
      exact congrFun hx i
    choose y hy using hd
    have hm : x = (M : ℤ) • A.basis.equivFun.symm y := by
      apply A.basis.equivFun.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact funext hy
    apply Ideal.mem_span_singleton.mpr
    exact ⟨A.basis.equivFun.symm y,by simpa only [zsmul_eq_mul, Int.cast_natCast] using hm⟩
  · intro hx
    obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp hx
    change x = (M : 𝓞 K)*y at hy
    rw [hy, ← nsmul_eq_mul, A.reduce_nsmul]
    funext i
    change M • A.reduce H y i = (0 : ZMod (H.factorial^2))
    simp only [nsmul_eq_mul, M, ZMod.natCast_self, zero_mul]

/-- The executable residue arithmetic generated from an integral basis. -/
def toExplicitIdealArithmetic : ExplicitIdealArithmetic.{u,0} K where
  residue := Coordinates A.degree
  ring := A.residueRing
  enumeration H := by
    letI : NeZero (H.factorial^2) := ⟨pow_ne_zero _ (Nat.factorial_ne_zero _)⟩
    infer_instance
  decidableEq _ := inferInstance
  reduction H := by
    letI : CommRing (Coordinates A.degree H) := A.residueRing H
    let f : 𝓞 K →+* Coordinates A.degree H :=
      { toFun := A.reduce H
        map_one' := A.reduce_one H
        map_mul' := A.reduce_mul H
        map_zero' := A.reduce_zero H
        map_add' := A.reduce_add H }
    exact ⟨f,A.reduce_surjective H,Ideal.ext fun x ↦ A.reduce_eq_zero_iff H x⟩
  degree := A.degree
  degree_eq := A.degree_eq

/-- Compute enclosures directly from the explicit integral basis. -/
def approximate (integral : Bool) (ε : ℚ) (hε : 0 < ε) : IdealDensityEnclosures :=
  A.toExplicitIdealArithmetic.approximate integral ε hε

/-- The two density extrema are computable with arbitrary rational
precision from the stated number-field presentation. -/
theorem approximate_spec (integral : Bool) (ε : ℚ) (hε : 0 < ε) :
    let B := A.approximate integral ε hε
    B.Sound K integral ∧ B.naturalUpper - B.naturalLower < ε ∧ B.upperUpper - B.upperLower < ε :=
  A.toExplicitIdealArithmetic.approximate_spec integral ε hε

end IntegralBasisIdealArithmetic
end GRHArticle.ProgressionFree.NumberFieldIdeals
