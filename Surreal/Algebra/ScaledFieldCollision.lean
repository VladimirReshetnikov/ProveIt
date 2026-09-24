import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Scaled-field collision in rings and modules

The full `osq:lem:collision` and `osq:eq:collision`. If a scalar multiple
mL of a subfield lies in a possibly nonunital subring, a collision between
the images of mx and my forces the image of m² to vanish. The same finite
identity acts directly on modules, bounding their cardinality without
passing to an endomorphism ring. Targets need not be commutative or reduced,
and maps need not preserve one.
-/

universe u v w
namespace Surreal.ScaledFieldCollision
noncomputable section

variable {F : Type u} [Field F]

/-- The scalar multiple of a subfield element, retained in the specified nonunital subring. -/
def scaled (A : NonUnitalSubring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) (x : L) : A := ⟨m * x, h x⟩

@[simp] theorem scaled_value (A : NonUnitalSubring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) (x : L) : (scaled A L m h x : F) = m * x := rfl

/-- The finite collision certificate holds inside the possibly nonunital source ring. -/
theorem collision_identity (A : NonUnitalSubring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) (x y : L) (hxy : x ≠ y) :
    (scaled A L m h x - scaled A L m h y) * scaled A L m h (x - y)⁻¹ =
      scaled A L m h 1 * scaled A L m h 1 := by
  have hv : (x : F) - (y : F) ≠ 0 := sub_ne_zero.mpr (Subtype.val_injective.ne hxy)
  apply Subtype.ext
  change (m * (x : F) - m * (y : F)) * (m * ((x : F) - (y : F))⁻¹) = (m * 1) * (m * 1)
  field_simp

/-- A nonzero square image makes the entire scaled subfield inject into any ring target. -/
theorem hom_injective (A : NonUnitalSubring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) {S : Type v} [NonUnitalRing S]
    (φ : A →ₙ+* S) (hφ : φ (scaled A L m h 1 * scaled A L m h 1) ≠ 0) :
    Function.Injective (fun x : L => φ (scaled A L m h x)) := by
  intro x y he
  change φ (scaled A L m h x) = φ (scaled A L m h y) at he
  by_contra hxy
  apply hφ
  rw [← collision_identity A L m h x y hxy, map_mul, map_sub, he, sub_self, zero_mul]

/-- The cardinal bound from the ring collision argument is valid across different universes. -/
theorem hom_cardinal_bound (A : NonUnitalSubring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) {S : Type v} [NonUnitalRing S]
    (φ : A →ₙ+* S) (hφ : φ (scaled A L m h 1 * scaled A L m h 1) ≠ 0) :
    Cardinal.lift.{v} (Cardinal.mk L) ≤ Cardinal.lift.{u} (Cardinal.mk S) :=
  Cardinal.lift_mk_le_lift_mk_of_injective (hom_injective A L m h φ hφ)

/-- A target of smaller cardinality forces the square image to be zero. -/
theorem hom_square_eq_zero_of_cardinal_lt (A : NonUnitalSubring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) {S : Type v} [NonUnitalRing S]
    (φ : A →ₙ+* S)
    (hcard : Cardinal.lift.{u} (Cardinal.mk S) < Cardinal.lift.{v} (Cardinal.mk L)) :
    φ (scaled A L m h 1 * scaled A L m h 1) = 0 := by
  by_contra hn
  exact (not_lt_of_ge (hom_cardinal_bound A L m h φ hn)) hcard

/-- A subfield larger than the small-target universe forces square images to vanish. -/
theorem hom_square_eq_zero_of_not_small (A : NonUnitalSubring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) {S : Type v} [NonUnitalRing S] [Small.{w} S]
    (φ : A →ₙ+* S) (hL : ¬ Small.{w} L) :
    φ (scaled A L m h 1 * scaled A L m h 1) = 0 := by
  by_contra hn
  exact hL (small_of_injective (hom_injective A L m h φ hn))

/-- The scaled element with the native unital subring type needed for module scalars. -/
def scaledInSubring (A : Subring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) (x : L) : A := ⟨m * x, h x⟩

/-- The same collision identity in a native unital subring. -/
theorem subring_collision_identity (A : Subring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) (x y : L) (hxy : x ≠ y) :
    (scaledInSubring A L m h x - scaledInSubring A L m h y) * scaledInSubring A L m h (x - y)⁻¹ =
      scaledInSubring A L m h 1 * scaledInSubring A L m h 1 := by
  apply Subtype.ext
  exact congrArg Subtype.val (collision_identity A.toNonUnitalSubring L m h x y hxy)

/-- The module collision argument uses the module's own elements, not its endomorphism ring. -/
theorem smul_injective (A : Subring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) {M : Type v} [AddCommGroup M] [Module A M]
    (v : M) (hv : (scaledInSubring A L m h 1 * scaledInSubring A L m h 1) • v ≠ 0) :
    Function.Injective (fun x : L => scaledInSubring A L m h x • v) := by
  intro x y he
  change scaledInSubring A L m h x • v = scaledInSubring A L m h y • v at he
  by_contra hxy
  apply hv
  rw [← subring_collision_identity A L m h x y hxy, mul_comm, mul_smul,
    sub_smul, he, sub_self, smul_zero]

/-- A nonzero square action bounds the cardinality of the subfield by that of the module. -/
theorem smul_cardinal_bound (A : Subring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) {M : Type v} [AddCommGroup M] [Module A M]
    (v : M) (hv : (scaledInSubring A L m h 1 * scaledInSubring A L m h 1) • v ≠ 0) :
    Cardinal.lift.{v} (Cardinal.mk L) ≤ Cardinal.lift.{u} (Cardinal.mk M) :=
  Cardinal.lift_mk_le_lift_mk_of_injective (smul_injective A L m h v hv)

/-- A module smaller than the scaled subfield is annihilated by the square scalar. -/
theorem square_smul_eq_zero_of_cardinal_lt (A : Subring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) {M : Type v} [AddCommGroup M] [Module A M]
    (hcard : Cardinal.lift.{u} (Cardinal.mk M) < Cardinal.lift.{v} (Cardinal.mk L)) (v : M) :
    (scaledInSubring A L m h 1 * scaledInSubring A L m h 1) • v = 0 := by
  by_contra hn
  exact (not_lt_of_ge (smul_cardinal_bound A L m h v hn)) hcard

/-- The same small-universe obstruction annihilates each vector directly. -/
theorem square_smul_eq_zero_of_not_small (A : Subring F) (L : Subfield F) (m : F)
    (h : ∀ x : L, m * (x : F) ∈ A) {M : Type v} [AddCommGroup M] [Module A M] [Small.{w} M]
    (hL : ¬ Small.{w} L) (v : M) :
    (scaledInSubring A L m h 1 * scaledInSubring A L m h 1) • v = 0 := by
  by_contra hn
  exact hL (small_of_injective (smul_injective A L m h v hn))

end
end Surreal.ScaledFieldCollision
