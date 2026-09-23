import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Inverse limits of ordinary integer congruences

Prerequisites for the profinite clause of `odg:eq:profinite`. Positive
moduli are ordered by reverse divisibility, so arrows are reduction maps.
The inverse limit uses Mathlib's ring of compatible sections, and its cone
is proved to be a limit in `CommRingCat`. The construction and the comparison
of two such limits allow rings in different universes.
-/

universe u v w

namespace Surreal.IntegerCongruenceLimit

open CategoryTheory CategoryTheory.Limits

/-- A positive ordinary modulus, used as an index for congruence quotients. -/
structure Modulus where
  val : ℕ
  positive : 0 < val

/-- Arrows go from a modulus to each of its positive divisors. -/
instance : Preorder Modulus where
  le m n := n.val ∣ m.val
  le_refl _ := dvd_refl _
  le_trans _ _ _ h₁ h₂ := dvd_trans h₂ h₁

instance : Nonempty Modulus := ⟨⟨1, Nat.zero_lt_one⟩⟩

variable (R : Type u) [CommRing R]

/-- The ideal of multiples of an ordinary positive modulus. -/
def ideal (n : Modulus) : Ideal R := Ideal.span {(n.val : R)}

/-- Divisibility of ordinary moduli gives the inclusion needed for reduction. -/
theorem ideal_le {m n : Modulus} (h : m ≤ n) : ideal R m ≤ ideal R n := by
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact map_dvd (Nat.castRingHom R) (show n.val ∣ m.val from h)

/-- The diagram of quotient rings with all ordinary reduction maps. -/
@[reducible] def diagram : Modulus ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (R ⧸ ideal R n)
  map f := CommRingCat.ofHom (Ideal.Quotient.factor (ideal_le R (leOfHom f)))
  map_id n := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The inverse-limit ring is Mathlib's ring of compatible sections of the quotient diagram. -/
abbrev Completion :=
  ↥(RingCat.sectionsSubring (diagram R ⋙ forget₂ CommRingCat RingCat))

instance : CommRing (Completion R) :=
  @Subring.toCommRing (∀ n, R ⧸ ideal R n) inferInstance
    (RingCat.sectionsSubring (diagram R ⋙ forget₂ CommRingCat RingCat))

/-- The projection to one congruence quotient. -/
def projection (n : Modulus) : Completion R →+* R ⧸ ideal R n where
  toFun x := x.val n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Every element of the inverse limit satisfies every reduction identity. -/
theorem compatible (x : Completion R) {m n : Modulus} (h : m ≤ n) :
    Ideal.Quotient.factor (ideal_le R h) (projection R m x) = projection R n x :=
  x.property (homOfLE h)

/-- The canonical map records all ordinary congruence classes. -/
def of : R →+* Completion R where
  toFun r := ⟨fun n => Ideal.Quotient.mk (ideal R n) r, fun _ => rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem projection_of (n : Modulus) (r : R) :
    projection R n (of R r) = Ideal.Quotient.mk (ideal R n) r := rfl

/-- Congruence projections determine elements of the inverse limit. -/
@[ext] theorem ext {x y : Completion R} (h : ∀ n, projection R n x = projection R n y) : x = y :=
  Subtype.ext (funext h)

/-- The kernel of the canonical map is the intersection of the ordinary congruence ideals. -/
theorem of_eq_zero_iff (r : R) : of R r = 0 ↔ r ∈ ⨅ n, ideal R n := by
  rw [Ideal.mem_iInf]
  constructor
  · intro h n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [projection_of, map_zero] using congrArg (projection R n) h
  · intro h
    apply ext R
    intro n
    rw [projection_of, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h n)

/-- The canonical cone from the compatible-section ring. -/
def cone : Cone (diagram R) where
  pt := CommRingCat.of (Completion R)
  π :=
    { app := fun n => CommRingCat.ofHom (projection R n)
      naturality := fun m n f => by
        ext x
        exact (compatible R x (leOfHom f)).symm }

/-- Mathlib's universal property verifies that this is the actual inverse limit of the diagram. -/
def isLimit : IsLimit (cone R) where
  lift c := CommRingCat.ofHom
    { toFun := fun x => ⟨fun n => (c.π.app n).hom x, fun f => by
        exact (congrArg (fun g => g.hom x) (c.π.naturality f)).symm⟩
      map_one' := Subtype.ext (funext fun n => (c.π.app n).hom.map_one)
      map_mul' x y := Subtype.ext (funext fun n => (c.π.app n).hom.map_mul x y)
      map_zero' := Subtype.ext (funext fun n => (c.π.app n).hom.map_zero)
      map_add' x y := Subtype.ext (funext fun n => (c.π.app n).hom.map_add x y) }
  fac _ _ := rfl
  uniq c f h := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply Subtype.ext
    funext n
    exact congrArg (fun g => g.hom x) (h n)

variable {R} {S : Type v} [CommRing S]
    (e : ∀ n, R ⧸ ideal R n ≃+* S ⧸ ideal S n)
    (he : ∀ {m n} (h : m ≤ n) x,
      e n (Ideal.Quotient.factor (ideal_le R h) x) =
        Ideal.Quotient.factor (ideal_le S h) (e m x))

/-- Compatible isomorphisms of all quotient rings induce an isomorphism of the inverse limits. -/
def congr : Completion R ≃+* Completion S where
  toFun x := ⟨fun n => e n (x.val n), fun {m n} f => by
    change Ideal.Quotient.factor (ideal_le S (leOfHom f)) (e m (projection R m x)) = _
    rw [← he (leOfHom f), compatible R x (leOfHom f)]
    rfl⟩
  invFun y := ⟨fun n => (e n).symm (y.val n), fun {m n} f => by
    change Ideal.Quotient.factor (ideal_le R (leOfHom f)) ((e m).symm (projection S m y)) =
      (e n).symm (projection S n y)
    apply (e n).injective
    rw [he (leOfHom f), RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact compatible S y (leOfHom f)⟩
  left_inv x := Subtype.ext (funext fun n => (e n).symm_apply_apply _)
  right_inv y := Subtype.ext (funext fun n => (e n).apply_symm_apply _)
  map_mul' x y := Subtype.ext (funext fun n => (e n).map_mul (x.val n) (y.val n))
  map_add' x y := Subtype.ext (funext fun n => (e n).map_add (x.val n) (y.val n))

@[simp] theorem projection_congr (n : Modulus) (x : Completion R) :
    projection S n (congr e he x) = e n (projection R n x) := rfl

end Surreal.IntegerCongruenceLimit
