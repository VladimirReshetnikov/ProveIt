import Surreal.Foundations.OmnificTelescope
import Surreal.Foundations.OmnificFiniteQuotients
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Universal small targets of the actual omnific integers

The real omnific instance of `osq:thm:universal`. The telescope supplies
finite certificates inside the purely infinite ideal. Non-small intervals
of subordinate exponents force collisions in arbitrary small targets,
including noncommutative and nonunital rings. Common monomial divisors
then kill the whole ideal. Smallness is relative to the birthday universe.
-/

universe u v w
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Any small-valued function on positive exponents collides below a prescribed scale. -/
theorem small_positive_scale_collision {T : Type v} [Small.{u} T]
    (f : Set.Ioi (0 : SignSequence.{u}) → T) (c : SignSequence.{u}) (hc : 0 < c) :
    ∃ (a b : SignSequence.{u}) (hb : 0 < b) (hba : b < a),
      (∀ n : ℕ, (n : SignSequence) * a < c) ∧ f ⟨a, hb.trans hba⟩ = f ⟨b, hb⟩ := by
  obtain ⟨h, hh, hs⟩ := small_subordinate_scale (fun _ : PUnit => c) (fun _ => hc)
  let g : Set.Ioo (0 : SignSequence.{u}) h → T := fun a => f ⟨a.val, a.property.1⟩
  have hn : ¬ Function.Injective g := fun hi => positive_interval_not_small h hh (small_of_injective hi)
  obtain ⟨x, y, he, hxy⟩ := Function.not_injective_iff.mp hn
  have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨y.val, x.val, x.property.1, hlt,
      fun n => interval_subordinate (fun _ : PUnit => c) h hs y.val y.property PUnit.unit n,
      he.symm⟩
  · exact ⟨x.val, y.val, y.property.1, hgt,
      fun n => interval_subordinate (fun _ : PUnit => c) h hs x.val x.property PUnit.unit n,
      he⟩

/-- The purely infinite ideal, viewed as its native nonunital ring. -/
def omnificPurelyInfiniteSubring : NonUnitalSubring OmnificInteger.{u} where
  carrier := omnificPurelyInfiniteIdeal
  zero_mem' := omnificPurelyInfiniteIdeal.zero_mem
  add_mem' := omnificPurelyInfiniteIdeal.add_mem
  neg_mem' := omnificPurelyInfiniteIdeal.neg_mem
  mul_mem' := fun _ hy => omnificPurelyInfiniteIdeal.mul_mem_left _ hy

/-- A positive monomial as an element of the nonunital purely infinite ring. -/
def purelyInfiniteMonomial (a : SignSequence.{u}) (ha : 0 < a) : omnificPurelyInfiniteSubring.{u} :=
  ⟨omnificMonomial a ha, omnificMonomial_mem_purelyInfinite a ha⟩

/-- Every nonunital map from the purely infinite ring to a small ring kills positive monomials. -/
theorem purelyInfinite_small_hom_monomial {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : omnificPurelyInfiniteSubring.{u} →ₙ+* S) (c : SignSequence.{u}) (hc : 0 < c) :
    φ (purelyInfiniteMonomial c hc) = 0 := by
  obtain ⟨a, b, hb, hba, hac, he⟩ := small_positive_scale_collision
    (fun a => φ (purelyInfiniteMonomial a.val a.property)) c hc
  obtain ⟨q, hq, hcert⟩ := omnific_monomial_difference_certificate c a b hb hba hac
  have hcert' : (purelyInfiniteMonomial a (hb.trans hba) - purelyInfiniteMonomial b hb) *
      (⟨q, hq⟩ : omnificPurelyInfiniteSubring.{u}) = purelyInfiniteMonomial c hc :=
    Subtype.ext hcert
  rw [← hcert', map_mul, map_sub, he, sub_self, zero_mul]

/-- Every nonunital small-target map defined just on the purely infinite ring is zero. -/
theorem purelyInfinite_small_hom_eq_zero {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : omnificPurelyInfiniteSubring.{u} →ₙ+* S) (x : omnificPurelyInfiniteSubring.{u}) : φ x = 0 := by
  obtain ⟨a, ha, hd⟩ := omnific_common_monomial_divisor
    (fun _ : PUnit => x.val) (fun _ => x.property)
  obtain ⟨q, hq, he⟩ := hd PUnit.unit
  have hx : x = purelyInfiniteMonomial a ha * (⟨q, hq⟩ : omnificPurelyInfiniteSubring.{u}) :=
    Subtype.ext he
  rw [hx, map_mul, purelyInfinite_small_hom_monomial, zero_mul]

/-- Every additive multiplicative map from the omnific ring to a small ring kills its infinite ideal. -/
theorem omnific_small_hom_purelyInfinite {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : OmnificInteger.{u} →ₙ+* S) (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    φ x = 0 :=
  purelyInfinite_small_hom_eq_zero (φ.comp { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }) ⟨x, hx⟩

/-- Small-target nonunital homomorphisms depend only on the ordinary integer constant. -/
theorem omnific_small_hom_eq_constant {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : OmnificInteger.{u} →ₙ+* S) (x : OmnificInteger.{u}) :
    φ x = φ (omnificIntCast (omnificConstantCoeff x)) := by
  obtain ⟨j, hj, he⟩ := omnific_constant_decomposition x
  calc
    φ x = φ (omnificIntCast (omnificConstantCoeff x)) + φ j := by rw [← map_add, ← he]
    _ = φ (omnificIntCast (omnificConstantCoeff x)) := by
      rw [omnific_small_hom_purelyInfinite φ j hj, _root_.add_zero]

/-- The unique nonunital factor is restriction to the ordinary integer constants. -/
theorem omnific_small_hom_factors_unique {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : OmnificInteger.{u} →ₙ+* S) :
    ∃! ψ : ℤ →ₙ+* S, φ = ψ.comp omnificConstantCoeff.toNonUnitalRingHom := by
  refine ⟨φ.comp omnificIntCast.toNonUnitalRingHom, ?_, ?_⟩
  · ext x
    exact omnific_small_hom_eq_constant φ x
  · intro ψ hψ
    ext n
    change ψ n = φ (omnificIntCast n)
    have he := congrArg (fun f : OmnificInteger.{u} →ₙ+* S => f (omnificIntCast n)) hψ
    change φ (omnificIntCast n) = ψ (omnificConstantCoeff (omnificIntCast n)) at he
    simpa only [omnificConstantCoeff_intCast] using he.symm

/-- For unital small-target maps the value is the target's integer cast of the constant. -/
theorem omnific_small_ringHom_eq_constant {S : Type v} [Ring S] [Small.{u} S]
    (φ : OmnificInteger.{u} →+* S) (x : OmnificInteger.{u}) :
    φ x = (omnificConstantCoeff x : S) :=
  (omnific_small_hom_eq_constant φ.toNonUnitalRingHom x).trans (omnific_hom_intCast φ _)

/-- Restriction to constants and composition with constant extraction are inverse bijections. -/
def omnificSmallRingHomEquiv (S : Type v) [Ring S] [Small.{u} S] :
    (OmnificInteger.{u} →+* S) ≃ (ℤ →+* S) where
  toFun φ := φ.comp omnificIntCast
  invFun ψ := ψ.comp omnificConstantCoeff
  left_inv φ := by
    ext x
    exact (omnific_small_hom_eq_constant φ.toNonUnitalRingHom x).symm
  right_inv ψ := by
    ext n
    simp only [RingHom.comp_apply, omnificConstantCoeff_intCast]

/-- The correspondence commutes with every unital change of small target. -/
theorem omnificSmallRingHomEquiv_natural {S : Type v} {T : Type w}
    [Ring S] [Ring T] [Small.{u} S] [Small.{u} T]
    (f : S →+* T) (φ : OmnificInteger.{u} →+* S) :
    omnificSmallRingHomEquiv T (f.comp φ) = f.comp (omnificSmallRingHomEquiv S φ) := rfl

/-- Positive monomials annihilate every vector of a small unital module. -/
theorem omnific_monomial_smul_small {M : Type v} [AddCommGroup M] [Module OmnificInteger.{u} M]
    [Small.{u} M] (c : SignSequence.{u}) (hc : 0 < c) (v : M) :
    omnificMonomial c hc • v = 0 := by
  obtain ⟨a, b, hb, hba, hac, he⟩ := small_positive_scale_collision
    (fun a => omnificMonomial a.val a.property • v) c hc
  obtain ⟨q, _, hcert⟩ := omnific_monomial_difference_certificate c a b hb hba hac
  rw [← hcert, mul_comm, mul_smul, sub_smul, he, sub_self, smul_zero]

/-- The entire purely infinite ideal annihilates each small unital module. -/
theorem omnific_purelyInfinite_smul_small {M : Type v} [AddCommGroup M]
    [Module OmnificInteger.{u} M] [Small.{u} M] (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (v : M) : x • v = 0 := by
  obtain ⟨a, ha, hd⟩ := omnific_common_monomial_divisor (fun _ : PUnit => x) (fun _ => hx)
  obtain ⟨q, _, he⟩ := hd PUnit.unit
  rw [he, mul_smul, omnific_monomial_smul_small]

/-- The action on every small module is exactly the action of the integer constant. -/
theorem omnific_smul_small_eq_constant {M : Type v} [AddCommGroup M]
    [Module OmnificInteger.{u} M] [Small.{u} M] (x : OmnificInteger.{u}) (v : M) :
    x • v = omnificConstantCoeff x • v := by
  obtain ⟨j, hj, he⟩ := omnific_constant_decomposition x
  calc
    x • v = (omnificIntCast (omnificConstantCoeff x) + j) • v := congrArg (· • v) he
    _ = omnificIntCast (omnificConstantCoeff x) • v := by
      rw [add_smul, omnific_purelyInfinite_smul_small j hj, _root_.add_zero]
    _ = omnificConstantCoeff x • v := by
      have hi (n : ℤ) : omnificIntCast.{u} n = (n : OmnificInteger.{u}) := map_intCast _ _
      rw [hi, Int.cast_smul_eq_zsmul]

end
end Surreal.Foundations.SignSequence
