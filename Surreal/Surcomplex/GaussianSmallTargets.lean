import Surreal.Surcomplex.GaussianPurelyInfiniteIdeal
import Surreal.Foundations.OmnificSmallTargets

/-!
# Universal small targets of Gaussian omnific integers

All four Gaussian clauses of `osq:thm:universal`. Nonunital maps on the
purely infinite ring vanish by real monomial restriction and common
monomial division. Maps from the full ring factor uniquely through the
Gaussian constant, and small modules have the same constant action.
-/

universe u v w
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The Gaussian purely infinite ideal with its native nonunital ring structure. -/
def gaussianPurelyInfiniteSubring : NonUnitalSubring GaussianOmnificInteger.{u} where
  carrier := gaussianOmnificPurelyInfiniteIdeal
  zero_mem' := gaussianOmnificPurelyInfiniteIdeal.zero_mem
  add_mem' := gaussianOmnificPurelyInfiniteIdeal.add_mem
  neg_mem' := gaussianOmnificPurelyInfiniteIdeal.neg_mem
  mul_mem' := fun _ hy => gaussianOmnificPurelyInfiniteIdeal.mul_mem_left _ hy

/-- Real purely infinite elements embed in the Gaussian purely infinite ring. -/
def purelyInfiniteToGaussian : SignSequence.omnificPurelyInfiniteSubring.{u} →ₙ+*
    gaussianPurelyInfiniteSubring.{u} where
  toFun x := ⟨omnificToGaussian x.val, omnificToGaussian_mem_purelyInfinite x.val x.property⟩
  map_zero' := Subtype.ext (map_zero omnificToGaussian)
  map_add' x y := Subtype.ext (map_add omnificToGaussian x.val y.val)
  map_mul' x y := Subtype.ext (map_mul omnificToGaussian x.val y.val)

/-- Every map defined just on the Gaussian purely infinite ring has zero image in a small ring. -/
theorem gaussianPurelyInfinite_small_hom_eq_zero {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : gaussianPurelyInfiniteSubring.{u} →ₙ+* S) (x : gaussianPurelyInfiniteSubring.{u}) : φ x = 0 := by
  obtain ⟨a, ha, hd⟩ := gaussianOmnific_common_monomial_divisor
    (fun _ : PUnit => x.val) (fun _ => x.property)
  obtain ⟨q, hq, he⟩ := hd PUnit.unit
  have hx : x = purelyInfiniteToGaussian (SignSequence.purelyInfiniteMonomial a ha) *
      (⟨q, hq⟩ : gaussianPurelyInfiniteSubring.{u}) := Subtype.ext he
  have hz := SignSequence.purelyInfinite_small_hom_eq_zero (φ.comp purelyInfiniteToGaussian)
    (SignSequence.purelyInfiniteMonomial a ha)
  change φ (purelyInfiniteToGaussian (SignSequence.purelyInfiniteMonomial a ha)) = 0 at hz
  rw [hx, map_mul, hz, zero_mul]

/-- Every small-target nonunital map on the Gaussian omnific ring kills its purely infinite ideal. -/
theorem gaussianOmnific_small_hom_purelyInfinite {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →ₙ+* S) (x : GaussianOmnificInteger.{u})
    (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal) : φ x = 0 :=
  gaussianPurelyInfinite_small_hom_eq_zero
    (φ.comp {
      toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }) ⟨x, hx⟩

/-- The value of a Gaussian omnific element depends only on its ordinary Gaussian constant. -/
theorem gaussianOmnific_small_hom_eq_constant {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →ₙ+* S) (x : GaussianOmnificInteger.{u}) :
    φ x = φ (gaussianOmnificConstants.{u} (gaussianOmnificConstantCoeff.{u} x)) := by
  have he := gaussianOmnific_small_hom_purelyInfinite φ _ (gaussianOmnific_constant_remainder x)
  rw [map_sub, sub_eq_zero] at he
  exact he

/-- Restriction to ordinary Gaussian constants is the unique factor, also for nonunital maps. -/
theorem gaussianOmnific_small_hom_factors_unique {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →ₙ+* S) :
    ∃! ψ : GaussianInt →ₙ+* S, φ = ψ.comp gaussianOmnificConstantCoeff.{u}.toNonUnitalRingHom := by
  refine ⟨φ.comp gaussianOmnificConstants.{u}.toNonUnitalRingHom, ?_, ?_⟩
  · ext x
    exact gaussianOmnific_small_hom_eq_constant φ x
  · intro ψ hψ
    ext n
    change ψ n = φ (gaussianOmnificConstants.{u} n)
    have he := congrArg (fun f : GaussianOmnificInteger.{u} →ₙ+* S => f (gaussianOmnificConstants.{u} n)) hψ
    change φ (gaussianOmnificConstants.{u} n) = ψ (gaussianOmnificConstantCoeff.{u} (gaussianOmnificConstants.{u} n)) at he
    simpa only [gaussianOmnificConstantCoeff_constants] using he.symm

/-- Unital small-target maps correspond precisely to unital maps from the Gaussian integers. -/
def gaussianOmnificSmallRingHomEquiv (S : Type v) [Ring S] [Small.{u} S] :
    (GaussianOmnificInteger.{u} →+* S) ≃ (GaussianInt →+* S) where
  toFun φ := φ.comp gaussianOmnificConstants.{u}
  invFun ψ := ψ.comp gaussianOmnificConstantCoeff.{u}
  left_inv φ := by
    ext x
    exact (gaussianOmnific_small_hom_eq_constant φ.toNonUnitalRingHom x).symm
  right_inv ψ := by
    apply RingHom.ext
    intro n
    simp only [RingHom.comp_apply, gaussianOmnificConstantCoeff_constants]

/-- The Gaussian constant correspondence is natural in the small target ring. -/
theorem gaussianOmnificSmallRingHomEquiv_natural {S : Type v} {T : Type w}
    [Ring S] [Ring T] [Small.{u} S] [Small.{u} T]
    (f : S →+* T) (φ : GaussianOmnificInteger.{u} →+* S) :
    gaussianOmnificSmallRingHomEquiv T (f.comp φ) = f.comp (gaussianOmnificSmallRingHomEquiv S φ) := rfl

/-- Real positive monomials annihilate each vector of every small Gaussian omnific module. -/
theorem gaussianOmnific_real_monomial_smul_small {M : Type v} [AddCommGroup M]
    [Module GaussianOmnificInteger.{u} M] [Small.{u} M]
    (a : SignSequence.{u}) (ha : 0 < a) (v : M) :
    omnificToGaussian (SignSequence.omnificMonomial a ha) • v = 0 := by
  letI : Module SignSequence.OmnificInteger.{u} M := Module.compHom M omnificToGaussian
  exact SignSequence.omnific_monomial_smul_small a ha v

/-- The whole Gaussian infinite ideal, including imaginary coefficients, annihilates small modules. -/
theorem gaussianOmnific_purelyInfinite_smul_small {M : Type v} [AddCommGroup M]
    [Module GaussianOmnificInteger.{u} M] [Small.{u} M] (x : GaussianOmnificInteger.{u})
    (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal) (v : M) : x • v = 0 := by
  obtain ⟨a, ha, hd⟩ := gaussianOmnific_common_monomial_divisor (fun _ : PUnit => x) (fun _ => hx)
  obtain ⟨q, _, he⟩ := hd PUnit.unit
  rw [he, mul_smul, gaussianOmnific_real_monomial_smul_small]

/-- Every small Gaussian omnific module has exactly its ordinary Gaussian constant action. -/
theorem gaussianOmnific_smul_small_eq_constant {M : Type v} [AddCommGroup M]
    [Module GaussianOmnificInteger.{u} M] [Small.{u} M] (x : GaussianOmnificInteger.{u}) (v : M) :
    x • v = gaussianOmnificConstants.{u} (gaussianOmnificConstantCoeff.{u} x) • v := by
  have he := gaussianOmnific_purelyInfinite_smul_small _ (gaussianOmnific_constant_remainder x) v
  rwa [sub_smul, sub_eq_zero] at he

end
end Surreal.Surcomplex
