import Surreal.Algebra.ProductNormForm
import Surreal.Algebra.SeparableNormRigidity

/-!
# Constant-coordinate rigidity for finite products of separable fields

The finite étale algebra step of `odg:dec:thm:etale`. Every factor norm is
a unit at a nonzero constant product-norm level. Field norm rigidity then
makes all component coordinates constant, and the inverse basis change
recovers the original coordinates. Neither a product basis nor equal
component dimensions is assumed.
-/

namespace Surreal.NormForm

open Module

noncomputable section

/-- Finite products of finite separable extensions have constant norm fibers in a
constant-unit algebra, in every basis. -/
theorem product_coordinates_constant {K E B H J : Type*}
    [Field K] [Infinite K] [Field E] [Algebra K E] [IsAlgClosed E]
    [CommRing B] [Algebra E B] [Fintype H] [DecidableEq H]
    {L : H → Type*} [∀ h, Field (L h)] [∀ h, Algebra K (L h)]
    [∀ h, Module.Finite K (L h)] [∀ h, Algebra.IsSeparable K (L h)]
    {ι : H → Type*} [∀ h, Fintype (ι h)] [∀ h, DecidableEq (ι h)]
    [Fintype J] [DecidableEq J]
    (ct : B →ₐ[E] E) (hunit : ∀ z : B, IsUnit z → z = algebraMap E B (ct z))
    (b : Basis J K (∀ h, L h)) (bs : ∀ h, Basis (ι h) K (L h))
    (c : E) (hc : c ≠ 0) (x : J → B)
    (hx : (polynomial b).eval₂ ((algebraMap E B).comp (algebraMap K E)) x = algebraMap E B c) :
    ∀ j, x j = algebraMap E B (ct (x j)) := by
  let φ := (algebraMap E B).comp (algebraMap K E)
  let y := componentCoordinates b bs φ x
  let n := fun h => (polynomial (bs h)).eval₂ φ (y h)
  have hp : ∏ h, n h = algebraMap E B c := by
    rw [polynomial_pi b bs, MvPolynomial.eval₂_prod] at hx
    simpa only [eval₂_componentPolynomial] using hx
  have hu (h : H) : IsUnit (n h) :=
    (IsUnit.prod_univ_iff.mp (hp.symm ▸ (isUnit_iff_ne_zero.mpr hc).map (algebraMap E B))) h
  have hy (h : H) : ∀ i, y h i = algebraMap E B (ct (y h i)) := by
    apply coordinates_constant ct hunit (bs h) (ct (n h))
      (isUnit_iff_ne_zero.mp ((hu h).map ct.toRingHom)) (y h)
    exact hunit (n h) (hu h)
  have he : x = fun j => algebraMap E B (ct (x j)) := by
    apply componentCoordinates_injective b bs φ
    funext s
    have h := hy s.1 s.2
    simpa only [y, componentCoordinates, φ, RingHom.comp_apply, map_sum, map_mul,
      AlgHom.commutes, Algebra.algebraMap_self_apply] using h
  exact fun j => congrFun he j

/-- Component bases can be chosen from finite-dimensionality; callers supply only the
basis of the finite product algebra. -/
theorem etale_coordinates_constant {K E B H J : Type*}
    [Field K] [Infinite K] [Field E] [Algebra K E] [IsAlgClosed E]
    [CommRing B] [Algebra E B] [Fintype H] [DecidableEq H]
    {L : H → Type*} [∀ h, Field (L h)] [∀ h, Algebra K (L h)]
    [∀ h, Module.Finite K (L h)] [∀ h, Algebra.IsSeparable K (L h)]
    [Fintype J] [DecidableEq J]
    (ct : B →ₐ[E] E) (hunit : ∀ z : B, IsUnit z → z = algebraMap E B (ct z))
    (b : Basis J K (∀ h, L h)) (c : E) (hc : c ≠ 0) (x : J → B)
    (hx : (polynomial b).eval₂ ((algebraMap E B).comp (algebraMap K E)) x = algebraMap E B c) :
    ∀ j, x j = algebraMap E B (ct (x j)) :=
  product_coordinates_constant ct hunit b (fun h => Module.finBasis K (L h)) c hc x hx

/-- In an intermediate subring, constant-coordinate rigidity descends through its intersection
with the constant field. The subring need not be closed under constant extraction. -/
theorem etale_intermediate_ring_rigidity {K E B H J : Type*}
    [Field K] [Infinite K] [Field E] [Algebra K E] [IsAlgClosed E]
    [CommRing B] [Algebra E B] [Fintype H] [DecidableEq H]
    {L : H → Type*} [∀ h, Field (L h)] [∀ h, Algebra K (L h)]
    [∀ h, Module.Finite K (L h)] [∀ h, Algebra.IsSeparable K (L h)]
    [Fintype J] [DecidableEq J]
    (ct : B →ₐ[E] E) (hunit : ∀ z : B, IsUnit z → z = algebraMap E B (ct z))
    (A : Subring B) (o : Subring E) (hA : ∀ a, algebraMap E B a ∈ A ↔ a ∈ o)
    (b : Basis J K (∀ h, L h)) (c : E) (hc : c ≠ 0) (x : J → A)
    (hx : (polynomial b).eval₂ ((algebraMap E B).comp (algebraMap K E))
      (fun j => (x j : B)) = algebraMap E B c) :
    ∀ j, ∃ a : o, (x j : B) = algebraMap E B (a : E) := by
  have he := etale_coordinates_constant ct hunit b c hc (fun j => (x j : B)) hx
  intro j
  have hm : ct (x j : B) ∈ o := (hA _).mp (by rw [← he j]; exact (x j).property)
  exact ⟨⟨ct (x j : B), hm⟩, he j⟩

end
end Surreal.NormForm
