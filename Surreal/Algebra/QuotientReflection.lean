import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Logic.Small.Basic

/-!
# Quotient reflection along a surjective constant map

The algebraic content of `osq:thm:reflection` and `osq:thm:quotients`.
The image of an ideal under a surjective ring map is an ideal; the induced
quotient map has kernel the image of the original kernel plus that ideal.
A split map's universal target factorization descends to every quotient.
-/

universe u v w t
namespace Surreal.QuotientReflection
noncomputable section

variable {A : Type u} {D : Type v} [CommRing A] [CommRing D]

/-- Reduction of the constant map modulo the image ideal. -/
def reduction (r : A →+* D) (I : Ideal A) : A →+* D ⧸ I.map r :=
  (Ideal.Quotient.mk (I.map r)).comp r

/-- Pulling back the image ideal adds precisely the kernel of a surjective map. -/
theorem comap_map (r : A →+* D) (hr : Function.Surjective r) (I : Ideal A) :
    (I.map r).comap r = RingHom.ker r ⊔ I := by
  rw [Ideal.comap_map_of_surjective r hr, ← RingHom.ker_eq_comap_bot, sup_comm]

/-- The kernel of reduction is exactly the original ideal plus the constant kernel. -/
theorem reduction_ker (r : A →+* D) (hr : Function.Surjective r) (I : Ideal A) :
    RingHom.ker (reduction r I) = RingHom.ker r ⊔ I := by
  calc
    RingHom.ker (reduction r I) = (I.map r).comap r := by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem
    _ = RingHom.ker r ⊔ I := comap_map r hr I

/-- The canonical map from the original quotient to the constant quotient. -/
def reflection (r : A →+* D) (I : Ideal A) : (A ⧸ I) →+* D ⧸ I.map r :=
  Ideal.Quotient.lift I (reduction r I) (fun _ hx =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem r hx))

@[simp] theorem reflection_mk (r : A →+* D) (I : Ideal A) (x : A) :
    reflection r I (Ideal.Quotient.mk I x) = Ideal.Quotient.mk (I.map r) (r x) := rfl

/-- The constant quotient reflection is onto. -/
theorem reflection_surjective (r : A →+* D) (hr : Function.Surjective r) (I : Ideal A) :
    Function.Surjective (reflection r I) := by
  intro y
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, rfl⟩ := hr d
  exact ⟨Ideal.Quotient.mk I x, rfl⟩

/-- The kernel inside the quotient is the image of the original kernel plus the ideal. -/
theorem reflection_ker (r : A →+* D) (hr : Function.Surjective r) (I : Ideal A) :
    RingHom.ker (reflection r I) = (RingHom.ker r ⊔ I).map (Ideal.Quotient.mk I) := by
  rw [reflection, Ideal.ker_quotient_lift, reduction_ker r hr]

/-- If the ideal already contains the constant kernel, reflection is a ring equivalence. -/
def quotientEquiv (r : A →+* D) (hr : Function.Surjective r)
    (I : Ideal A) (hI : RingHom.ker r ≤ I) : (A ⧸ I) ≃+* D ⧸ I.map r :=
  RingEquiv.ofBijective (reflection r I) ⟨by
    rw [RingHom.injective_iff_ker_eq_bot, reflection_ker r hr,
      sup_eq_right.mpr hI, Ideal.map_quotient_self], reflection_surjective r hr I⟩

/-- Quotient by an inverse-image ideal is the original ordinary quotient. -/
def quotientComapEquiv (r : A →+* D) (hr : Function.Surjective r) (J : Ideal D) :
    (A ⧸ J.comap r) ≃+* D ⧸ J :=
  (quotientEquiv r hr (J.comap r) (by
    intro x hx
    change r x ∈ J
    change r x = 0 at hx
    rw [hx]
    exact J.zero_mem)).trans (Ideal.quotEquivOfEq (Ideal.map_comap_of_surjective r hr J))

/-- An ideal containing the constant kernel is the inverse image of its unique image ideal. -/
theorem ideal_correspondence (r : A →+* D) (hr : Function.Surjective r)
    (I : Ideal A) (hI : RingHom.ker r ≤ I) : ∃! J : Ideal D, I = J.comap r := by
  refine ⟨I.map r, (comap_map r hr I).trans (sup_eq_right.mpr hI) |>.symm, ?_⟩
  intro J hJ
  rw [hJ, Ideal.map_comap_of_surjective r hr]

/-- A quotient containing the constant kernel is small whenever the coefficient ring is small. -/
theorem small_quotient_of_ker_le (r : A →+* D) (hr : Function.Surjective r)
    (I : Ideal A) (hI : RingHom.ker r ≤ I) [Small.{w} D] : Small.{w} (A ⧸ I) :=
  small_of_injective (quotientEquiv r hr I hI).injective

variable (r : A →+* D) (s : D →+* A) (hs : ∀ d, r (s d) = d)
  {S : Type w} [Ring S]
  (hfactor : ∀ (f : A →+* S) (x : A), f x = f (s (r x)))

/-- The ordinary factor of a quotient map kills exactly the required image ideal. -/
def factor (I : Ideal A) (φ : (A ⧸ I) →+* S) : (D ⧸ I.map r) →+* S :=
  Ideal.Quotient.lift (I.map r) ((φ.comp (Ideal.Quotient.mk I)).comp s) (by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_map_iff_of_surjective r (fun d => ⟨s d, hs d⟩) |>.mp hd
    change φ (Ideal.Quotient.mk I (s (r x))) = 0
    have he := hfactor (φ.comp (Ideal.Quotient.mk I)) x
    simp only [RingHom.comp_apply] at he
    rw [← he]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])

/-- The universal target factorization descends to any quotient, even a large one. -/
def homEquiv (I : Ideal A) : ((A ⧸ I) →+* S) ≃ ((D ⧸ I.map r) →+* S) where
  toFun := factor r s hs hfactor I
  invFun ψ := ψ.comp (reflection r I)
  left_inv φ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact (hfactor (φ.comp (Ideal.Quotient.mk I)) x).symm
  right_inv ψ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro d
    change ψ (Ideal.Quotient.mk (I.map r) (r (s d))) = ψ (Ideal.Quotient.mk (I.map r) d)
    rw [hs]

/-- The inverse of the homomorphism correspondence is literally composition with reflection. -/
theorem homEquiv_symm_apply (I : Ideal A) (ψ : (D ⧸ I.map r) →+* S) :
    (homEquiv r s hs hfactor I).symm ψ = ψ.comp (reflection r I) := rfl

/-- Postcomposition with a target map commutes with quotient reflection. -/
theorem homEquiv_natural (I : Ideal A) {T : Type t} [Ring T]
    (hfactorT : ∀ (f : A →+* T) (x : A), f x = f (s (r x)))
    (g : S →+* T) (φ : (A ⧸ I) →+* S) :
    homEquiv r s hs hfactorT I (g.comp φ) = g.comp (homEquiv r s hs hfactor I φ) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro d
  rfl

end
end Surreal.QuotientReflection
