import Surreal.Algebra.IntegerDiophantineGuards

/-!
# Polynomial images of finite Diophantine systems

A closure property used for the signed-integer form of MRDP in
`odg:def:thm:ce`. Source coordinates become existential witnesses and output
coordinates are tied to their integer-coefficient polynomial values.
-/

namespace Surreal.IntegerDiophantine
open MvPolynomial
noncomputable section

variable {m n : ℕ} {R : Type*} [CommRing R]

/-- Add source-coordinate witnesses and equations for the polynomial output map. -/
def System.polynomialImage (p : System m) (f : Fin n → MvPolynomial (Fin m) ℤ) : System n :=
  System.ofFinite (ν := Fin m ⊕ Fin p.witnesses) (ε := Fin p.equations ⊕ Fin n)
    (Sum.elim (fun j => rename Sum.inr (p.polynomial j))
      (fun j => X (Sum.inl j) - rename (fun k => Sum.inr (Sum.inl k)) (f j)))

/-- The new system defines exactly the polynomial image of the old solution set. -/
theorem System.holds_polynomialImage_iff (p : System m) (f : Fin n → MvPolynomial (Fin m) ℤ)
    (x : Fin n → R) : (p.polynomialImage f).Holds x ↔
      ∃ y : Fin m → R, p.Holds y ∧ ∀ j, x j = (f j).eval₂ (Int.castRingHom R) y := by
  rw [polynomialImage, holds_ofFinite_iff]
  have he (z : Fin m ⊕ Fin p.witnesses → R) : Sum.elim x z ∘ Sum.inr =
      Sum.elim (fun j => z (Sum.inl j)) (fun w => z (Sum.inr w)) := by
    funext v
    cases v <;> rfl
  have hf (z : Fin m ⊕ Fin p.witnesses → R) :
      Sum.elim x z ∘ (fun k => Sum.inr (Sum.inl k)) = (fun k => z (Sum.inl k)) := rfl
  simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, eval₂_rename, eval₂_sub, eval₂_X,
    sub_eq_zero, he, hf]
  constructor
  · rintro ⟨z, hp, hz⟩
    exact ⟨fun j => z (Sum.inl j), ⟨fun w => z (Sum.inr w), hp⟩, hz⟩
  · rintro ⟨y, ⟨w, hw⟩, hy⟩
    exact ⟨Sum.elim y w, hw, hy⟩

/-- Integer-polynomial images preserve finite-system Diophantine definability in any commutative ring. -/
theorem Definable.polynomialImage {D : Set (Fin m → R)} (hD : Definable D)
    (f : Fin n → MvPolynomial (Fin m) ℤ) :
    Definable {x : Fin n → R | ∃ y ∈ D, ∀ j, x j = (f j).eval₂ (Int.castRingHom R) y} := by
  obtain ⟨p, hp⟩ := hD
  refine ⟨p.polynomialImage f, fun x => ?_⟩
  rw [p.holds_polynomialImage_iff]
  exact exists_congr (fun y => and_congr (hp y) Iff.rfl)

end
end Surreal.IntegerDiophantine
