import Surreal.Algebra.ConstantTermGraph
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Homomorphisms respect the constant-term graph

The algebraic mechanism of `odg:def:thm:homct`. Existential graph witnesses
map along arbitrary unital ring homomorphisms. Integer constants are fixed;
Gaussian constants are either fixed or conjugated, as determined by the
image of the imaginary unit in a domain.
-/

namespace Surreal.ConstantTermGraph

noncomputable section

variable {R S O P : Type*} [CommRing R] [CommRing S] [CommRing O] [CommRing P]

/-- Preserving graph witnesses forces commutation with the embedded constant terms. -/
theorem map_embedded_constant (ct : R →+* O) (ι : O →+* R)
    (ct' : S →+* P) (ι' : P →+* S)
    (hgraph : ∀ x n : R, Graph x n ↔ n = ι (ct x))
    (hgraph' : ∀ x n : S, Graph x n ↔ n = ι' (ct' x))
    (φ : R →+* S) (x : R) : φ (ι (ct x)) = ι' (ct' (φ x)) :=
  (hgraph' _ _).mp (((hgraph x _).mpr rfl).map φ)

/-- For integer constants the induced action is the identity. -/
theorem integer_hom_constant (ct : R →+* ℤ) (ι : ℤ →+* R)
    (ct' : S →+* ℤ) (ι' : ℤ →+* S) (hi' : Function.Injective ι')
    (hgraph : ∀ x n : R, Graph x n ↔ n = ι (ct x))
    (hgraph' : ∀ x n : S, Graph x n ↔ n = ι' (ct' x))
    (φ : R →+* S) (x : R) : ct' (φ x) = ct x := by
  apply hi'
  have he := map_embedded_constant ct ι ct' ι' hgraph hgraph' φ x
  have hc : φ.comp ι = ι' := Subsingleton.elim _ _
  exact he.symm.trans (congrArg (fun f : ℤ →+* S => f (ct x)) hc)

/-- Every map from Gaussian integers into a domain is determined by either sign of i. -/
theorem gaussian_hom_eq_or_conjugate [IsDomain S] (j g : GaussianInt →+* S) :
    g = j ∨ g = j.comp (starRingEnd GaussianInt) := by
  have hi : (Zsqrtd.sqrtd : GaussianInt) ^ 2 = -1 := by decide
  have hs : g Zsqrtd.sqrtd ^ 2 = j Zsqrtd.sqrtd ^ 2 := by
    rw [← map_pow, ← map_pow, hi, map_neg, map_one, map_neg, map_one]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact Or.inl (Zsqrtd.hom_ext g j h)
  · apply Or.inr
    apply Zsqrtd.hom_ext
    change g Zsqrtd.sqrtd = j (star (Zsqrtd.sqrtd : GaussianInt))
    rw [show star (Zsqrtd.sqrtd : GaussianInt) = -Zsqrtd.sqrtd by decide, map_neg]
    exact h

/-- The sign of the imaginary unit and the induced constant-term action agree. -/
theorem gaussian_hom_constant [IsDomain S]
    (ct : R →+* GaussianInt) (ι : GaussianInt →+* R)
    (ct' : S →+* GaussianInt) (ι' : GaussianInt →+* S) (hi' : Function.Injective ι')
    (hgraph : ∀ x n : R, Graph x n ↔ n = ι (ct x))
    (hgraph' : ∀ x n : S, Graph x n ↔ n = ι' (ct' x)) (φ : R →+* S) :
    (φ (ι Zsqrtd.sqrtd) = ι' Zsqrtd.sqrtd ∧ ∀ x, ct' (φ x) = ct x) ∨
      (φ (ι Zsqrtd.sqrtd) = -ι' Zsqrtd.sqrtd ∧ ∀ x, ct' (φ x) = star (ct x)) := by
  rcases gaussian_hom_eq_or_conjugate ι' (φ.comp ι) with h | h
  · refine Or.inl ⟨congrArg (fun f : GaussianInt →+* S => f Zsqrtd.sqrtd) h, fun x => ?_⟩
    apply hi'
    exact (map_embedded_constant ct ι ct' ι' hgraph hgraph' φ x).symm.trans
      (congrArg (fun f : GaussianInt →+* S => f (ct x)) h)
  · refine Or.inr ⟨?_, fun x => ?_⟩
    · have he := congrArg (fun f : GaussianInt →+* S => f Zsqrtd.sqrtd) h
      change φ (ι Zsqrtd.sqrtd) = ι' (star (Zsqrtd.sqrtd : GaussianInt)) at he
      simpa only [show star (Zsqrtd.sqrtd : GaussianInt) = -Zsqrtd.sqrtd by decide, map_neg] using he
    · apply hi'
      exact (map_embedded_constant ct ι ct' ι' hgraph hgraph' φ x).symm.trans
        (congrArg (fun f : GaussianInt →+* S => f (ct x)) h)

end
end Surreal.ConstantTermGraph
