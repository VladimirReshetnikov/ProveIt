import Mathlib.Algebra.MvPolynomial.CommRing
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

theorem integerPolynomial_coefficientGrid (I : MvPolynomial σ ℤ) (q : ℕ) :
    (fun α => (map (Int.castRingHom ℚ) I).coeff α) ∈ denominatorGrid q := by
  refine ⟨fun α => (q : ℤ) * I.coeff α, fun α => ?_⟩
  change (q : ℚ) * (map (Int.castRingHom ℚ) I).coeff α = _
  simp only [coeff_map, Int.cast_mul, Int.cast_natCast]
  rfl

theorem add_integerPolynomial_coefficientGrid (R : MvPolynomial σ ℚ)
    (I : MvPolynomial σ ℤ) (q : ℕ)
    (hR : (fun α => R.coeff α) ∈ denominatorGrid q) :
    (fun α => (R + map (Int.castRingHom ℚ) I).coeff α) ∈ denominatorGrid q := by
  obtain ⟨z, hz⟩ := hR
  refine ⟨fun α => z α + (q : ℤ) * I.coeff α, fun α => ?_⟩
  change (q : ℚ) * (R + map (Int.castRingHom ℚ) I).coeff α = _
  have hα : (q : ℚ) * R.coeff α = (z α : ℚ) := hz α
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_map, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, mul_add, hα]
  rfl

end Erdos3

end

end OAI
