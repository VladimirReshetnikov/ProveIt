import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Gaussian integers: Euclidean structure and the splitting of rational primes

Mathlib provides the Euclidean-domain structure of `ℤ[i]` for the norm `N(x + iy) = x² + y²`
(`GaussianInt.instEuclideanDomain`), hence unique factorisation.  This file records the three
statements of qg:lem-gaussian-ufd:

* `2 = -i (1 + i)²` (`gaussianInt_two_eq`);
* a rational prime `p ≡ 3 (mod 4)` is irreducible (indeed prime) in `ℤ[i]`
  (`gaussianInt_irreducible_of_mod_four_eq_three`, from Mathlib's
  `GaussianInt.prime_of_nat_prime_of_mod_four_eq_three`);
* a rational prime `p ≡ 1 (mod 4)` splits as `p = ϖ ϖ̄` with `ϖ` a Gaussian prime, unique up to a
  unit and conjugation (`gaussianInt_exists_prime_mul_star`, from Fermat's two-square theorem
  `Nat.Prime.sq_add_sq` and the norm argument `irreducible_of_norm_natAbs_prime`).
-/

set_option autoImplicit false

open GaussianInt Zsqrtd

local notation "ℤ[i]" => GaussianInt

namespace Fabius

/-- `2 = -i (1 + i)²` in `ℤ[i]`. -/
theorem gaussianInt_two_eq : (2 : ℤ[i]) = -(⟨0, 1⟩ : ℤ[i]) * (⟨1, 1⟩ : ℤ[i]) ^ 2 := by
  ext <;> simp [sq]

/-- An element of `ℤ[i]` whose norm is a rational prime is irreducible. -/
theorem irreducible_of_norm_natAbs_prime {z : ℤ[i]} (hz : (norm z).natAbs.Prime) :
    Irreducible z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero, Int.natAbs_zero] at hz
    exact Nat.not_prime_zero hz
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [← norm_eq_one_iff] at hu
    rw [hu] at hz
    exact Nat.not_prime_one hz
  · have hnorm : (norm z).natAbs = (norm a).natAbs * (norm b).natAbs := by
      rw [hab, norm_mul, Int.natAbs_mul]
    rcases hz.eq_one_or_self_of_dvd (norm a).natAbs ⟨(norm b).natAbs, hnorm⟩ with ha | ha
    · exact Or.inl (norm_eq_one_iff.mp ha)
    · right
      rw [ha] at hnorm
      have hb : (norm b).natAbs = 1 :=
        Nat.eq_of_mul_eq_mul_left hz.pos (by rw [← hnorm, mul_one])
      exact norm_eq_one_iff.mp hb

/-- A rational prime `p ≡ 3 (mod 4)` is irreducible in `ℤ[i]`. -/
theorem gaussianInt_irreducible_of_mod_four_eq_three (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    Irreducible (p : ℤ[i]) :=
  (prime_of_nat_prime_of_mod_four_eq_three p hp).irreducible

/-- The norm of `⟨a, b⟩` is `a² + b²`. -/
theorem norm_mk_eq (a b : ℤ) : norm (⟨a, b⟩ : ℤ[i]) = a * a + b * b := by
  simp [Zsqrtd.norm]

/-- A rational prime `p ≡ 1 (mod 4)` is `ϖ ϖ̄` for a Gaussian prime `ϖ`, unique up to a unit and
conjugation. -/
theorem gaussianInt_exists_prime_mul_star (p : ℕ) [hp : Fact p.Prime] (hp1 : p % 4 = 1) :
    ∃ ϖ : ℤ[i], Prime ϖ ∧ (p : ℤ[i]) = ϖ * star ϖ ∧
      ∀ σ : ℤ[i], Prime σ → (p : ℤ[i]) = σ * star σ →
        Associated σ ϖ ∨ Associated σ (star ϖ) := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  let ϖ : ℤ[i] := ⟨a, b⟩
  have hnorm : norm ϖ = p := by
    rw [norm_mk_eq]
    exact_mod_cast (by rw [← hab]; ring : a * a + b * b = p)
  have hprime : ∀ z : ℤ[i], norm z = p → Prime z := fun z hz =>
    UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (irreducible_of_norm_natAbs_prime (by rw [hz, Int.natAbs_natCast]; exact hp.out))
  have hsplit : (p : ℤ[i]) = ϖ * star ϖ := by
    have := norm_eq_mul_conj ϖ
    rw [hnorm] at this
    exact_mod_cast this
  refine ⟨ϖ, hprime ϖ hnorm, hsplit, fun σ hσ hσp => ?_⟩
  have hstar : Prime (star ϖ) := hprime _ (by rw [norm_conj, hnorm])
  have hdvd : σ ∣ ϖ * star ϖ := ⟨star σ, by rw [← hsplit, hσp]⟩
  rcases hσ.dvd_or_dvd hdvd with h | h
  · exact Or.inl (hσ.associated_of_dvd (hprime ϖ hnorm) h)
  · exact Or.inr (hσ.associated_of_dvd hstar h)

end Fabius
