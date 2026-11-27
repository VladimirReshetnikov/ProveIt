import GRHArticle.ProgressionFree.PolynomialReplacementSeries
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The degree series of the smooth polynomial primes
-/

namespace GRHArticle.ProgressionFree

private theorem finite_monic_irreducible_degree_le (F : Type*) [Field F] [Finite F]
    (L : ℕ) : {p : Polynomial F | p.Monic ∧ Irreducible p ∧ p.natDegree ≤ L}.Finite := by
  letI : Finite (Polynomial.degreeLT F (L + 1)) :=
    Finite.of_injective _ (Polynomial.degreeLTEquiv F (L + 1)).injective
  refine (Set.toFinite (Polynomial.degreeLT F (L + 1) : Set (Polynomial F))).subset ?_
  intro p hp
  apply Polynomial.mem_degreeLT.mpr
  refine (Polynomial.degree_le_of_natDegree_le hp.2.2).trans_lt ?_
  exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self L)

/-- The finite set of monic irreducibles of degree at most the smoothness cutoff. -/
noncomputable def polynomialSmoothPrimes (F : Type*) [Field F] [Finite F] (L : ℕ) :
    Finset (Polynomial F) :=
  (finite_monic_irreducible_degree_le F L).toFinset

@[simp] theorem mem_polynomialSmoothPrimes {F : Type*} [Field F] [Finite F]
    {L : ℕ} {p : Polynomial F} :
    p ∈ polynomialSmoothPrimes F L ↔ p.Monic ∧ Irreducible p ∧ p.natDegree ≤ L := by
  exact Set.Finite.mem_toFinset _

/-- The formal series `H` for the smooth primes of a finite field. -/
noncomputable def polynomialSmoothDegreeSeries (F : Type*) [Field F] [Finite F] (L : ℕ) :
    PowerSeries ℕ :=
  smoothDegreeCountingSeries (polynomialSmoothPrimes F L) Polynomial.natDegree

/-- For any finite field, the article's formal series product has a positive
integer coefficient. -/
theorem polynomialSmoothDegreeSeries_exists_positive_replacement_coefficient
    (F : Type*) [Field F] [Finite F] (L : ℕ) :
    ∃ R, 1 ≤ PowerSeries.coeff R
      (PowerSeries.map (Nat.castRingHom ℤ) (polynomialSmoothDegreeSeries F L) *
        PowerSeries.mk polynomialDeficitDifference) :=
  smoothDegreeCountingSeries_exists_positive_coefficient
    (polynomialSmoothPrimes F L) Polynomial.natDegree

end GRHArticle.ProgressionFree
