import FabiusFunction.OrdinaryBellComposition
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Multinomial form of the ordinary Bell polynomials

The ordinary partial Bell polynomial `ordPartialBell x n k` is already the
coefficient of the `k`-th power of a zero-constant-term series.  This module
groups its ordered compositions by the multiplicity of each possible part
size.  A profile `π : Fin n → ℕ` records `π j` parts of size `j + 1`; its two
constraints say that it has `k` parts and total weight `n`.

The resulting finite sum is the multinomial form of ordinary composition.
It works over every commutative semiring.  The source-facing composition
corollary retains the commutative-ring hypotheses of power-series
substitution and includes degree zero: there the unique empty profile gives
the constant coefficient.  No convergence or analytic composition is used.

## Main results

* `ordinaryMultiplicityProfiles` and `mem_ordinaryMultiplicityProfiles`:
  finite multiplicity profiles with prescribed part count and weight.
* `ordPartialBell_eq_sum_multinomial`: the multinomial expansion of an
  ordinary partial Bell polynomial.
* `coeff_subst_eq_sum_multinomial`: ordinary power-series composition in
  multiplicity form.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- Multiplicity profiles for partitions of total weight `n` into `k`
positive parts.  The coordinate `j : Fin n` records the number of parts of
size `j + 1`. -/
noncomputable def ordinaryMultiplicityProfiles (n k : ℕ) :
    Finset (Fin n → ℕ) :=
  (Finset.piAntidiag (Finset.univ : Finset (Fin n)) k).filter
    (fun π => ∑ j : Fin n, (j.1 + 1) * π j = n)

/-- Membership in `ordinaryMultiplicityProfiles n k` is exactly the pair of
constraints `∑ π_j = k` and `∑ (j+1)π_j = n`. -/
@[simp]
theorem mem_ordinaryMultiplicityProfiles {n k : ℕ} {π : Fin n → ℕ} :
    π ∈ ordinaryMultiplicityProfiles n k ↔
      (∑ j : Fin n, π j) = k ∧
        (∑ j : Fin n, (j.1 + 1) * π j) = n := by
  simp [ordinaryMultiplicityProfiles]

/-- The ordinary partial Bell polynomial is the sum over multiplicity
profiles, with the number of orderings of each profile supplied by the
multinomial coefficient. -/
theorem ordPartialBell_eq_sum_multinomial {R : Type*} [CommSemiring R]
    (x : ℕ → R) (n k : ℕ) :
    ordPartialBell x n k =
      ∑ π ∈ ordinaryMultiplicityProfiles n k,
        (Nat.multinomial (Finset.univ : Finset (Fin n)) π : R) *
          ∏ j : Fin n, x (j.1 + 1) ^ π j := by
  classical
  let p : R⟦X⟧ :=
    ∑ j : Fin n, PowerSeries.monomial (j.1 + 1) (x (j.1 + 1))
  have hp0 : PowerSeries.constantCoeff p = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [p, PowerSeries.coeff_monomial]
  have hpcoeff (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      PowerSeries.coeff i p = x i := by
    have hit : i - 1 < n := by omega
    simp only [p, map_sum]
    rw [Finset.sum_eq_single (⟨i - 1, hit⟩ : Fin n)]
    · have hval : i - 1 + 1 = i := by omega
      simp [hval]
    · intro j _ hj
      rw [PowerSeries.coeff_monomial]
      split_ifs with heq
      · exfalso
        apply hj
        apply Fin.ext
        dsimp at heq ⊢
        omega
      · rfl
    · simp
  have hcast (m : ℕ) : (m : R⟦X⟧) = PowerSeries.C (m : R) := by
    exact (map_natCast (PowerSeries.C : R →+* R⟦X⟧) m).symm
  have hmonomial (π : Fin n → ℕ) :
      ∏ j : Fin n,
          (PowerSeries.monomial (j.1 + 1) (x (j.1 + 1))) ^ π j =
        PowerSeries.monomial
          (∑ j : Fin n, (j.1 + 1) * π j)
          (∏ j : Fin n, x (j.1 + 1) ^ π j) := by
    simp_rw [PowerSeries.monomial_pow]
    simpa [Nat.mul_comm] using
      (PowerSeries.prod_monomial
        (R := R) (fun j : Fin n => π j * (j.1 + 1))
        (fun j : Fin n => x (j.1 + 1) ^ π j)
        (Finset.univ : Finset (Fin n)))
  have hmultinomial :
      p ^ k =
        ∑ π ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k,
          (Nat.multinomial (Finset.univ : Finset (Fin n)) π : R⟦X⟧) *
            ∏ j : Fin n,
              (PowerSeries.monomial (j.1 + 1) (x (j.1 + 1))) ^ π j := by
    simpa [p] using
      (Finset.sum_pow_eq_sum_piAntidiag
        (R := R⟦X⟧) (Finset.univ : Finset (Fin n))
        (fun j : Fin n =>
          PowerSeries.monomial (j.1 + 1) (x (j.1 + 1))) k)
  calc
    ordPartialBell x n k =
        ordPartialBell (fun i => PowerSeries.coeff i p) n k :=
      ordPartialBell_congr_of_le n k fun i hi hin =>
        (hpcoeff i hi hin).symm
    _ = PowerSeries.coeff n (p ^ k) :=
      (coeff_pow_eq_ordPartialBell hp0 n k).symm
    _ = PowerSeries.coeff n
        (∑ π ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k,
          (Nat.multinomial (Finset.univ : Finset (Fin n)) π : R⟦X⟧) *
            ∏ j : Fin n,
              (PowerSeries.monomial (j.1 + 1) (x (j.1 + 1))) ^ π j) := by
      rw [hmultinomial]
    _ = ∑ π ∈ ordinaryMultiplicityProfiles n k,
        (Nat.multinomial (Finset.univ : Finset (Fin n)) π : R) *
          ∏ j : Fin n, x (j.1 + 1) ^ π j := by
      rw [ordinaryMultiplicityProfiles, Finset.sum_filter]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [hcast, hmonomial, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_monomial]
      by_cases hweight : (∑ j : Fin n, (j.1 + 1) * π j) = n
      · rw [if_pos hweight, if_pos hweight.symm]
      · rw [if_neg hweight, if_neg (Ne.symm hweight), mul_zero]

/-- Ordinary power-series composition in multiplicity form.  For positive
`n`, the `k = 0` summand vanishes and this is the usual sum from `1` to `n`;
at `n = 0`, the unique empty profile returns the constant coefficient of
`g`. -/
theorem coeff_subst_eq_sum_multinomial {R : Type*} [CommRing R]
    (g : R⟦X⟧) {f : R⟦X⟧} (hf : constantCoeff f = 0) (n : ℕ) :
    coeff n (g.subst f) =
      ∑ k ∈ Finset.range (n + 1), coeff k g *
        ∑ π ∈ ordinaryMultiplicityProfiles n k,
          (Nat.multinomial (Finset.univ : Finset (Fin n)) π : R) *
            ∏ j : Fin n, coeff (j.1 + 1) f ^ π j := by
  rw [coeff_subst_eq_sum_ordPartialBell g hf n]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ordPartialBell_eq_sum_multinomial]

end Fabius
