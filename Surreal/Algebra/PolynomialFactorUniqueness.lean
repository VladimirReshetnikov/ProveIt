import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Uniqueness of monic factors from coprime reductions

The uniqueness clause of `polynomial:thm:hensel` must compare all qualifying
factors, not only factors constructed by a specified coefficient recursion.
A coefficient homomorphism that reflects units suffices: the resultant of
two monic polynomials is a unit whenever their reductions are coprime.
Cross-coprimeness and equality of the products then force divisibility,
and monic degree preservation forces equality.

No completeness, support restriction, or prior choice of a lifting algorithm
is assumed. The coefficient rings may have zero divisors.
-/

namespace Surreal.FinitePolynomial

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]

/-- Monic coprime reductions lift through any coefficient map reflecting units.
Monicity ensures that both actual resultant degrees survive the map. -/
theorem isCoprime_of_monic_reductions (φ : R →+* S)
    (hunit : ∀ a, IsUnit (φ a) → IsUnit a)
    {p q : R[X]} (hp : p.Monic) (hq : q.Monic)
    (hcop : IsCoprime (p.map φ) (q.map φ)) : IsCoprime p q := by
  apply (Polynomial.isUnit_resultant_iff_isCoprime hp).mp
  apply hunit
  have h := (Polynomial.isUnit_resultant_iff_isCoprime (hp.map φ)).mpr hcop
  simpa only [hp.natDegree_map, hq.natDegree_map, Polynomial.resultant_map_map] using h

/-- Any two monic factorizations with the same coprime reductions coincide.
The degrees need not be assumed separately: reduction preserves monic degrees. -/
theorem monic_factorization_unique_of_reductions (φ : R →+* S)
    (hunit : ∀ a, IsUnit (φ a) → IsUnit a)
    {p q p' q' : R[X]} (hp : p.Monic) (hq : q.Monic)
    (hp' : p'.Monic) (hq' : q'.Monic)
    (hcop : IsCoprime (p.map φ) (q.map φ))
    (hredp : p'.map φ = p.map φ) (hredq : q'.map φ = q.map φ)
    (hmul : p * q = p' * q') : p' = p ∧ q' = q := by
  have hcross : IsCoprime p q' := isCoprime_of_monic_reductions φ hunit hp hq'
    (by simpa only [hredq] using hcop)
  have hcross' : IsCoprime q p' := isCoprime_of_monic_reductions φ hunit hq hp'
    (by simpa only [hredp] using hcop.symm)
  have hpd : p ∣ p' := hcross.dvd_of_dvd_mul_right (hmul ▸ dvd_mul_right p q)
  have hqd : q ∣ q' := hcross'.dvd_of_dvd_mul_left (hmul ▸ dvd_mul_left q p)
  have hdegp : p'.natDegree = p.natDegree := by
    simpa only [hp.natDegree_map, hp'.natDegree_map] using congrArg natDegree hredp
  have hdegq : q'.natDegree = q.natDegree := by
    simpa only [hq.natDegree_map, hq'.natDegree_map] using congrArg natDegree hredq
  exact ⟨eq_of_monic_of_dvd_of_natDegree_le hp hp' hpd hdegp.le,
    eq_of_monic_of_dvd_of_natDegree_le hq hq' hqd hdegq.le⟩

/-- Finite-family uniqueness from pairwise coprime residues, including empty
families and degree-zero factors. No support restrictions on the candidates
are needed. -/
theorem monic_finite_factorization_unique_of_reductions {ι : Type*} [Fintype ι]
    (φ : R →+* S) (hunit : ∀ a, IsUnit (φ a) → IsUnit a)
    (p p' : ι → R[X]) (hp : ∀ i, (p i).Monic) (hp' : ∀ i, (p' i).Monic)
    (hcop : Pairwise fun i j => IsCoprime ((p i).map φ) ((p j).map φ))
    (hred : ∀ i, (p' i).map φ = (p i).map φ)
    (hmul : ∏ i, p i = ∏ i, p' i) : p' = p := by
  classical
  funext i
  have hcross : IsCoprime (p i) (∏ j ∈ Finset.univ.erase i, p' j) := by
    apply IsCoprime.prod_right
    intro j hj
    apply isCoprime_of_monic_reductions φ hunit (hp i) (hp' j)
    rw [hred]
    exact hcop (Finset.ne_of_mem_erase hj).symm
  have hdiv : p i ∣ ∏ j, p' j := hmul ▸ Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  rw [← Finset.mul_prod_erase Finset.univ p' (Finset.mem_univ i)] at hdiv
  have hdeg : (p' i).natDegree = (p i).natDegree := by
    simpa only [(hp i).natDegree_map, (hp' i).natDegree_map] using congrArg natDegree (hred i)
  exact eq_of_monic_of_dvd_of_natDegree_le (hp i) (hp' i)
    (hcross.dvd_of_dvd_mul_right hdiv) hdeg.le

end Surreal.FinitePolynomial
