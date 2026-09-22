import Surreal.Algebra.PolynomialFactorUniqueness

/-!
# From binary to finite coprime factor lifting

The finite-family algebraic reduction used for `polynomial:thm:hensel` in
`docs/surcomplex/polynomial-algebra/article.tex`. A proved binary lifting
property gives lifts of every finite family of monic, pairwise coprime
residue factors. Unit reflection then gives uniqueness among all monic
candidates, exact factor degrees, and pairwise coprimeness of the lifts.

This module is a reduction theorem, not a proof of the binary lifting
property for a particular coefficient ring. Its empty-family case is
included and uses degree preservation for monic polynomials.
-/

namespace Surreal.FinitePolynomial

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The binary existence property needed by the finite-family reduction.
In applications this property must be proved for the actual coefficient map. -/
def BinaryMonicFactorLifting (φ : R →+* S) : Prop :=
  ∀ p q : S[X], p.Monic → q.Monic → IsCoprime p q →
    ∀ H : R[X], H.Monic → H.map φ = p * q →
      ∃ P Q : R[X], P.Monic ∧ Q.Monic ∧ P.map φ = p ∧ Q.map φ = q ∧ P * Q = H

variable [Nontrivial S]

private theorem exists_monic_finset_factorization_of_binary {ι : Type*}
    (φ : R →+* S) (hlift : BinaryMonicFactorLifting φ)
    (p : ι → S[X]) (hm : ∀ i, (p i).Monic)
    (hc : Pairwise fun i j => IsCoprime (p i) (p j)) (s : Finset ι) :
    ∀ H : R[X], H.Monic → H.map φ = ∏ i ∈ s, p i →
      ∃ P : ι → R[X], (∀ i ∈ s, (P i).Monic ∧ (P i).map φ = p i) ∧
        ∏ i ∈ s, P i = H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro H hH hred
    refine ⟨fun _ => 1, by simp, ?_⟩
    have hHone : H = 1 := hH.eq_one_of_map_eq_one φ (by simpa using hred)
    simp [hHone]
  | @insert i s hi ih =>
    intro H hH hred
    have hprod : (∏ j ∈ s, p j).Monic := monic_prod_of_monic _ _ (fun j _ => hm j)
    have hcop : IsCoprime (p i) (∏ j ∈ s, p j) := by
      apply IsCoprime.prod_right
      intro j hj
      exact hc (by intro hij; exact hi (hij ▸ hj))
    obtain ⟨P, Q, hP, hQ, hPred, hQred, hPQ⟩ :=
      hlift (p i) (∏ j ∈ s, p j) (hm i) hprod hcop H hH
        (by simpa only [Finset.prod_insert hi] using hred)
    obtain ⟨Ps, hPs, hPsprod⟩ := ih Q hQ hQred
    refine ⟨Function.update Ps i P, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Function.update_self] using And.intro hP hPred
      · have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
        simpa only [Function.update_of_ne hji] using hPs j hj
    · have hupdate : ∏ j ∈ s, Function.update Ps i P j = ∏ j ∈ s, Ps j := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
        exact Function.update_of_ne hji P Ps
      rw [Finset.prod_insert hi, Function.update_self, hupdate, hPsprod, hPQ]

/-- Binary lifting implies existence of lifts for every finite pairwise
coprime monic factorization. This includes empty and singleton families. -/
theorem exists_monic_finite_factorization_of_binary {ι : Type*} [Fintype ι]
    (φ : R →+* S) (hlift : BinaryMonicFactorLifting φ)
    (p : ι → S[X]) (hm : ∀ i, (p i).Monic)
    (hc : Pairwise fun i j => IsCoprime (p i) (p j))
    (H : R[X]) (hH : H.Monic) (hred : H.map φ = ∏ i, p i) :
    ∃ P : ι → R[X], (∀ i, (P i).Monic ∧ (P i).map φ = p i) ∧ ∏ i, P i = H := by
  classical
  obtain ⟨P, hP, hprod⟩ :=
    exists_monic_finset_factorization_of_binary φ hlift p hm hc Finset.univ H hH hred
  exact ⟨P, fun i => hP i (Finset.mem_univ i), hprod⟩

/-- The resulting monic lifts are unique among all candidates with the
prescribed reductions and product, without any support or construction
restriction on a candidate. -/
theorem existsUnique_monic_finite_factorization_of_binary {ι : Type*} [Fintype ι]
    (φ : R →+* S) (hunit : ∀ a, IsUnit (φ a) → IsUnit a)
    (hlift : BinaryMonicFactorLifting φ)
    (p : ι → S[X]) (hm : ∀ i, (p i).Monic)
    (hc : Pairwise fun i j => IsCoprime (p i) (p j))
    (H : R[X]) (hH : H.Monic) (hred : H.map φ = ∏ i, p i) :
    ∃! P : ι → R[X], (∀ i, (P i).Monic ∧ (P i).map φ = p i) ∧ ∏ i, P i = H := by
  obtain ⟨P, hP, hprod⟩ := exists_monic_finite_factorization_of_binary φ hlift p hm hc H hH hred
  refine ⟨P, ⟨hP, hprod⟩, ?_⟩
  intro Q hQ
  apply monic_finite_factorization_unique_of_reductions φ hunit P Q
    (fun i => (hP i).1) (fun i => (hQ.1 i).1)
  · intro i j hij
    simpa only [(hP i).2, (hP j).2] using hc hij
  · intro i
    exact (hQ.1 i).2.trans (hP i).2.symm
  · exact hprod.trans hQ.2.symm

/-- Finite lifting with its automatic coprimeness and exact-degree
consequences. These conclusions impose no extra assumptions on the residues. -/
theorem existsUnique_coprime_monic_finite_factorization_of_binary
    {ι : Type*} [Fintype ι]
    (φ : R →+* S) (hunit : ∀ a, IsUnit (φ a) → IsUnit a)
    (hlift : BinaryMonicFactorLifting φ)
    (p : ι → S[X]) (hm : ∀ i, (p i).Monic)
    (hc : Pairwise fun i j => IsCoprime (p i) (p j))
    (H : R[X]) (hH : H.Monic) (hred : H.map φ = ∏ i, p i) :
    ∃! P : ι → R[X],
      (∀ i, (P i).Monic ∧ (P i).map φ = p i ∧ (P i).natDegree = (p i).natDegree) ∧
      (Pairwise fun i j => IsCoprime (P i) (P j)) ∧ ∏ i, P i = H := by
  obtain ⟨P, ⟨hP, hprod⟩, huniq⟩ :=
    existsUnique_monic_finite_factorization_of_binary φ hunit hlift p hm hc H hH hred
  refine ⟨P, ⟨?_, ?_, hprod⟩, ?_⟩
  · intro i
    refine ⟨(hP i).1, (hP i).2, ?_⟩
    rw [← (hP i).1.natDegree_map φ, (hP i).2]
  · intro i j hij
    apply isCoprime_of_monic_reductions φ hunit (hP i).1 (hP j).1
    simpa only [(hP i).2, (hP j).2] using hc hij
  · intro Q hQ
    exact huniq Q ⟨fun i => ⟨(hQ.1 i).1, (hQ.1 i).2.1⟩, hQ.2.2⟩

end Surreal.FinitePolynomial
