import Surreal.HahnSeries.PolynomialFactorLifting

/-!
# Common support bounds for all lifted Hahn factors

Every factor in a finite coprime lift inherits the support monoid generated
by the errors of the original polynomial. For each factor, binary uniqueness
compares it with a binary lift separating its own residue from the product of
all remaining residues. Thus the common support bound refers to the original
error, independently of the factorization order. Subtracting each constant
residue gives a lower-degree positive-order correction, with support in the
same generated monoid minus zero, as in `polynomial:thm:hensel`.
-/

namespace Surreal.HahnSeries

open Polynomial
open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- Every member of any finite monic factorization with pairwise coprime
residues has support in the original polynomial's error monoid. -/
theorem support_finite_factor_coeff_subset_residueErrorSupport
    {ι : Type*} [Fintype ι] (p : ι → K[X]) (hp : ∀ i, (p i).Monic)
    (hcop : Pairwise fun i j => IsCoprime (p i) (p j))
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic)
    (hred : H.map (standardPart Γ K) = ∏ i, p i)
    (P : ι → Polynomial (nonnegativeSubring Γ K)) (hP : ∀ i, (P i).Monic)
    (hPred : ∀ i, (P i).map (standardPart Γ K) = p i) (hprod : ∏ i, P i = H)
    (i : ι) (n : ℕ) : (P i |>.coeff n : K⟦Γ⟧).support ⊆ residueErrorSupport H := by
  classical
  let q := ∏ j ∈ Finset.univ.erase i, p j
  let Q := ∏ j ∈ Finset.univ.erase i, P j
  have hq : q.Monic := monic_prod_of_monic _ _ (fun j _ => hp j)
  have hQ : Q.Monic := monic_prod_of_monic _ _ (fun j _ => hP j)
  have hcopi : IsCoprime (p i) q := by
    apply IsCoprime.prod_right
    intro j hj
    exact hcop (Finset.ne_of_mem_erase hj).symm
  have hQred : Q.map (standardPart Γ K) = q := by
    simp only [Q, q, Polynomial.map_prod, hPred]
  have hred' : H.map (standardPart Γ K) = p i * q := by
    rw [hred]
    exact (Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)).symm
  have hprod' : P i * Q = H := by
    rw [Finset.mul_prod_erase Finset.univ P (Finset.mem_univ i)]
    exact hprod
  obtain ⟨⟨A, B⟩, hA, hB, _, _, hAred, hBred, _, hAB, hAs, _⟩ :=
    exists_monic_factorization_with_support_of_standardPart (p i) q (hp i) hq hcopi H hH hred'
  obtain ⟨hPi, _⟩ := monic_factorization_unique_of_standardPart hA hB (hP i) hQ
    (by rw [hAred, hBred]; exact hcopi)
    ((hPred i).trans hAred.symm) (hQred.trans hBred.symm) (hAB.trans hprod'.symm)
  rw [hPi]
  exact hAs n

/-- Subtracting the residue removes zero from the support while preserving
membership in any containing additive monoid. -/
theorem support_sub_constant_standardPart_subset
    (a : nonnegativeSubring Γ K) (S : AddSubmonoid Γ)
    (hS : (a : K⟦Γ⟧).support ⊆ S) :
    ((a : K⟦Γ⟧) - single 0 (standardPart Γ K a)).support ⊆ (S : Set Γ) \ {0} := by
  intro g hg
  constructor
  · rcases support_sub_subset _ _ hg with hga | hgc
    · exact hS hga
    · rw [eq_of_mem_support_single hgc]
      exact S.zero_mem
  · intro hg0
    have hzero : g = 0 := Set.mem_singleton_iff.mp hg0
    subst g
    have hn := (mem_support _ _).mp hg
    apply hn
    rw [HahnSeries.coeff_sub, coeff_single_same, standardPart_apply, sub_self]

/-- The difference between a monic factor and its constant residue has
strictly smaller polynomial degree, including degree-zero factors. -/
theorem degree_factor_correction_lt (P : Polynomial (nonnegativeSubring Γ K))
    (hP : P.Monic) (p : K[X]) (hred : P.map (standardPart Γ K) = p) :
    (P - p.map constantNonnegative).degree < (p.natDegree : WithBot ℕ) := by
  have hp : p.Monic := hred ▸ hP.map _
  have hpm : (p.map (constantNonnegative (Γ := Γ))).Monic := hp.map _
  have hd : P.natDegree = p.natDegree := by
    rw [← hP.natDegree_map (standardPart Γ K), hred]
  have hd' : P.degree = (p.map (constantNonnegative (Γ := Γ))).degree := by
    rw [Polynomial.degree_eq_natDegree hP.ne_zero,
      Polynomial.degree_eq_natDegree hpm.ne_zero, hp.natDegree_map, hd]
  simpa only [Polynomial.degree_eq_natDegree hP.ne_zero, hd] using
    Polynomial.degree_sub_lt hd' hP.ne_zero (hP.trans hpm.symm)

/-- Every correction coefficient of any finite coprime lift has support in
the original error monoid with zero removed. -/
theorem support_finite_factor_correction_subset
    {ι : Type*} [Fintype ι] (p : ι → K[X]) (hp : ∀ i, (p i).Monic)
    (hcop : Pairwise fun i j => IsCoprime (p i) (p j))
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic)
    (hred : H.map (standardPart Γ K) = ∏ i, p i)
    (P : ι → Polynomial (nonnegativeSubring Γ K)) (hP : ∀ i, (P i).Monic)
    (hPred : ∀ i, (P i).map (standardPart Γ K) = p i) (hprod : ∏ i, P i = H)
    (i : ι) (n : ℕ) :
    ((P i - (p i).map constantNonnegative).coeff n : K⟦Γ⟧).support ⊆
      (residueErrorSupport H : Set Γ) \ {0} := by
  have hs := support_finite_factor_coeff_subset_residueErrorSupport
    p hp hcop H hH hred P hP hPred hprod i n
  have hc : standardPart Γ K ((P i).coeff n) = (p i).coeff n := by
    have h := congrArg (fun F => F.coeff n) (hPred i)
    rw [Polynomial.coeff_map] at h
    exact h
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map]
  have h := support_sub_constant_standardPart_subset ((P i).coeff n) (residueErrorSupport H) hs
  rw [hc] at h
  exact h

/-- Full finite-family Hahn Hensel lifting with common support control on all
positive-order lower-degree corrections. Uniqueness already holds without
these support restrictions. -/
theorem existsUnique_monic_finite_factorization_with_support
    {ι : Type*} [Fintype ι] (p : ι → K[X]) (hp : ∀ i, (p i).Monic)
    (hcop : Pairwise fun i j => IsCoprime (p i) (p j))
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic)
    (hred : H.map (standardPart Γ K) = ∏ i, p i) :
    ∃! P : ι → Polynomial (nonnegativeSubring Γ K),
      (∀ i, (P i).Monic ∧ (P i).map (standardPart Γ K) = p i ∧
        (P i).natDegree = (p i).natDegree) ∧
      (Pairwise fun i j => IsCoprime (P i) (P j)) ∧ (∏ i, P i = H) ∧
      (∀ i, (P i - (p i).map constantNonnegative).degree < ((p i).natDegree : WithBot ℕ)) ∧
      (∀ i n, 0 < ((P i - (p i).map constantNonnegative).coeff n : K⟦Γ⟧).orderTop) ∧
      (∀ i n, ((P i - (p i).map constantNonnegative).coeff n : K⟦Γ⟧).support ⊆
        (residueErrorSupport H : Set Γ) \ {0}) := by
  obtain ⟨P, ⟨hP, hcopP, hprod⟩, huniq⟩ :=
    existsUnique_monic_finite_factorization_of_standardPart p hp hcop H hH hred
  refine ⟨P, ⟨hP, hcopP, hprod, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact degree_factor_correction_lt (P i) (hP i).1 (p i) (hP i).2.1
  · intro i n
    rw [← (hP i).2.1]
    exact orderTop_coeff_sub_constant_residue_pos (P i) n
  · exact support_finite_factor_correction_subset p hp hcop H hH hred P
      (fun i => (hP i).1) (fun i => (hP i).2.1) hprod
  · intro Q hQ
    exact huniq Q ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩

end

end Surreal.HahnSeries
