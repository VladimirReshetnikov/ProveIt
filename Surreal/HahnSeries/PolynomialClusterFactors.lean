import Surreal.HahnSeries.PolynomialFiniteFactorSupport
import Mathlib.Analysis.Complex.Polynomial.Basic
import Surreal.HahnSeries.PolynomialReduction

/-!
# Canonical standard-part cluster factors in Hahn fields

This proves `polynomial:cor:clusterfactor`: a monic polynomial over the
nonnegative-order Hahn ring has unique factors indexed by the distinct roots
of its ordinary residue polynomial. Each factor collects precisely the
existing Hahn roots with its prescribed standard part. The residue field
must split the residue polynomial; for complex coefficients Mathlib supplies
this automatically. No algebraic closedness of the Hahn field or divisibility
of its exponent group is assumed.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- Reduction of a root of a cluster factor determines its residue center. -/
theorem standardPart_eq_of_cluster_root
    (P : Polynomial (nonnegativeSubring Γ K)) (c : K) (m : ℕ) (hm : 0 < m)
    (hred : P.map (standardPart Γ K) = (X - C c) ^ m)
    (z : nonnegativeSubring Γ K) (hz : P.IsRoot z) : standardPart Γ K z = c := by
  have h := hz.map (f := standardPart Γ K)
  rw [hred, IsRoot.def, eval_pow, eval_sub, eval_X, eval_C] at h
  exact sub_eq_zero.mp ((pow_eq_zero_iff hm.ne').mp h)

/-- A finite factorization with distinct cluster residues assigns each finite
root to precisely the factor determined by its standard part. -/
theorem isRoot_cluster_factor_iff {ι : Type*} [Fintype ι]
    (c : ι → K) (hc : Function.Injective c) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (H : Polynomial (nonnegativeSubring Γ K))
    (P : ι → Polynomial (nonnegativeSubring Γ K))
    (hred : ∀ i, (P i).map (standardPart Γ K) = (X - C (c i)) ^ m i)
    (hprod : ∏ i, P i = H) (i : ι) (z : nonnegativeSubring Γ K) :
    (P i).IsRoot z ↔ H.IsRoot z ∧ standardPart Γ K z = c i := by
  classical
  constructor
  · intro hz
    refine ⟨?_, standardPart_eq_of_cluster_root (P i) (c i) (m i) (hm i) (hred i) z hz⟩
    rw [← hprod]
    exact (isRoot_prod Finset.univ P z).mpr ⟨i, Finset.mem_univ i, hz⟩
  · rintro ⟨hz, hzc⟩
    rw [← hprod] at hz
    obtain ⟨j, _, hj⟩ := (isRoot_prod Finset.univ P z).mp hz
    have hjc := standardPart_eq_of_cluster_root (P j) (c j) (m j) (hm j) (hred j) z hj
    have hji : j = i := hc (hjc.symm.trans hzc)
    simpa only [hji] using hj

/-- The cluster root characterization applies to every existing ambient Hahn
root: monicity supplies its finiteness automatically. -/
theorem isRoot_map_cluster_factor_iff {ι : Type*} [Fintype ι]
    (c : ι → K) (hc : Function.Injective c) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic)
    (P : ι → Polynomial (nonnegativeSubring Γ K)) (hP : ∀ i, (P i).Monic)
    (hred : ∀ i, (P i).map (standardPart Γ K) = (X - C (c i)) ^ m i)
    (hprod : ∏ i, P i = H) (i : ι) (z : K⟦Γ⟧) :
    ((P i).map (nonnegativeSubring Γ K).subtype).IsRoot z ↔
      (H.map (nonnegativeSubring Γ K).subtype).IsRoot z ∧ z.coeff 0 = c i := by
  constructor
  · intro hz
    let z₀ : nonnegativeSubring Γ K := ⟨z, orderTop_nonneg_of_monic_root (P i) (hP i) z hz⟩
    have hz₀ : (P i).IsRoot z₀ := hz.of_map Subtype.val_injective
    obtain ⟨hroot, hstd⟩ := (isRoot_cluster_factor_iff c hc m hm H P hred hprod i z₀).mp hz₀
    exact ⟨hroot.map (f := (nonnegativeSubring Γ K).subtype), hstd⟩
  · rintro ⟨hz, hzc⟩
    let z₀ : nonnegativeSubring Γ K := ⟨z, orderTop_nonneg_of_monic_root H hH z hz⟩
    have hz₀ : H.IsRoot z₀ := hz.of_map Subtype.val_injective
    exact ((isRoot_cluster_factor_iff c hc m hm H P hred hprod i z₀).mpr
      ⟨hz₀, hzc⟩).map (f := (nonnegativeSubring Γ K).subtype)

/-- Canonical cluster factors from a finite factorization of the residue into
powers of distinct linear factors, with common support control and the full
ambient-root characterization. -/
theorem existsUnique_cluster_factors {ι : Type*} [Fintype ι]
    (c : ι → K) (hc : Function.Injective c) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic)
    (hred : H.map (standardPart Γ K) = ∏ i, (X - C (c i)) ^ m i) :
    ∃! P : ι → Polynomial (nonnegativeSubring Γ K),
      (∀ i, (P i).Monic ∧ (P i).map (standardPart Γ K) = (X - C (c i)) ^ m i ∧
        (P i).natDegree = m i) ∧
      (Pairwise fun i j => IsCoprime (P i) (P j)) ∧ (∏ i, P i = H) ∧
      (∀ i n, ((P i - ((X - C (c i)) ^ m i).map constantNonnegative).coeff n : K⟦Γ⟧).support ⊆
        (residueErrorSupport H : Set Γ) \ {0}) ∧
      (∀ i z, ((P i).map (nonnegativeSubring Γ K).subtype).IsRoot z ↔
        (H.map (nonnegativeSubring Γ K).subtype).IsRoot z ∧ z.coeff 0 = c i) := by
  let p : ι → K[X] := fun i => (X - C (c i)) ^ m i
  have hp (i : ι) : (p i).Monic := (monic_X_sub_C (c i)).pow _
  have hcop : Pairwise fun i j => IsCoprime (p i) (p j) :=
    fun _ _ hij => (pairwise_coprime_X_sub_C hc hij).pow
  obtain ⟨P, ⟨hP, hcopP, hprod, _, _, hs⟩, _⟩ :=
    existsUnique_monic_finite_factorization_with_support p hp hcop H hH hred
  have hPd (i : ι) : (P i).natDegree = m i := by
    simpa only [p, natDegree_pow, natDegree_X_sub_C, mul_one] using (hP i).2.2
  refine ⟨P, ⟨fun i => ⟨(hP i).1, (hP i).2.1, hPd i⟩, hcopP, hprod, hs, ?_⟩, ?_⟩
  · exact isRoot_map_cluster_factor_iff c hc m hm H hH P
      (fun i => (hP i).1) (fun i => (hP i).2.1) hprod
  · intro Q hQ
    apply FinitePolynomial.monic_finite_factorization_unique_of_reductions
      (standardPart Γ K) standardPart_reflects_units P Q
      (fun i => (hP i).1) (fun i => (hQ.1 i).1)
    · intro i j hij
      rw [(hP i).2.1, (hP j).2.1]
      exact hcop hij
    · intro i
      exact (hQ.1 i).2.1.trans (hP i).2.1.symm
    · exact hprod.trans hQ.2.2.1.symm


/-- The distinct ordinary roots of the residue polynomial. -/
def residueRootSet (H : Polynomial (nonnegativeSubring Γ K)) : Finset K := by
  classical
  exact (H.map (standardPart Γ K)).roots.toFinset

/-- The ordinary multiplicity of a residue center. -/
def residueMultiplicity (H : Polynomial (nonnegativeSubring Γ K))
    (c : residueRootSet H) : ℕ := rootMultiplicity c.val (H.map (standardPart Γ K))

theorem residueMultiplicity_pos (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic)
    (c : residueRootSet H) : 0 < residueMultiplicity H c := by
  classical
  apply (rootMultiplicity_pos (hH.map (standardPart Γ K)).ne_zero).mpr
  apply (mem_roots (hH.map (standardPart Γ K)).ne_zero).mp
  exact Multiset.mem_toFinset.mp c.property

/-- Splitting gives the canonical finite product indexed by distinct residue
roots and weighted by their ordinary root multiplicities. -/
theorem residue_eq_prod_cluster_factors (H : Polynomial (nonnegativeSubring Γ K))
    (hH : H.Monic) (hs : (H.map (standardPart Γ K)).Splits) :
    H.map (standardPart Γ K) =
      ∏ c : residueRootSet H, (X - C c.val) ^ residueMultiplicity H c := by
  classical
  rw [hs.eq_prod_roots_of_monic (hH.map (standardPart Γ K)),
    prod_multiset_root_eq_finset_root]
  exact (Finset.prod_coe_sort _ _).symm

/-- The data and consequences defining a cluster factorization: prescribed
monic residue powers and degrees, pairwise coprimeness, exact product, common
correction support, and the characterization of every existing ambient root. -/
def IsClusterFactorization {ι : Type*} [Fintype ι]
    (c : ι → K) (m : ι → ℕ) (H : Polynomial (nonnegativeSubring Γ K))
    (P : ι → Polynomial (nonnegativeSubring Γ K)) : Prop :=
  (∀ i, (P i).Monic ∧ (P i).map (standardPart Γ K) = (X - C (c i)) ^ m i ∧
    (P i).natDegree = m i) ∧
  (Pairwise fun i j => IsCoprime (P i) (P j)) ∧ (∏ i, P i = H) ∧
  (∀ i n, ((P i - ((X - C (c i)) ^ m i).map constantNonnegative).coeff n : K⟦Γ⟧).support ⊆
    (residueErrorSupport H : Set Γ) \ {0}) ∧
  (∀ i z, ((P i).map (nonnegativeSubring Γ K).subtype).IsRoot z ↔
    (H.map (nonnegativeSubring Γ K).subtype).IsRoot z ∧ z.coeff 0 = c i)

/-- Canonical factors indexed by the actual distinct roots of a split residue
polynomial. This requires splitting only in the ordinary coefficient field. -/
theorem existsUnique_canonical_cluster_factors_of_splits
    (H : Polynomial (nonnegativeSubring Γ K)) (hH : H.Monic)
    (hs : (H.map (standardPart Γ K)).Splits) :
    ∃! P : residueRootSet H → Polynomial (nonnegativeSubring Γ K),
      IsClusterFactorization (fun c : residueRootSet H => c.val) (residueMultiplicity H) H P :=
  existsUnique_cluster_factors (fun c : residueRootSet H => c.val) Subtype.val_injective
    (residueMultiplicity H) (residueMultiplicity_pos H hH) H hH
    (residue_eq_prod_cluster_factors H hH hs)

/-- Every monic polynomial over the nonnegative complex Hahn ring has its
canonical standard-part cluster factors. Complex residue splitting is supplied
by Mathlib; the Hahn field itself need not be algebraically closed. -/
theorem existsUnique_complex_cluster_factors
    (H : Polynomial (nonnegativeSubring Γ ℂ)) (hH : H.Monic) :
    ∃! P : residueRootSet H → Polynomial (nonnegativeSubring Γ ℂ),
      IsClusterFactorization (fun c : residueRootSet H => c.val) (residueMultiplicity H) H P :=
  existsUnique_canonical_cluster_factors_of_splits H hH (IsAlgClosed.splits _)

end

end Surreal.HahnSeries
