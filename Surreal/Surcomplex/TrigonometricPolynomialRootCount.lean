import Surreal.Algebra.LaurentAlgebraization
import Surreal.Surcomplex.FiniteFourier
import Surreal.Surcomplex.AlgebraicallyClosed
import Surreal.Surcomplex.TrigonometricPolynomialCayley

/-!
# Finite real-angle root bounds for trigonometric polynomials

The actual-field algebraic part of `trigonometry:thm:polyroots`: a finite
Laurent sum has at most twice its frequency bound many distinct finite
real-angle roots modulo ordinary periods. The same bound holds with native
polynomial multiplicities. `AngularLaurentEvaluation` identifies these with
orders of exact local angular strong series. The global exponential strip
remains a separate construction.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Finset

noncomputable section

/-- The existing native Laurent-polynomial evaluation equals its bounded Fourier sum. -/
theorem trigonometricPolynomial_eq_laurentSum
    (p : LaurentPolynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (θ : SignSequence.FiniteElement.{u}) :
    trigonometricPolynomial p θ = FiniteFourier.laurentEval N p.coeff (finitePhase θ) := by
  classical
  have hsub : p.coeff.support ⊆ Icc (-(N : ℤ)) N := by
    intro k hk
    have hb := hN k hk
    exact mem_Icc.mpr (by omega)
  unfold trigonometricPolynomial LaurentPolynomial.smeval FiniteFourier.laurentEval
  simp only [Finsupp.sum, smul_eq_mul, Units.val_zpow_eq_zpow_val, phaseUnit_val]
  apply sum_subset hsub
  intro k _ hk
  rw [Finsupp.notMem_support_iff.mp hk, zero_mul]

/-- A nonzero native Laurent polynomial has a nonzero coefficient inside every frequency bound. -/
theorem exists_laurent_coefficient_ne_zero
    (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃ k ∈ Icc (-(N : ℤ)) N, p.coeff k ≠ 0 := by
  classical
  by_contra! he
  apply hp
  apply LaurentPolynomial.ext
  intro k
  change p.coeff k = 0
  by_cases hk : k ∈ p.coeff.support
  · apply he k
    have hb := hN k hk
    exact mem_Icc.mpr (by omega)
  · exact Finsupp.notMem_support_iff.mp hk

/-- Clearing the negative frequencies preserves the zeros at every actual finite angle. -/
theorem laurentSum_zero_iff_polynomial_root (N : ℕ) (c : ℤ → Surcomplex.{u})
    (θ : SignSequence.FiniteElement.{u}) :
    FiniteFourier.laurentEval N c (finitePhase θ) = 0 ↔
      (LaurentAlgebraization.polynomial N c).IsRoot (finitePhase θ) :=
  (LaurentAlgebraization.isRoot_iff N c (finitePhase θ)
    (FiniteFourier.ne_zero_of_modulus_eq_one (modulus_finitePhase θ))).symm

/-- Any finite collection of roots with distinct phases satisfies the `2N` bound. -/
theorem card_laurentSum_roots_le (N : ℕ) (c : ℤ → Surcomplex.{u})
    (hc : ∃ k ∈ Icc (-(N : ℤ)) N, c k ≠ 0)
    (S : Finset SignSequence.FiniteElement.{u})
    (hS : ∀ θ ∈ S, FiniteFourier.laurentEval N c (finitePhase θ) = 0)
    (hinj : Set.InjOn finitePhase (S : Set SignSequence.FiniteElement.{u})) :
    S.card ≤ 2 * N := by
  classical
  have hp : LaurentAlgebraization.polynomial N c ≠ 0 := by
    rw [ne_eq, LaurentAlgebraization.polynomial_eq_zero_iff]
    obtain ⟨k, hk, hc⟩ := hc
    exact fun h => hc (h k hk)
  have hmap : Set.MapsTo finitePhase (S : Set SignSequence.FiniteElement.{u})
      ((LaurentAlgebraization.nonzeroRoots N c).toFinset : Set Surcomplex.{u}) := by
    intro θ hθ
    rw [Finset.mem_coe, Multiset.mem_toFinset,
      LaurentAlgebraization.mem_nonzeroRoots N c hp]
    exact ⟨FiniteFourier.ne_zero_of_modulus_eq_one (modulus_finitePhase θ), hS θ hθ⟩
  exact (Finset.card_le_card_of_injOn finitePhase hmap hinj).trans
    ((Multiset.toFinset_card_le _).trans (LaurentAlgebraization.card_nonzeroRoots_le N c))

/-- The bound also holds when the roots are weighted by their native polynomial multiplicities. -/
theorem sum_laurentSum_rootMultiplicities_le (N : ℕ) (c : ℤ → Surcomplex.{u})
    (hc : ∃ k ∈ Icc (-(N : ℤ)) N, c k ≠ 0)
    (S : Finset SignSequence.FiniteElement.{u})
    (hS : ∀ θ ∈ S, FiniteFourier.laurentEval N c (finitePhase θ) = 0)
    (hinj : Set.InjOn finitePhase (S : Set SignSequence.FiniteElement.{u})) :
    ∑ θ ∈ S, (LaurentAlgebraization.polynomial N c).rootMultiplicity (finitePhase θ) ≤
      2 * N := by
  classical
  let P := LaurentAlgebraization.polynomial N c
  have hp : P ≠ 0 := by
    rw [ne_eq, LaurentAlgebraization.polynomial_eq_zero_iff]
    obtain ⟨k, hk, hc⟩ := hc
    exact fun h => hc (h k hk)
  have hsub : S.image finitePhase ⊆ P.roots.toFinset := by
    intro z hz
    obtain ⟨θ, hθ, rfl⟩ := mem_image.mp hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact (laurentSum_zero_iff_polynomial_root N c θ).mp (hS θ hθ)
  calc
    ∑ θ ∈ S, P.rootMultiplicity (finitePhase θ) =
        ∑ z ∈ S.image finitePhase, P.rootMultiplicity z := (sum_image (f := fun z => P.rootMultiplicity z) hinj).symm
    _ ≤ ∑ z ∈ P.roots.toFinset, P.rootMultiplicity z := sum_le_sum_of_subset hsub
    _ = P.natDegree := by
      simpa only [Polynomial.count_roots, FinitePolynomial.roots_card] using
        Multiset.toFinset_sum_count_eq P.roots
    _ ≤ 2 * N := LaurentAlgebraization.natDegree_le N c

/-- Ordinary full-turn inequivalence is precisely the distinct-phase condition in the root bound. -/
theorem card_laurentSum_roots_mod_period_le (N : ℕ) (c : ℤ → Surcomplex.{u})
    (hc : ∃ k ∈ Icc (-(N : ℤ)) N, c k ≠ 0)
    (S : Finset SignSequence.FiniteElement.{u})
    (hS : ∀ θ ∈ S, FiniteFourier.laurentEval N c (finitePhase θ) = 0)
    (hperiod : ∀ θ ∈ S, ∀ φ ∈ S, ∀ n : ℤ,
      θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) → θ = φ) :
    S.card ≤ 2 * N := by
  apply card_laurentSum_roots_le N c hc S hS
  intro θ hθ φ hφ he
  obtain ⟨n, hn⟩ := (finitePhase_eq_iff θ φ).mp he
  exact hperiod θ hθ φ hφ n hn

/-- The `2N` bound for the library's existing native Laurent trigonometric polynomials. -/
theorem card_trigonometricPolynomial_roots_le
    (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (S : Finset SignSequence.FiniteElement.{u})
    (hS : ∀ θ ∈ S, trigonometricPolynomial p θ = 0)
    (hinj : Set.InjOn finitePhase (S : Set SignSequence.FiniteElement.{u})) :
    S.card ≤ 2 * N := by
  apply card_laurentSum_roots_le N p.coeff
    (exists_laurent_coefficient_ne_zero p hp N hN) S _ hinj
  intro θ hθ
  rw [← trigonometricPolynomial_eq_laurentSum p N hN θ]
  exact hS θ hθ

end
end Surreal.Surcomplex
