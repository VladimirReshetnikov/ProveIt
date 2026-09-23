import Surreal.Surcomplex.TrigonometricPolynomialRootCount

/-!
# Fourier coefficient uniqueness and reality

These are the coefficient assertions preceding and following
`trigonometry:thm:polyroots`. Values at ordinary real angles already determine
all coefficients of a finite Fourier sum over the actual surcomplex field.
Reality on finite angles is equivalent to conjugate symmetry of coefficients.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Finset

noncomputable section

/-- Agreement at all ordinary angles forces agreement of every coefficient in the window. -/
theorem laurentSum_coeff_eq_of_ordinary_angles (N : ℕ) (c d : ℤ → Surcomplex.{u})
    (h : ∀ x : ℝ,
      FiniteFourier.laurentEval N c (finitePhase (SignSequence.finiteOfReal x)) =
        FiniteFourier.laurentEval N d (finitePhase (SignSequence.finiteOfReal x)))
    (k : ℤ) (hk : |k| ≤ N) : c k = d k := by
  let M := 2 * N + 1
  have hM : 2 * N < M := by omega
  have hs : ∀ j : ℕ, FiniteFourier.zeta M ^ j =
      finitePhase (SignSequence.finiteOfReal ((j : ℝ) * (2 * Real.pi / M))) := by
    intro j
    rw [FiniteFourier.zeta, ← finitePhase_nsmul, ← map_nsmul, nsmul_eq_mul]
  rw [FiniteFourier.surcomplex_fourier_inversion hM c (u₀ := 1) one_ne_zero hk,
    FiniteFourier.surcomplex_fourier_inversion hM d (u₀ := 1) one_ne_zero hk]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [one_mul, hs, h]

/-- A finite Laurent sum vanishing at every ordinary angle has every Fourier coefficient zero. -/
theorem laurentSum_eq_zero_of_ordinary_angles (N : ℕ) (c : ℤ → Surcomplex.{u})
    (h : ∀ x : ℝ, FiniteFourier.laurentEval N c
      (finitePhase (SignSequence.finiteOfReal x)) = 0) :
    ∀ k ∈ Icc (-(N : ℤ)) N, c k = 0 := by
  intro k hk
  apply laurentSum_coeff_eq_of_ordinary_angles N c (fun _ => 0) _ k
    (abs_le.mpr (mem_Icc.mp hk))
  intro x
  simpa only [FiniteFourier.laurentEval, zero_mul, sum_const_zero] using h x

/-- Conjugating a Laurent sum on the actual circle reflects and conjugates its coefficients. -/
theorem conj_laurentSum (N : ℕ) (c : ℤ → Surcomplex.{u})
    (θ : SignSequence.FiniteElement.{u}) :
    conj (FiniteFourier.laurentEval N c (finitePhase θ)) =
      FiniteFourier.laurentEval N (fun k => conj (c (-k))) (finitePhase θ) := by
  classical
  change star (FiniteFourier.laurentEval N c (finitePhase θ)) = _
  rw [FiniteFourier.star_laurentEval c
    (FiniteFourier.star_eq_inv_of_modulus_eq_one (modulus_finitePhase θ))]
  unfold FiniteFourier.laurentEval
  refine sum_bij (fun k _ => -k) ?_ ?_ ?_ ?_
  · intro k hk
    have hb := mem_Icc.mp hk
    exact mem_Icc.mpr (by omega)
  · intro a _ b _ he
    exact neg_injective he
  · intro k hk
    refine ⟨-k, mem_Icc.mpr ?_, by simp⟩
    have hb := mem_Icc.mp hk
    omega
  · intro k _
    simp only [neg_neg]
    rfl

/-- Real-valuedness at all finite angles is exactly conjugate symmetry of the Fourier coefficients. -/
theorem laurentSum_real_iff (N : ℕ) (c : ℤ → Surcomplex.{u}) :
    (∀ θ : SignSequence.FiniteElement.{u},
      (FiniteFourier.laurentEval N c (finitePhase θ)).im = 0) ↔
      ∀ k ∈ Icc (-(N : ℤ)) N, c (-k) = conj (c k) := by
  classical
  constructor
  · intro h k hk
    have he : c k = conj (c (-k)) := by
      apply laurentSum_coeff_eq_of_ordinary_angles N c (fun j => conj (c (-j))) _ k
        (abs_le.mpr (mem_Icc.mp hk))
      intro x
      rw [← conj_laurentSum]
      apply QuadraticAlgebra.ext
      · simp only [conj_re]
      · rw [conj_im, h, neg_zero]
    have hh := congrArg conj he
    simpa only [conj_conj] using hh.symm
  · intro h θ
    have he : conj (FiniteFourier.laurentEval N c (finitePhase θ)) =
        FiniteFourier.laurentEval N c (finitePhase θ) := by
      rw [conj_laurentSum]
      unfold FiniteFourier.laurentEval
      apply sum_congr rfl
      intro k hk
      dsimp only
      rw [h k hk, conj_conj]
    have hi := congrArg (fun z : Surcomplex.{u} => z.im) he
    rw [conj_im] at hi
    linarith

/-- Native Laurent polynomials are determined by their trigonometric values at ordinary angles. -/
theorem trigonometricPolynomial_eq_of_ordinary_angles
    (p q : LaurentPolynomial Surcomplex.{u})
    (h : ∀ x : ℝ, trigonometricPolynomial p (SignSequence.finiteOfReal x) =
      trigonometricPolynomial q (SignSequence.finiteOfReal x)) : p = q := by
  obtain ⟨M, hM⟩ := LaurentCayley.exists_frequency_bound p
  obtain ⟨L, hL⟩ := LaurentCayley.exists_frequency_bound q
  let N := max M L
  have hp : ∀ k ∈ p.coeff.support, k.natAbs ≤ N := fun k hk => (hM k hk).trans (le_max_left _ _)
  have hq : ∀ k ∈ q.coeff.support, k.natAbs ≤ N := fun k hk => (hL k hk).trans (le_max_right _ _)
  apply LaurentPolynomial.ext
  intro k
  by_cases hk : k.natAbs ≤ N
  · apply laurentSum_coeff_eq_of_ordinary_angles N p.coeff q.coeff _ k (by
      simpa only [Int.natCast_natAbs] using
        (show (k.natAbs : ℤ) ≤ (N : ℤ) by exact_mod_cast hk))
    intro x
    rw [← trigonometricPolynomial_eq_laurentSum p N hp,
      ← trigonometricPolynomial_eq_laurentSum q N hq]
    exact h x
  · have hpk : k ∉ p.coeff.support := fun hm => hk (hp k hm)
    have hqk : k ∉ q.coeff.support := fun hm => hk (hq k hm)
    rw [Finsupp.notMem_support_iff.mp hpk, Finsupp.notMem_support_iff.mp hqk]

/-- No nonzero native Laurent polynomial vanishes at every ordinary real angle. -/
theorem exists_ordinary_angle_trigonometricPolynomial_ne_zero
    (p : LaurentPolynomial Surcomplex.{u}) (hp : p ≠ 0) :
    ∃ x : ℝ, trigonometricPolynomial p (SignSequence.finiteOfReal x) ≠ 0 := by
  by_contra! h
  apply hp
  apply trigonometricPolynomial_eq_of_ordinary_angles p 0
  intro x
  rw [h]
  simp only [trigonometricPolynomial, LaurentPolynomial.smeval_zero]

/-- Reality of a native Laurent trigonometric polynomial is equivalent to symmetry at every frequency. -/
theorem trigonometricPolynomial_real_iff (p : LaurentPolynomial Surcomplex.{u}) :
    (∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0) ↔
      ∀ k : ℤ, p.coeff (-k) = conj (p.coeff k) := by
  obtain ⟨N, hN⟩ := LaurentCayley.exists_frequency_bound p
  have hr : (∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0) ↔
      ∀ k ∈ Icc (-(N : ℤ)) N, p.coeff (-k) = conj (p.coeff k) := by
    simpa only [trigonometricPolynomial_eq_laurentSum p N hN] using
      laurentSum_real_iff N p.coeff
  constructor
  · intro h k
    by_cases hk : k.natAbs ≤ N
    · exact hr.mp h k (mem_Icc.mpr (by omega))
    · have hp : k ∉ p.coeff.support := fun hm => hk (hN k hm)
      have hm : -k ∉ p.coeff.support := by
        intro hm
        exact hk (by simpa only [Int.natAbs_neg] using hN (-k) hm)
      rw [Finsupp.notMem_support_iff.mp hp, Finsupp.notMem_support_iff.mp hm, map_zero]
  · intro h
    exact hr.mpr (fun k _ => h k)

end
end Surreal.Surcomplex
