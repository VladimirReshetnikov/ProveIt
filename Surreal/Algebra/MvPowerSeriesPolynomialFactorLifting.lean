import Surreal.Algebra.MvPowerSeriesFactorLifting

/-!
# Polynomial factors over multivariate formal power series

The bounded multivariate coefficient recursion is packaged as actual polynomials
with coefficients in `MvPowerSeries σ R`. The resulting monic factors retain
the degrees and constant specializations of the coprime residue factors, and
are unique among all such polynomial factors. No restriction on the parameter
set is needed for this formal algebraic stage of `polynomial:thm:hensel`.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- Interchange the polynomial variable with the formal series parameters. -/
def polynomialMvSeriesEmbedding : (MvPowerSeries σ R)[X] →+* MvPowerSeries σ R[X] :=
  Polynomial.eval₂RingHom (MvPowerSeries.map Polynomial.C) (MvPowerSeries.C Polynomial.X)

/-- The variable interchange preserves each double coefficient. -/
theorem coeff_coeff_polynomialMvSeriesEmbedding (P : (MvPowerSeries σ R)[X])
    (d : σ →₀ ℕ) (j : ℕ) :
    (MvPowerSeries.coeff d (polynomialMvSeriesEmbedding P)).coeff j =
      MvPowerSeries.coeff d (P.coeff j) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]
  | monomial k a =>
    rw [polynomialMvSeriesEmbedding, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
    rw [← map_pow, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_map,
      Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coeff_monomial, apply_ite, map_zero]
    split_ifs <;> rfl

/-- Variable interchange is injective. -/
theorem polynomialMvSeriesEmbedding_injective :
    Function.Injective
      (polynomialMvSeriesEmbedding : (MvPowerSeries σ R)[X] → MvPowerSeries σ R[X]) := by
  intro P Q h
  apply Polynomial.ext
  intro j
  apply MvPowerSeries.ext
  intro d
  simpa only [coeff_coeff_polynomialMvSeriesEmbedding] using
    congrArg (fun F : MvPowerSeries σ R[X] => (MvPowerSeries.coeff d F).coeff j) h

/-- The formal coefficient series of a fixed polynomial power. -/
def mvPolynomialCoefficientSeries (F : MvPowerSeries σ R[X]) (j : ℕ) :
    MvPowerSeries σ R := fun d => (MvPowerSeries.coeff d F).coeff j

@[simp] theorem coeff_mvPolynomialCoefficientSeries (F : MvPowerSeries σ R[X])
    (j : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (mvPolynomialCoefficientSeries F j) =
      (MvPowerSeries.coeff d F).coeff j := rfl

/-- Reconstruct a polynomial from a multivariate series with a uniform degree bound. -/
def polynomialOfBoundedMvSeries (n : ℕ) (F : MvPowerSeries σ R[X]) : (MvPowerSeries σ R)[X] :=
  ∑ j ∈ Finset.range n,
    Polynomial.monomial j (mvPolynomialCoefficientSeries F j)

theorem coeff_polynomialOfBoundedMvSeries (n : ℕ) (F : MvPowerSeries σ R[X]) (j : ℕ) :
    (polynomialOfBoundedMvSeries n F).coeff j =
      if j < n then mvPolynomialCoefficientSeries F j else 0 := by
  classical
  simp [polynomialOfBoundedMvSeries, Polynomial.coeff_monomial, Finset.mem_range]

theorem degree_polynomialOfBoundedMvSeries_lt (n : ℕ) (F : MvPowerSeries σ R[X]) :
    (polynomialOfBoundedMvSeries n F).degree < n := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_polynomialOfBoundedMvSeries, if_neg (Nat.not_lt.mpr hj)]

/-- Reconstruction is inverse to variable interchange on uniformly bounded series. -/
theorem polynomialMvSeriesEmbedding_polynomialOfBoundedMvSeries (n : ℕ)
    (F : MvPowerSeries σ R[X]) (hF : ∀ d, (MvPowerSeries.coeff d F).degree < n) :
    polynomialMvSeriesEmbedding (polynomialOfBoundedMvSeries n F) = F := by
  apply MvPowerSeries.ext
  intro d
  apply Polynomial.ext
  intro j
  rw [coeff_coeff_polynomialMvSeriesEmbedding, coeff_polynomialOfBoundedMvSeries]
  split_ifs with hj
  · rfl
  · rw [map_zero]
    exact ((Polynomial.degree_lt_iff_coeff_zero _ _).mp (hF d) j (Nat.le_of_not_gt hj)).symm

@[simp] theorem polynomialMvSeriesEmbedding_C (a : MvPowerSeries σ R) :
    polynomialMvSeriesEmbedding (Polynomial.C a) = MvPowerSeries.map Polynomial.C a :=
  Polynomial.eval₂_C _ _

@[simp] theorem polynomialMvSeriesEmbedding_map_C (p : R[X]) :
    polynomialMvSeriesEmbedding (p.map (MvPowerSeries.C (σ := σ))) = MvPowerSeries.C p := by
  apply MvPowerSeries.ext
  intro d
  apply Polynomial.ext
  intro j
  rw [coeff_coeff_polynomialMvSeriesEmbedding, Polynomial.coeff_map]
  by_cases hd : d = 0
  · subst d
    simp
  · simp [MvPowerSeries.coeff_C_of_ne_zero hd]

/-- Constant specialization commutes with the variable interchange. -/
theorem map_constantCoeff_eq_coeff_zero_mvEmbedding (P : (MvPowerSeries σ R)[X]) :
    P.map MvPowerSeries.constantCoeff = MvPowerSeries.coeff 0 (polynomialMvSeriesEmbedding P) := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_map, coeff_coeff_polynomialMvSeriesEmbedding,
    MvPowerSeries.coeff_zero_eq_constantCoeff]

private theorem mvSeries_degree_bound_of_constant_and_nonzero (p : R[X])
    (F : MvPowerSeries σ R[X]) (hF₀ : MvPowerSeries.constantCoeff F = p)
    (hF : ∀ d, d ≠ 0 → (MvPowerSeries.coeff d F).degree < p.natDegree) :
    ∀ d, (MvPowerSeries.coeff d F).degree < p.natDegree + 1 := by
  intro d
  by_cases hd : d = 0
  · subst d
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff, hF₀]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self p.natDegree)
  · exact (hF d hd).trans (by exact_mod_cast Nat.lt_succ_self p.natDegree)

private theorem natDegree_polynomialOfBoundedMvSeries_succ_le (n : ℕ)
    (F : MvPowerSeries σ R[X]) :
    (polynomialOfBoundedMvSeries (n + 1) F).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_polynomialOfBoundedMvSeries, if_neg (by omega)]

private theorem topCoeff_polynomialOfBoundedMvSeries (p : R[X]) (hp : p.Monic)
    (F : MvPowerSeries σ R[X]) (hF₀ : MvPowerSeries.constantCoeff F = p)
    (hF : ∀ d, d ≠ 0 → (MvPowerSeries.coeff d F).degree < p.natDegree) :
    (polynomialOfBoundedMvSeries (p.natDegree + 1) F).coeff p.natDegree = 1 := by
  rw [coeff_polynomialOfBoundedMvSeries, if_pos (Nat.lt_succ_self _)]
  apply MvPowerSeries.ext
  intro d
  rw [coeff_mvPolynomialCoefficientSeries]
  by_cases hd : d = 0
  · subst d
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff, hF₀, hp.coeff_natDegree, map_one]
  · rw [Polynomial.coeff_eq_zero_of_degree_lt (hF d hd)]
    classical
    simp [MvPowerSeries.coeff_one, hd]

/-- A monic constant term and lower-degree nonconstant coefficients reconstruct
as a monic polynomial. -/
theorem monic_polynomialOfBoundedMvSeries (p : R[X]) (hp : p.Monic)
    (F : MvPowerSeries σ R[X]) (hF₀ : MvPowerSeries.constantCoeff F = p)
    (hF : ∀ d, d ≠ 0 → (MvPowerSeries.coeff d F).degree < p.natDegree) :
    (polynomialOfBoundedMvSeries (p.natDegree + 1) F).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one p.natDegree
    (natDegree_polynomialOfBoundedMvSeries_succ_le _ _)
    (topCoeff_polynomialOfBoundedMvSeries p hp F hF₀ hF)

theorem natDegree_polynomialOfBoundedMvSeries [Nontrivial R] (p : R[X]) (hp : p.Monic)
    (F : MvPowerSeries σ R[X]) (hF₀ : MvPowerSeries.constantCoeff F = p)
    (hF : ∀ d, d ≠ 0 → (MvPowerSeries.coeff d F).degree < p.natDegree) :
    (polynomialOfBoundedMvSeries (p.natDegree + 1) F).natDegree = p.natDegree :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_polynomialOfBoundedMvSeries_succ_le _ _)
    (by rw [topCoeff_polynomialOfBoundedMvSeries p hp F hF₀ hF]; exact one_ne_zero)

/-- Nonconstant parameter coefficients of a monic polynomial have strictly
smaller polynomial degree. -/
theorem degree_coeff_mvEmbedding_lt (P : (MvPowerSeries σ R)[X]) (hP : P.Monic)
    {d : σ →₀ ℕ} (hd : d ≠ 0) :
    (MvPowerSeries.coeff d (polynomialMvSeriesEmbedding P)).degree < P.natDegree := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_coeff_polynomialMvSeriesEmbedding]
  obtain rfl | hlt := hj.eq_or_lt
  · rw [hP.coeff_natDegree]
    classical
    simp [MvPowerSeries.coeff_one, hd]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero]


/-- Coprimeness of the constant specializations implies coprimeness of monic
polynomials over multivariate formal power series. -/
theorem isCoprime_of_mvConstant_specialization [Nontrivial R]
    (P Q : (MvPowerSeries σ R)[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hc : IsCoprime (P.map MvPowerSeries.constantCoeff) (Q.map MvPowerSeries.constantCoeff)) :
    IsCoprime P Q := by
  apply (Polynomial.isUnit_resultant_iff_isCoprime hP).mp
  apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← Polynomial.resultant_map_map, ← hP.natDegree_map MvPowerSeries.constantCoeff,
    ← hQ.natDegree_map MvPowerSeries.constantCoeff]
  exact (Polynomial.isUnit_resultant_iff_isCoprime (hP.map MvPowerSeries.constantCoeff)).mpr hc

/-- Binary monic Hensel factorization for an arbitrary polynomial over the
multivariate formal series ring. Monicity and the constant specialization imply
the required degree equality; no prospective lift is assumed. -/
theorem existsUnique_monic_factorization_over_mvPowerSeries [Nontrivial R]
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) (hpq : IsCoprime p q)
    (H : (MvPowerSeries σ R)[X]) (hH : H.Monic)
    (hH₀ : H.map MvPowerSeries.constantCoeff = p * q) :
    ∃! PQ : (MvPowerSeries σ R)[X] × (MvPowerSeries σ R)[X],
      PQ.1.Monic ∧ PQ.2.Monic ∧ PQ.1.natDegree = p.natDegree ∧ PQ.2.natDegree = q.natDegree ∧
      PQ.1.map MvPowerSeries.constantCoeff = p ∧ PQ.2.map MvPowerSeries.constantCoeff = q ∧
      IsCoprime PQ.1 PQ.2 ∧ PQ.1 * PQ.2 = H := by
  have hHd : H.natDegree = p.natDegree + q.natDegree := by
    rw [← hH.natDegree_map MvPowerSeries.constantCoeff, hH₀, hp.natDegree_mul hq]
  have hconst : MvPowerSeries.constantCoeff (polynomialMvSeriesEmbedding H) = p * q := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff,
      ← map_constantCoeff_eq_coeff_zero_mvEmbedding, hH₀]
  obtain ⟨⟨F, G⟩, ⟨hF₀, hG₀, hF, hG, hFG⟩, huniq⟩ :=
    existsUnique_mvFormal_factorization p q hp hpq (polynomialMvSeriesEmbedding H) hconst
      (fun d hd => by simpa only [hHd] using degree_coeff_mvEmbedding_lt H hH hd)
  let P := polynomialOfBoundedMvSeries (p.natDegree + 1) F
  let Q := polynomialOfBoundedMvSeries (q.natDegree + 1) G
  have hPe : polynomialMvSeriesEmbedding P = F :=
    polynomialMvSeriesEmbedding_polynomialOfBoundedMvSeries _ _
      (mvSeries_degree_bound_of_constant_and_nonzero p F hF₀ hF)
  have hQe : polynomialMvSeriesEmbedding Q = G :=
    polynomialMvSeriesEmbedding_polynomialOfBoundedMvSeries _ _
      (mvSeries_degree_bound_of_constant_and_nonzero q G hG₀ hG)
  have hP : P.Monic := monic_polynomialOfBoundedMvSeries p hp F hF₀ hF
  have hQ : Q.Monic := monic_polynomialOfBoundedMvSeries q hq G hG₀ hG
  have hP₀ : P.map MvPowerSeries.constantCoeff = p := by
    rw [map_constantCoeff_eq_coeff_zero_mvEmbedding, hPe,
      MvPowerSeries.coeff_zero_eq_constantCoeff, hF₀]
  have hQ₀ : Q.map MvPowerSeries.constantCoeff = q := by
    rw [map_constantCoeff_eq_coeff_zero_mvEmbedding, hQe,
      MvPowerSeries.coeff_zero_eq_constantCoeff, hG₀]
  have hPQ : IsCoprime P Q := isCoprime_of_mvConstant_specialization P Q hP hQ
    (by rw [hP₀, hQ₀]; exact hpq)
  refine ⟨⟨P, Q⟩, ⟨hP, hQ, natDegree_polynomialOfBoundedMvSeries p hp F hF₀ hF,
    natDegree_polynomialOfBoundedMvSeries q hq G hG₀ hG, hP₀, hQ₀, hPQ, ?_⟩, ?_⟩
  · apply polynomialMvSeriesEmbedding_injective
    rw [map_mul, hPe, hQe, hFG]
  · rintro ⟨P', Q'⟩ ⟨hP', hQ', hPd, hQd, hP'₀, hQ'₀, _, hP'Q'⟩
    have hconstP : MvPowerSeries.constantCoeff (polynomialMvSeriesEmbedding P') = p := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff,
        ← map_constantCoeff_eq_coeff_zero_mvEmbedding, hP'₀]
    have hconstQ : MvPowerSeries.constantCoeff (polynomialMvSeriesEmbedding Q') = q := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff,
        ← map_constantCoeff_eq_coeff_zero_mvEmbedding, hQ'₀]
    have hpair := huniq ⟨polynomialMvSeriesEmbedding P', polynomialMvSeriesEmbedding Q'⟩
      ⟨hconstP, hconstQ,
        fun d hd => by simpa only [hPd] using degree_coeff_mvEmbedding_lt P' hP' hd,
        fun d hd => by simpa only [hQd] using degree_coeff_mvEmbedding_lt Q' hQ' hd,
        by rw [← map_mul, hP'Q']⟩
    apply Prod.ext
    · apply polynomialMvSeriesEmbedding_injective
      rw [hPe]
      exact congrArg Prod.fst hpair
    · apply polynomialMvSeriesEmbedding_injective
      rw [hQe]
      exact congrArg Prod.snd hpair

end

end Surreal.FinitePolynomial
