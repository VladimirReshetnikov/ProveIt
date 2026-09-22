import Surreal.Algebra.PowerSeriesFactorLifting

/-!
# Polynomial factors with formal power-series coefficients

The coefficient recursion in `PowerSeriesFactorLifting` produces power series
whose coefficients are uniformly bounded-degree polynomials. This module
interchanges the two variables and packages the result as actual polynomials
over `PowerSeries R`, preserving multiplication, constant specialization,
and the prescribed monic degrees.

This is the formal-parameter stage of `polynomial:thm:hensel`; evaluation in
general Hahn fields and arbitrary support-monoid recursion remain separate.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- Interchange the polynomial variable and the formal parameter. The polynomial
variable becomes a constant series of polynomials, and each coefficient series
is embedded coefficientwise as constant polynomials. -/
def polynomialSeriesEmbedding : (PowerSeries R)[X] →+* PowerSeries R[X] :=
  Polynomial.eval₂RingHom (PowerSeries.map Polynomial.C) (PowerSeries.C Polynomial.X)

/-- The variable interchange has the expected double-coefficient formula. -/
theorem coeff_coeff_polynomialSeriesEmbedding (P : (PowerSeries R)[X]) (n j : ℕ) :
    (PowerSeries.coeff n (polynomialSeriesEmbedding P)).coeff j =
      PowerSeries.coeff n (P.coeff j) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, coeff_add, hP, hQ]
  | monomial k a =>
    rw [polynomialSeriesEmbedding, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_map,
      Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coeff_monomial, apply_ite, map_zero]
    split_ifs <;> rfl

/-- Variable interchange loses no information. -/
theorem polynomialSeriesEmbedding_injective :
    Function.Injective (polynomialSeriesEmbedding : (PowerSeries R)[X] → PowerSeries R[X]) := by
  intro P Q h
  apply Polynomial.ext
  intro j
  apply PowerSeries.ext
  intro n
  simpa only [coeff_coeff_polynomialSeriesEmbedding] using
    congrArg (fun F : PowerSeries R[X] => (PowerSeries.coeff n F).coeff j) h

/-- Reconstruct a polynomial from a formal series with the declared uniform degree bound. -/
def polynomialOfBoundedSeries (d : ℕ) (F : PowerSeries R[X]) : (PowerSeries R)[X] :=
  ∑ j ∈ Finset.range d,
    Polynomial.monomial j (PowerSeries.mk fun n => (PowerSeries.coeff n F).coeff j)

theorem coeff_polynomialOfBoundedSeries (d : ℕ) (F : PowerSeries R[X]) (j : ℕ) :
    (polynomialOfBoundedSeries d F).coeff j =
      if j < d then PowerSeries.mk (fun n => (PowerSeries.coeff n F).coeff j) else 0 := by
  classical
  simp [polynomialOfBoundedSeries, Polynomial.coeff_monomial, Finset.mem_range]

/-- The reconstructed polynomial has degree below its uniform bound. -/
theorem degree_polynomialOfBoundedSeries_lt (d : ℕ) (F : PowerSeries R[X]) :
    (polynomialOfBoundedSeries d F).degree < d := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_polynomialOfBoundedSeries, if_neg (Nat.not_lt.mpr hj)]

/-- The bounded reconstruction is a genuine inverse, coefficient by coefficient. -/
theorem polynomialSeriesEmbedding_polynomialOfBoundedSeries (d : ℕ) (F : PowerSeries R[X])
    (hF : ∀ n, (PowerSeries.coeff n F).degree < d) :
    polynomialSeriesEmbedding (polynomialOfBoundedSeries d F) = F := by
  apply PowerSeries.ext
  intro n
  apply Polynomial.ext
  intro j
  rw [coeff_coeff_polynomialSeriesEmbedding, coeff_polynomialOfBoundedSeries]
  split_ifs with hj
  · exact PowerSeries.coeff_mk _ _
  · rw [map_zero]
    exact ((Polynomial.degree_lt_iff_coeff_zero _ _).mp (hF n) j (Nat.le_of_not_gt hj)).symm

@[simp] theorem polynomialSeriesEmbedding_C (a : PowerSeries R) :
    polynomialSeriesEmbedding (Polynomial.C a) = PowerSeries.map Polynomial.C a :=
  Polynomial.eval₂_C _ _

/-- Ordinary coefficient polynomials become constant formal series. -/
@[simp] theorem polynomialSeriesEmbedding_map_C (p : R[X]) :
    polynomialSeriesEmbedding (p.map PowerSeries.C) = PowerSeries.C p := by
  apply PowerSeries.ext
  intro n
  apply Polynomial.ext
  intro j
  rw [coeff_coeff_polynomialSeriesEmbedding, Polynomial.coeff_map]
  simp only [PowerSeries.coeff_C]
  split_ifs <;> rfl

/-- Specialization at formal parameter zero commutes with variable interchange. -/
theorem map_constantCoeff_eq_coeff_zero_embedding (P : (PowerSeries R)[X]) :
    P.map PowerSeries.constantCoeff = PowerSeries.coeff 0 (polynomialSeriesEmbedding P) := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_map, coeff_coeff_polynomialSeriesEmbedding,
    PowerSeries.coeff_zero_eq_constantCoeff]

private theorem series_degree_bound_of_constant_and_positive (p : R[X])
    (F : PowerSeries R[X]) (hF₀ : PowerSeries.constantCoeff F = p)
    (hF : ∀ n, (PowerSeries.coeff (n + 1) F).degree < p.natDegree) :
    ∀ n, (PowerSeries.coeff n F).degree < p.natDegree + 1 := by
  intro n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff, hF₀]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self p.natDegree)
  | succ n => exact (hF n).trans (by exact_mod_cast Nat.lt_succ_self p.natDegree)

private theorem natDegree_polynomialOfBoundedSeries_succ_le (d : ℕ) (F : PowerSeries R[X]) :
    (polynomialOfBoundedSeries (d + 1) F).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_polynomialOfBoundedSeries, if_neg (by omega)]

private theorem topCoeff_polynomialOfBoundedSeries (p : R[X]) (hp : p.Monic)
    (F : PowerSeries R[X]) (hF₀ : PowerSeries.constantCoeff F = p)
    (hF : ∀ n, (PowerSeries.coeff (n + 1) F).degree < p.natDegree) :
    (polynomialOfBoundedSeries (p.natDegree + 1) F).coeff p.natDegree = 1 := by
  rw [coeff_polynomialOfBoundedSeries, if_pos (Nat.lt_succ_self _)]
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk]
  cases n with
  | zero => simp only [PowerSeries.coeff_zero_eq_constantCoeff, hF₀, hp.coeff_natDegree, map_one]
  | succ n =>
    rw [Polynomial.coeff_eq_zero_of_degree_lt (hF n)]
    simp

/-- A bounded series with a monic constant factor and strictly lower-degree
positive coefficients reconstructs to a monic polynomial. -/
theorem monic_polynomialOfBoundedSeries (p : R[X]) (hp : p.Monic)
    (F : PowerSeries R[X]) (hF₀ : PowerSeries.constantCoeff F = p)
    (hF : ∀ n, (PowerSeries.coeff (n + 1) F).degree < p.natDegree) :
    (polynomialOfBoundedSeries (p.natDegree + 1) F).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one p.natDegree
    (natDegree_polynomialOfBoundedSeries_succ_le _ _)
    (topCoeff_polynomialOfBoundedSeries p hp F hF₀ hF)

theorem natDegree_polynomialOfBoundedSeries [Nontrivial R] (p : R[X]) (hp : p.Monic)
    (F : PowerSeries R[X]) (hF₀ : PowerSeries.constantCoeff F = p)
    (hF : ∀ n, (PowerSeries.coeff (n + 1) F).degree < p.natDegree) :
    (polynomialOfBoundedSeries (p.natDegree + 1) F).natDegree = p.natDegree :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_polynomialOfBoundedSeries_succ_le _ _)
    (by rw [topCoeff_polynomialOfBoundedSeries p hp F hF₀ hF]; exact one_ne_zero)

/-- The left formal lift packaged as an actual polynomial over power series. -/
def liftedLeftPolynomial (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) : (PowerSeries R)[X] :=
  polynomialOfBoundedSeries (p.natDegree + 1) (liftedLeftFactor p q hp hpq e)

/-- The right formal lift packaged as an actual polynomial over power series. -/
def liftedRightPolynomial (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) : (PowerSeries R)[X] :=
  polynomialOfBoundedSeries (q.natDegree + 1) (liftedRightFactor p q hp hpq e)

/-- The prescribed error is uniformly bounded in the polynomial variable. -/
def factorErrorPolynomial (p q : R[X])
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) : (PowerSeries R)[X] :=
  polynomialOfBoundedSeries (p.natDegree + q.natDegree) (factorErrorSeries p q e)

/-- The actual polynomial input is the original product plus parameter times error. -/
def factorInputPolynomial (p q : R[X])
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) : (PowerSeries R)[X] :=
  (p * q).map PowerSeries.C + Polynomial.C PowerSeries.X * factorErrorPolynomial p q e

@[simp] theorem polynomialSeriesEmbedding_liftedLeftPolynomial (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    polynomialSeriesEmbedding (liftedLeftPolynomial p q hp hpq e) = liftedLeftFactor p q hp hpq e :=
  polynomialSeriesEmbedding_polynomialOfBoundedSeries _ _
    (series_degree_bound_of_constant_and_positive p _ (constantCoeff_liftedLeftFactor p q hp hpq e)
      (degree_coeff_liftedLeftFactor_succ_lt p q hp hpq e))

@[simp] theorem polynomialSeriesEmbedding_liftedRightPolynomial (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    polynomialSeriesEmbedding (liftedRightPolynomial p q hp hpq e) = liftedRightFactor p q hp hpq e :=
  polynomialSeriesEmbedding_polynomialOfBoundedSeries _ _
    (series_degree_bound_of_constant_and_positive q _ (constantCoeff_liftedRightFactor p q hp hpq e)
      (degree_coeff_liftedRightFactor_succ_lt p q hp hpq e))

@[simp] theorem polynomialSeriesEmbedding_factorErrorPolynomial (p q : R[X])
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    polynomialSeriesEmbedding (factorErrorPolynomial p q e) = factorErrorSeries p q e :=
  polynomialSeriesEmbedding_polynomialOfBoundedSeries _ _ (fun n => by
    simpa only [factorErrorSeries, PowerSeries.coeff_mk] using mem_degreeLT.mp (e n).property)

@[simp] theorem polynomialSeriesEmbedding_factorInputPolynomial (p q : R[X])
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    polynomialSeriesEmbedding (factorInputPolynomial p q e) =
      PowerSeries.C (p * q) + PowerSeries.X * factorErrorSeries p q e := by
  simp only [factorInputPolynomial, map_add, map_mul, polynomialSeriesEmbedding_map_C,
    polynomialSeriesEmbedding_C, PowerSeries.map_X, polynomialSeriesEmbedding_factorErrorPolynomial]

/-- Exact factorization in the polynomial ring over the formal coefficient ring. -/
theorem liftedPolynomials_mul (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    liftedLeftPolynomial p q hp hpq e * liftedRightPolynomial p q hp hpq e =
      factorInputPolynomial p q e := by
  apply polynomialSeriesEmbedding_injective
  simpa only [map_mul, polynomialSeriesEmbedding_liftedLeftPolynomial,
    polynomialSeriesEmbedding_liftedRightPolynomial, polynomialSeriesEmbedding_factorInputPolynomial]
    using liftedFactors_mul p q hp hpq e

theorem liftedLeftPolynomial_monic (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    (liftedLeftPolynomial p q hp hpq e).Monic :=
  monic_polynomialOfBoundedSeries p hp _ (constantCoeff_liftedLeftFactor p q hp hpq e)
    (degree_coeff_liftedLeftFactor_succ_lt p q hp hpq e)

theorem liftedRightPolynomial_monic (p q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    (liftedRightPolynomial p q hp hpq e).Monic :=
  monic_polynomialOfBoundedSeries q hq _ (constantCoeff_liftedRightFactor p q hp hpq e)
    (degree_coeff_liftedRightFactor_succ_lt p q hp hpq e)

theorem liftedLeftPolynomial_natDegree [Nontrivial R] (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    (liftedLeftPolynomial p q hp hpq e).natDegree = p.natDegree :=
  natDegree_polynomialOfBoundedSeries p hp _ (constantCoeff_liftedLeftFactor p q hp hpq e)
    (degree_coeff_liftedLeftFactor_succ_lt p q hp hpq e)

theorem liftedRightPolynomial_natDegree [Nontrivial R] (p q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    (liftedRightPolynomial p q hp hpq e).natDegree = q.natDegree :=
  natDegree_polynomialOfBoundedSeries q hq _ (constantCoeff_liftedRightFactor p q hp hpq e)
    (degree_coeff_liftedRightFactor_succ_lt p q hp hpq e)

@[simp] theorem liftedLeftPolynomial_map_constantCoeff (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    (liftedLeftPolynomial p q hp hpq e).map PowerSeries.constantCoeff = p := by
  rw [map_constantCoeff_eq_coeff_zero_embedding, polynomialSeriesEmbedding_liftedLeftPolynomial,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_liftedLeftFactor]

@[simp] theorem liftedRightPolynomial_map_constantCoeff (p q : R[X]) (hp : p.Monic)
    (hpq : IsCoprime p q) (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    (liftedRightPolynomial p q hp hpq e).map PowerSeries.constantCoeff = q := by
  rw [map_constantCoeff_eq_coeff_zero_embedding, polynomialSeriesEmbedding_liftedRightPolynomial,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_liftedRightFactor]

private theorem degree_coeff_embedding_succ_lt (P : (PowerSeries R)[X]) (hP : P.Monic) (n : ℕ) :
    (PowerSeries.coeff (n + 1) (polynomialSeriesEmbedding P)).degree < P.natDegree := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_coeff_polynomialSeriesEmbedding]
  obtain rfl | hlt := hj.eq_or_lt
  · rw [hP.coeff_natDegree]
    simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero]

/-- Uniqueness in the actual polynomial ring, among all monic factors of the
prescribed degrees and constant specializations. -/
theorem liftedPolynomials_unique (p q : R[X]) (hp : p.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) (P Q : (PowerSeries R)[X])
    (hP : P.Monic) (hQ : Q.Monic)
    (hPd : P.natDegree = p.natDegree) (hQd : Q.natDegree = q.natDegree)
    (hP₀ : P.map PowerSeries.constantCoeff = p) (hQ₀ : Q.map PowerSeries.constantCoeff = q)
    (hPQ : P * Q = factorInputPolynomial p q e) :
    P = liftedLeftPolynomial p q hp hpq e ∧ Q = liftedRightPolynomial p q hp hpq e := by
  have hcP : PowerSeries.constantCoeff (polynomialSeriesEmbedding P) = p := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← map_constantCoeff_eq_coeff_zero_embedding, hP₀]
  have hcQ : PowerSeries.constantCoeff (polynomialSeriesEmbedding Q) = q := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← map_constantCoeff_eq_coeff_zero_embedding, hQ₀]
  obtain ⟨hF, hG⟩ := liftedFactors_unique p q hp hpq e
    (polynomialSeriesEmbedding P) (polynomialSeriesEmbedding Q) hcP hcQ
    (fun n => by simpa only [hPd] using degree_coeff_embedding_succ_lt P hP n)
    (fun n => by simpa only [hQd] using degree_coeff_embedding_succ_lt Q hQ n)
    (by rw [← map_mul, hPQ, polynomialSeriesEmbedding_factorInputPolynomial])
  constructor
  · apply polynomialSeriesEmbedding_injective
    simpa only [polynomialSeriesEmbedding_liftedLeftPolynomial] using hF
  · apply polynomialSeriesEmbedding_injective
    simpa only [polynomialSeriesEmbedding_liftedRightPolynomial] using hG

/-- Binary formal Hensel factorization as actual polynomials over `PowerSeries R`. -/
theorem existsUnique_monic_powerSeries_polynomial_factors [Nontrivial R]
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    ∃! PQ : (PowerSeries R)[X] × (PowerSeries R)[X],
      PQ.1.Monic ∧ PQ.2.Monic ∧ PQ.1.natDegree = p.natDegree ∧ PQ.2.natDegree = q.natDegree ∧
      PQ.1.map PowerSeries.constantCoeff = p ∧ PQ.2.map PowerSeries.constantCoeff = q ∧
      PQ.1 * PQ.2 = factorInputPolynomial p q e := by
  refine ⟨⟨liftedLeftPolynomial p q hp hpq e, liftedRightPolynomial p q hp hpq e⟩,
    ⟨liftedLeftPolynomial_monic p q hp hpq e, liftedRightPolynomial_monic p q hp hq hpq e,
      liftedLeftPolynomial_natDegree p q hp hpq e, liftedRightPolynomial_natDegree p q hp hq hpq e,
      liftedLeftPolynomial_map_constantCoeff p q hp hpq e,
      liftedRightPolynomial_map_constantCoeff p q hp hpq e, liftedPolynomials_mul p q hp hpq e⟩, ?_⟩
  rintro ⟨P, Q⟩ ⟨hP, hQ, hPd, hQd, hP₀, hQ₀, hPQ⟩
  obtain ⟨hP', hQ'⟩ := liftedPolynomials_unique p q hp hpq e P Q hP hQ hPd hQd hP₀ hQ₀ hPQ
  exact Prod.ext hP' hQ'

/-- Coprimeness persists in the actual polynomial ring. The resultant has
the original unit resultant as its constant coefficient. -/
theorem liftedPolynomials_isCoprime [Nontrivial R] (p q : R[X])
    (hp : p.Monic) (hq : q.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    IsCoprime (liftedLeftPolynomial p q hp hpq e) (liftedRightPolynomial p q hp hpq e) := by
  apply (Polynomial.isUnit_resultant_iff_isCoprime (liftedLeftPolynomial_monic p q hp hpq e)).mp
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← Polynomial.resultant_map_map, liftedLeftPolynomial_map_constantCoeff,
    liftedRightPolynomial_map_constantCoeff, liftedLeftPolynomial_natDegree,
    liftedRightPolynomial_natDegree p q hp hq hpq e]
  exact (Polynomial.isUnit_resultant_iff_isCoprime hp).mpr hpq

theorem factorInputPolynomial_monic (p q : R[X])
    (hp : p.Monic) (hq : q.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    (factorInputPolynomial p q e).Monic := by
  rw [← liftedPolynomials_mul p q hp hpq e]
  exact (liftedLeftPolynomial_monic p q hp hpq e).mul (liftedRightPolynomial_monic p q hp hq hpq e)

theorem factorInputPolynomial_natDegree [Nontrivial R] (p q : R[X])
    (hp : p.Monic) (hq : q.Monic) (hpq : IsCoprime p q)
    (e : ℕ → degreeLT R (p.natDegree + q.natDegree)) :
    (factorInputPolynomial p q e).natDegree = p.natDegree + q.natDegree := by
  rw [← liftedPolynomials_mul p q hp hpq e,
    (liftedLeftPolynomial_monic p q hp hpq e).natDegree_mul
      (liftedRightPolynomial_monic p q hp hq hpq e),
    liftedLeftPolynomial_natDegree, liftedRightPolynomial_natDegree p q hp hq hpq e]

/-- Binary monic Hensel factorization for an arbitrary polynomial over the formal
power-series coefficient ring, stated using its ordinary constant specialization. -/
theorem existsUnique_monic_factorization_over_powerSeries [Nontrivial R]
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) (hpq : IsCoprime p q)
    (H : (PowerSeries R)[X]) (hH : H.Monic)
    (hHd : H.natDegree = p.natDegree + q.natDegree)
    (hH₀ : H.map PowerSeries.constantCoeff = p * q) :
    ∃! PQ : (PowerSeries R)[X] × (PowerSeries R)[X],
      PQ.1.Monic ∧ PQ.2.Monic ∧ PQ.1.natDegree = p.natDegree ∧ PQ.2.natDegree = q.natDegree ∧
      PQ.1.map PowerSeries.constantCoeff = p ∧ PQ.2.map PowerSeries.constantCoeff = q ∧
      PQ.1 * PQ.2 = H := by
  let e : ℕ → degreeLT R (p.natDegree + q.natDegree) := fun n =>
    ⟨PowerSeries.coeff (n + 1) (polynomialSeriesEmbedding H), mem_degreeLT.mpr
      (by simpa only [hHd] using degree_coeff_embedding_succ_lt H hH n)⟩
  have hconst : PowerSeries.constantCoeff (polynomialSeriesEmbedding H) = p * q := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← map_constantCoeff_eq_coeff_zero_embedding, hH₀]
  have hinput : factorInputPolynomial p q e = H := by
    apply polynomialSeriesEmbedding_injective
    rw [polynomialSeriesEmbedding_factorInputPolynomial]
    simpa only [factorErrorSeries, e, hconst, add_comm] using
      (PowerSeries.eq_X_mul_shift_add_const (polynomialSeriesEmbedding H)).symm
  simpa only [hinput] using existsUnique_monic_powerSeries_polynomial_factors p q hp hq hpq e

end

end Surreal.FinitePolynomial
