import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree
import OAI.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (I : LieIdeal ℚ L)

theorem realQuotientMultidegree_mem_layer (a : σ → ℕ) {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realification.layer a) :
    realificationLieHom (lieQuotientMap I) x ∈ (F.quotientMultidegree I).realification.layer a := by
  change realificationLieHom (lieQuotientMap I) x ∈
    ((F.layer a).map (lieQuotientMap I).toLinearMap).baseChange ℝ
  rw [realification_map]
  exact ⟨x, hx, rfl⟩

noncomputable def realQuotientMultidegreeMap :
    F.realification.Group →* (F.quotientMultidegree I).realification.Group :=
  realificationMap (hnil := F.ordinary.lowerCentralSeries_eq_bot)
    (hM := (F.quotientMultidegree I).ordinary.lowerCentralSeries_eq_bot) (lieQuotientMap I)

noncomputable def realQuotientMultidegreeOrbit (g : F.realification.PolynomialOrbit) :
    (F.quotientMultidegree I).realification.PolynomialOrbit :=
  (F.quotientMultidegree I).realification.polynomialOrbitOfLog
    (VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
      (PolynomialOrbit.log F.realification g)) (by
        intro a
        rw [coefficients_map]
        exact F.realQuotientMultidegree_mem_layer I (fun i => a i)
          (PolynomialOrbit.adapted F.realification g a))

theorem realQuotientMultidegreeOrbit_eval (g : F.realification.PolynomialOrbit) (x : σ → ℤ) :
    (F.quotientMultidegree I).realification.polynomialOrbitEval x (F.realQuotientMultidegreeOrbit I g) =
      F.realQuotientMultidegreeMap I (F.realification.polynomialOrbitEval x g) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ))
    (VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
      (PolynomialOrbit.log F.realification g)) = _
  rw [eval_map]
  rfl

theorem realQuotientMultidegreeOrbit_zero (g : F.realification.PolynomialOrbit)
    (hg : F.realification.polynomialOrbitEval 0 g = 1) :
    (F.quotientMultidegree I).realification.polynomialOrbitEval 0 (F.realQuotientMultidegreeOrbit I g) = 1 := by
  rw [F.realQuotientMultidegreeOrbit_eval, hg, map_one]

end Erdos3.MultidegreeLieFiltration

end

end OAI
