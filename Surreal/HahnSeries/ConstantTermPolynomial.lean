import Surreal.Algebra.ConstantTermPolynomial
import Surreal.HahnSeries.QuinticConstants
import Surreal.HahnSeries.ConstantTermGraph

/-!
# The degree-ten graph on full ordered Hahn coefficient pullbacks

The single real polynomial following `odg:def:thm:ctgraph`, over every
ordered abelian exponent group. An ordered coefficient field containing
a square root of two suffices.
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The eight-witness polynomial defines the graph in any ordered coefficient field with sqrt(2). -/
theorem integerRestricted_constantTermPolynomial_iff (r : K) (hr : r ^ 2 = 2)
    (x n : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)) :
    ConstantTermPolynomial.Graph x n ↔ n = coefficientRestrictedConstants (Γ := Γ) (Int.castRingHom K)
      (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom K) Int.cast_injective x) := by
  let A := coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)
  rw [ConstantTermPolynomial.graph_iff (intermediateLexInclusion A)
    (intermediateLexInclusion_injective A)]
  apply ConstantTermGraph.standard_graph_iff (coefficientRestrictedRetraction (Γ := Γ)
    (Int.castRingHom K) Int.cast_injective) (coefficientRestrictedConstants (Int.castRingHom K))
  · exact CoefficientPullback.retraction_sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := K))
      (Int.castRingHom K) Int.cast_injective nonpositiveConstants nonpositiveConstantCoeff_constants
  · intro a
    rw [integer_intermediate_quintic_iff A
      (coefficientRestricted_constants_intersection (Int.castRingHom K))]
    exact exists_congr (fun b => ⟨fun hb => Subtype.ext hb, fun hb => congrArg Subtype.val hb⟩)
  · intro a
    exact (integerRestricted_purelyInfinite_iff_quadratic r hr a).symm.trans
      (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K))
        (Int.castRingHom K) Int.cast_injective a).symm

/-- The source's full real Hahn-ring instance, without rank or divisibility restrictions. -/
theorem realRestricted_constantTermPolynomial_iff
    (x n : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)) :
    ConstantTermPolynomial.Graph x n ↔ n = coefficientRestrictedConstants (Γ := Γ) (Int.castRingHom ℝ)
      (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom ℝ) Int.cast_injective x) :=
  integerRestricted_constantTermPolynomial_iff (Real.sqrt 2) (by norm_num [Real.sq_sqrt]) x n

/-- The polynomial graph has exactly one output in every real Hahn pullback. -/
theorem realRestricted_constantTermPolynomial_existsUnique
    (x : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)) :
    ∃! n, ConstantTermPolynomial.Graph x n :=
  ⟨_, (realRestricted_constantTermPolynomial_iff x _).mpr rfl,
    fun n hn => (realRestricted_constantTermPolynomial_iff x n).mp hn⟩

end
end Surreal.HahnSeries
