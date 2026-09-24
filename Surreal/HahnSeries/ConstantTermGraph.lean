import Surreal.Algebra.ConstantTermGraph
import Surreal.HahnSeries.DiophantineConstants
import Surreal.HahnSeries.QuadraticIdealDefinition

/-!
# The constant-term graph on full Hahn coefficient pullbacks

The full Hahn-ring conclusion of `odg:def:thm:ctgraph` and
`odg:def:eq:ctgraph`. Integer and Gaussian coefficients use the identical
six-witness formula. No restrictions on rank or divisibility of the
ordered abelian exponent group are needed.
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CommRing O]

/-- Constant extraction with values in the prescribed ordinary coefficient ring. -/
abbrev coefficientRestrictedRetraction (i : O →+* K) (hi : Function.Injective i) :
    coefficientRestrictedSubring (Γ := Γ) i →+* O :=
  CoefficientPullback.retraction (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi

/-- The full pullback has precisely the prescribed intersection with the coefficient field. -/
theorem coefficientRestricted_constants_intersection (i : O →+* K) (a : K) :
    nonpositiveConstants (Γ := Γ) a ∈ coefficientRestrictedSubring i ↔ a ∈ i.range := by
  change nonpositiveConstantCoeff (nonpositiveConstants a) ∈ i.range ↔ _
  rw [nonpositiveConstantCoeff_constants]

/-- Ordinary root exclusion, ordinary Xi witnesses, and the quadratic ideal test give the graph. -/
theorem coefficientRestricted_constantTermGraph_iff [CharZero K]
    (i : O →+* K) (hi : Function.Injective i)
    (hno : ∀ b : O, IntersectivePolynomial.value b ≠ 0)
    (hord : ∀ b : O, DiophantineConstants.Xi b)
    (hkernel : ∀ a : coefficientRestrictedSubring (Γ := Γ) i,
      a.val ∈ purelyInfiniteIdeal ↔
        ∃ y : coefficientRestrictedSubring (Γ := Γ) i, a ^ 2 = 2 * y ^ 2)
    (x n : coefficientRestrictedSubring (Γ := Γ) i) :
    ConstantTermGraph.Graph x n ↔
      n = coefficientRestrictedConstants (Γ := Γ) i (coefficientRestrictedRetraction (Γ := Γ) i hi x) := by
  apply ConstantTermGraph.graph_iff (coefficientRestrictedRetraction (Γ := Γ) i hi)
    (coefficientRestrictedConstants i)
  · exact CoefficientPullback.retraction_sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi
      nonpositiveConstants nonpositiveConstantCoeff_constants
  · intro a
    have h := intermediate_xi_iff i hi hno hord (coefficientRestrictedSubring i)
      (coefficientRestricted_constants_intersection i) a
    rw [h]
    exact exists_congr (fun b => ⟨fun hb => Subtype.ext hb, fun hb => congrArg Subtype.val hb⟩)
  · intro a
    exact (hkernel a).symm.trans
      (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K)) i hi a).symm

/-- Integer coefficient pullbacks over any characteristic-zero field containing sqrt(2). -/
theorem integerRestricted_constantTermGraph_iff [CharZero K] (r : K) (hr : r ^ 2 = 2)
    (x n : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)) :
    ConstantTermGraph.Graph x n ↔ n = coefficientRestrictedConstants (Γ := Γ) (Int.castRingHom K)
      (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom K) Int.cast_injective x) :=
  coefficientRestricted_constantTermGraph_iff (Int.castRingHom K) Int.cast_injective
    IntersectivePolynomial.integer_value_ne_zero DiophantineConstants.integer_xi
    (integerRestricted_purelyInfinite_iff_quadratic r hr) x n

/-- Gaussian coefficient pullbacks over any characteristic-zero field containing sqrt(2). -/
theorem gaussianRestricted_constantTermGraph_iff [CharZero K]
    (i : GaussianInt →+* K) (hi : Function.Injective i) (r : K) (hr : r ^ 2 = 2)
    (x n : coefficientRestrictedSubring (Γ := Γ) i) :
    ConstantTermGraph.Graph x n ↔
      n = coefficientRestrictedConstants (Γ := Γ) i (coefficientRestrictedRetraction (Γ := Γ) i hi x) :=
  coefficientRestricted_constantTermGraph_iff i hi IntersectivePolynomial.gaussian_value_ne_zero
    DiophantineConstants.gaussian_xi (gaussianRestricted_purelyInfinite_iff_quadratic i hi r hr) x n

/-- The source's real coefficient-field instance of the graph equivalence. -/
theorem realRestricted_constantTermGraph_iff
    (x n : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)) :
    ConstantTermGraph.Graph x n ↔ n = coefficientRestrictedConstants (Γ := Γ) (Int.castRingHom ℝ)
      (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom ℝ) Int.cast_injective x) :=
  integerRestricted_constantTermGraph_iff (Real.sqrt 2) (by norm_num [Real.sq_sqrt]) x n

/-- The source's complex coefficient-field instance of the Gaussian graph equivalence. -/
theorem complexRestricted_constantTermGraph_iff
    (x n : coefficientRestrictedSubring (Γ := Γ) GaussianInt.toComplex) :
    ConstantTermGraph.Graph x n ↔ n = coefficientRestrictedConstants (Γ := Γ) GaussianInt.toComplex
      (coefficientRestrictedRetraction (Γ := Γ) GaussianInt.toComplex GaussianInt.toComplex_injective x) := by
  apply gaussianRestricted_constantTermGraph_iff GaussianInt.toComplex GaussianInt.toComplex_injective
    (Real.sqrt 2 : ℂ)
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- Every real Hahn input has exactly one ring-valued constant output. -/
theorem realRestricted_constantTermGraph_existsUnique
    (x : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)) :
    ∃! n, ConstantTermGraph.Graph x n :=
  ⟨_, (realRestricted_constantTermGraph_iff x _).mpr rfl,
    fun n hn => (realRestricted_constantTermGraph_iff x n).mp hn⟩

/-- Every Gaussian Hahn input has exactly one ring-valued constant output. -/
theorem complexRestricted_constantTermGraph_existsUnique
    (x : coefficientRestrictedSubring (Γ := Γ) GaussianInt.toComplex) :
    ∃! n, ConstantTermGraph.Graph x n :=
  ⟨_, (complexRestricted_constantTermGraph_iff x _).mpr rfl,
    fun n hn => (complexRestricted_constantTermGraph_iff x n).mp hn⟩

end
end Surreal.HahnSeries
