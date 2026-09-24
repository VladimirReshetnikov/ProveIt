import Surreal.Algebra.ConstantTermQuartic
import Surreal.HahnSeries.QuarticConstants
import Surreal.HahnSeries.ConstantTermGraph

/-!
# The two quartic graphs on full ordered Hahn pullbacks

The seven-witness assertions of `odg:def:cor:ctquartic` over arbitrary
ordered abelian exponent groups and ordered fields containing sqrt(2).
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Either quartic defines the constant-term graph in an ordered Hahn pullback with sqrt(2). -/
theorem integerRestricted_constantTermQuartic_iff (squared : Bool) (r : K) (hr : r ^ 2 = 2)
    (x n : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)) :
    ConstantTermQuartic.Graph squared x n ↔ n = coefficientRestrictedConstants (Γ := Γ)
      (Int.castRingHom K)
      (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom K) Int.cast_injective x) := by
  let A := coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)
  rw [ConstantTermQuartic.graph_iff (intermediateLexInclusion A)
    (intermediateLexInclusion_injective A)]
  let Std : A → Prop := fun n =>
    if squared then QuarticVariant.Defines n else QuarticConstants.Defines n
  change (Std n ∧ _) ↔ _
  apply ConstantTermGraph.standard_graph_iff (coefficientRestrictedRetraction (Γ := Γ)
    (Int.castRingHom K) Int.cast_injective) (coefficientRestrictedConstants (Int.castRingHom K))
  · exact CoefficientPullback.retraction_sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := K))
      (Int.castRingHom K) Int.cast_injective nonpositiveConstants nonpositiveConstantCoeff_constants
  · intro a
    have hs : Std a ↔ ∃ b : ℤ, a.val = nonpositiveConstants (b : K) := by
      cases squared
      · exact integer_intermediate_quartic_iff A
          (coefficientRestricted_constants_intersection (Int.castRingHom K)) a
      · exact integer_intermediate_quarticVariant_iff A
          (coefficientRestricted_constants_intersection (Int.castRingHom K)) a
    rw [hs]
    exact exists_congr (fun b => ⟨fun hb => Subtype.ext hb, fun hb => congrArg Subtype.val hb⟩)
  · intro a
    exact (integerRestricted_purelyInfinite_iff_quadratic r hr a).symm.trans
      (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := K))
        (Int.castRingHom K) Int.cast_injective a).symm

/-- Both printed seven-witness quartics work in the full real Hahn ring. -/
theorem realRestricted_constantTermQuartic_iff (squared : Bool)
    (x n : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)) :
    ConstantTermQuartic.Graph squared x n ↔ n = coefficientRestrictedConstants (Γ := Γ)
      (Int.castRingHom ℝ)
      (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom ℝ) Int.cast_injective x) :=
  integerRestricted_constantTermQuartic_iff squared (Real.sqrt 2) (by norm_num [Real.sq_sqrt]) x n

/-- Every input in a real Hahn pullback has a unique output under either quartic graph. -/
theorem realRestricted_constantTermQuartic_existsUnique (squared : Bool)
    (x : coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom ℝ)) :
    ∃! n, ConstantTermQuartic.Graph squared x n :=
  ⟨_, (realRestricted_constantTermQuartic_iff squared x _).mpr rfl,
    fun n hn => (realRestricted_constantTermQuartic_iff squared x n).mp hn⟩

end
end Surreal.HahnSeries
