import Surreal.Algebra.DefinableSplitting
import Surreal.Algebra.ConstantTermPrenex
import Surreal.Surcomplex.ConstantTermGraph
import Surreal.Surcomplex.IntersectiveDetector

/-!
# The definable splitting and quantified graphs of the actual omnific rings

The actual-carrier instances of `odg:def:cor:splitting` and
`odg:def:rem:sigma2`. Both quantified formulas give the same unique
ordinary output as the existential graph.
-/

universe u
namespace Surreal

open ConstantTermGraph

noncomputable section

namespace Foundations.SignSequence

/-- The actual integer constant-term sequence has the stated definable exact splitting. -/
theorem omnific_definableSplitting : DefinableSplitting omnificConstantCoeff.{u} omnificIntCast :=
  definableSplitting_of_graph omnificConstantCoeff omnificIntCast omnificConstantCoeff_intCast
    omnific_constantTermGraph_iff (fun a => (omnific_purelyInfinite_iff_quadratic a).symm)

/-- Both printed quantifier orders define the ordinary constant output on actual omnific integers. -/
theorem omnific_prenexGraph_iff (a c : OmnificInteger.{u}) :
    (UniversalGraph a c ↔ c = omnificIntCast (omnificConstantCoeff a)) ∧
      (ExistsForallGraph a c ↔ c = omnificIntCast (omnificConstantCoeff a)) ∧
      (ForallExistsGraph a c ↔ c = omnificIntCast (omnificConstantCoeff a)) := by
  obtain ⟨h₁, h₂, h₃⟩ := prenex_graph_equivalences omnificConstantCoeff omnific_detector_iff
    omnific_definableSplitting.kernel_formula a c
  have hg := omnific_constantTermGraph_iff a c
  exact ⟨h₁.trans hg, h₂.trans hg, h₃.trans hg⟩

end Foundations.SignSequence
namespace Surcomplex

/-- The actual Gaussian constant-term sequence has the same definable exact splitting. -/
theorem gaussianOmnific_definableSplitting :
    DefinableSplitting gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u} :=
  definableSplitting_of_graph gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u}
    gaussianOmnificConstantCoeff_constants gaussianOmnific_constantTermGraph_iff
    (fun a => (gaussianOmnific_purelyInfinite_iff_quadratic a).symm)

/-- Both quantifier orders also give exactly the actual Gaussian constant output. -/
theorem gaussianOmnific_prenexGraph_iff (a c : GaussianOmnificInteger.{u}) :
    (UniversalGraph a c ↔ c = gaussianOmnificConstants (gaussianOmnificConstantCoeff a)) ∧
      (ExistsForallGraph a c ↔ c = gaussianOmnificConstants (gaussianOmnificConstantCoeff a)) ∧
      (ForallExistsGraph a c ↔ c = gaussianOmnificConstants (gaussianOmnificConstantCoeff a)) := by
  obtain ⟨h₁, h₂, h₃⟩ := prenex_graph_equivalences gaussianOmnificConstantCoeff.{u}
    gaussianOmnific_detector_iff gaussianOmnific_definableSplitting.kernel_formula a c
  have hg := gaussianOmnific_constantTermGraph_iff a c
  exact ⟨h₁.trans hg, h₂.trans hg, h₃.trans hg⟩

end Surcomplex
end
end Surreal
