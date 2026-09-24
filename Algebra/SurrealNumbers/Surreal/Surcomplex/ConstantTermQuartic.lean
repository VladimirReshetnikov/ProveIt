import Surreal.Algebra.ConstantTermQuartic
import Surreal.Foundations.OmnificQuartic
import Surreal.Surcomplex.QuarticVariant
import Surreal.Surcomplex.ConstantTermGraph

/-!
# The two quartic graphs on actual omnific integers

Both seven-witness variants in `odg:def:cor:ctquartic`. The six-witness
version depending on the three-square guard is a separate result.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Either printed seven-witness quartic defines the actual constant-term graph. -/
theorem omnific_constantTermQuartic_iff (squared : Bool) (x n : OmnificInteger.{u}) :
    ConstantTermQuartic.Graph squared x n ↔ n = omnificIntCast (omnificConstantCoeff x) := by
  rw [ConstantTermQuartic.graph_iff omnificToSurreal omnificToSurreal_injective]
  cases squared
  · exact omnific_standard_graph_iff QuarticConstants.Defines omnific_quartic_iff x n
  · exact omnific_standard_graph_iff QuarticVariant.Defines omnific_quarticVariant_iff x n

/-- The seven-witness quartic graph has exactly one output for every actual input. -/
theorem omnific_constantTermQuartic_existsUnique (squared : Bool) (x : OmnificInteger.{u}) :
    ∃! n, ConstantTermQuartic.Graph squared x n :=
  ⟨_, (omnific_constantTermQuartic_iff squared x _).mpr rfl,
    fun n hn => (omnific_constantTermQuartic_iff squared x n).mp hn⟩

end
end Surreal.Foundations.SignSequence
