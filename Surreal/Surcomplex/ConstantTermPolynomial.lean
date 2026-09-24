import Surreal.Algebra.ConstantTermPolynomial
import Surreal.Foundations.OmnificQuintic
import Surreal.Surcomplex.ConstantTermGraph

/-!
# The degree-ten constant-term graph on actual omnific integers

The eight-witness single real polynomial following `odg:def:thm:ctgraph`.
Its output is the embedded ordinary integer constant coefficient.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The literal degree-ten equation defines precisely the actual constant-term graph. -/
theorem omnific_constantTermPolynomial_iff (x n : OmnificInteger.{u}) :
    ConstantTermPolynomial.Graph x n ↔ n = omnificIntCast (omnificConstantCoeff x) := by
  rw [ConstantTermPolynomial.graph_iff omnificToSurreal omnificToSurreal_injective]
  exact omnific_standard_graph_iff QuinticConstants.Defines omnific_quintic_iff x n

/-- Each actual input has a unique output satisfying the eight-witness polynomial formula. -/
theorem omnific_constantTermPolynomial_existsUnique (x : OmnificInteger.{u}) :
    ∃! n, ConstantTermPolynomial.Graph x n :=
  ⟨_, (omnific_constantTermPolynomial_iff x _).mpr rfl,
    fun n hn => (omnific_constantTermPolynomial_iff x n).mp hn⟩

end
end Surreal.Foundations.SignSequence
