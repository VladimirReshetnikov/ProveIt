import Surreal.Algebra.ConstantTermGraph
import Surreal.Surcomplex.DiophantineConstants
import Surreal.Surcomplex.QuadraticIdealDefinition

/-!
# The Diophantine constant-term graph on the actual omnific carriers

The actual-carrier conclusions of `odg:def:thm:ctgraph` and
`odg:def:eq:ctgraph`. The output belongs to the same ring as the input;
it is proved to be the embedded ordinary constant coefficient.
-/

universe u
namespace Surreal

noncomputable section

namespace Foundations.SignSequence

/-- Any definition of Z combines with the quadratic ideal formula to define the actual graph. -/
theorem omnific_standard_graph_iff (Std : OmnificInteger.{u} → Prop)
    (hStd : ∀ n, Std n ↔ ∃ b : ℤ, n = omnificIntCast b) (x n : OmnificInteger.{u}) :
    (Std n ∧ ∃ y : OmnificInteger.{u}, (x - n) ^ 2 = 2 * y ^ 2) ↔
      n = omnificIntCast (omnificConstantCoeff x) :=
  ConstantTermGraph.standard_graph_iff omnificConstantCoeff omnificIntCast
    omnificConstantCoeff_intCast Std hStd
    (fun a => (omnific_purelyInfinite_iff_quadratic a).symm) x n

/-- The printed six-witness graph defines the actual omnific constant-term retraction. -/
theorem omnific_constantTermGraph_iff (x n : OmnificInteger.{u}) :
    ConstantTermGraph.Graph x n ↔ n = omnificIntCast (omnificConstantCoeff x) :=
  omnific_standard_graph_iff DiophantineConstants.Xi omnific_xi_iff x n

/-- Each actual omnific input has exactly one output in the graph. -/
theorem omnific_constantTermGraph_existsUnique (x : OmnificInteger.{u}) :
    ∃! n : OmnificInteger.{u}, ConstantTermGraph.Graph x n :=
  ⟨omnificIntCast (omnificConstantCoeff x), (omnific_constantTermGraph_iff x _).mpr rfl,
    fun n hn => (omnific_constantTermGraph_iff x n).mp hn⟩

end Foundations.SignSequence
namespace Surcomplex

/-- The identical six-witness graph defines the actual Gaussian constant-term retraction. -/
theorem gaussianOmnific_constantTermGraph_iff (x n : GaussianOmnificInteger.{u}) :
    ConstantTermGraph.Graph x n ↔
      n = gaussianOmnificConstants (gaussianOmnificConstantCoeff x) :=
  ConstantTermGraph.graph_iff gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u}
    gaussianOmnificConstantCoeff_constants gaussianOmnific_xi_iff
    (fun a => (gaussianOmnific_purelyInfinite_iff_quadratic a).symm) x n

/-- The Gaussian output is unique, although the six witnesses need not be. -/
theorem gaussianOmnific_constantTermGraph_existsUnique (x : GaussianOmnificInteger.{u}) :
    ∃! n : GaussianOmnificInteger.{u}, ConstantTermGraph.Graph x n :=
  ⟨gaussianOmnificConstants (gaussianOmnificConstantCoeff x),
    (gaussianOmnific_constantTermGraph_iff x _).mpr rfl,
    fun n hn => (gaussianOmnific_constantTermGraph_iff x n).mp hn⟩

end Surcomplex
end
end Surreal
