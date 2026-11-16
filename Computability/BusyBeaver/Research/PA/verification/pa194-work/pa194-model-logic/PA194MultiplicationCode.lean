import PA194MultiplicationTemplateRew
import PA194SourceTernaryTemplate
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SourceTemplates
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource
open M6.PA.RelationalSource
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def multiplicationTemplate : Semiproposition SourceL 3 := PairGraph.mulResult (.bvar 0) (.bvar 1) (.bvar 2)
noncomputable def multiplicationCode (x y z : V) : V := templateThree multiplicationTemplate x y z
noncomputable abbrev multiplicationCodeGraph : 𝚺₁.Semisentence 4 := templateThreeGraph multiplicationTemplate
theorem multiplicationCode_graph (out x y z : V) :
    multiplicationCodeGraph.val.Evalb ![out,x,y,z] ↔ out = multiplicationCode x y z := templateThree_graph _ _ _ _ _
instance multiplicationCode_defined : 𝚺₁-Function₃ (multiplicationCode : V → V → V → V) via multiplicationCodeGraph :=
  templateThree_defined multiplicationTemplate
theorem multiplicationCode_quote {m : Nat} (x y z : Semiterm SourceL Nat m) :
    multiplicationCode (⌜x⌝ : V) ⌜y⌝ ⌜z⌝ = ⌜PairGraph.mulResult x y z⌝ := by
  rw [multiplicationCode,templateThree_quote]
  congr 1
  exact PairGraph.mulResult_rew _ _ _ _
theorem multiplicationCode_valid {n x y z : V}
    (hx : IsSemiterm SourceL n x) (hy : IsSemiterm SourceL n y) (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (multiplicationCode x y z) := templateThree_valid _ hx hy hz
#print axioms multiplicationCode_graph
#print axioms multiplicationCode_defined
#print axioms multiplicationCode_quote
#print axioms multiplicationCode_valid
end generic
end PA194SourceTemplates
