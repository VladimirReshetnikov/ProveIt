import PA194AdditionTemplateRew
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
def additionTemplate : Semiproposition SourceL 3 := PairGraph.addResult (.bvar 0) (.bvar 1) (.bvar 2)
noncomputable def additionCode (x y z : V) : V := templateThree additionTemplate x y z
noncomputable abbrev additionCodeGraph : 𝚺₁.Semisentence 4 := templateThreeGraph additionTemplate
theorem additionCode_graph (out x y z : V) :
    additionCodeGraph.val.Evalb ![out,x,y,z] ↔ out = additionCode x y z := templateThree_graph _ _ _ _ _
instance additionCode_defined : 𝚺₁-Function₃ (additionCode : V → V → V → V) via additionCodeGraph :=
  templateThree_defined additionTemplate
theorem additionCode_quote {m : Nat} (x y z : Semiterm SourceL Nat m) :
    additionCode (⌜x⌝ : V) ⌜y⌝ ⌜z⌝ = ⌜PairGraph.addResult x y z⌝ := by
  rw [additionCode,templateThree_quote]
  congr 1
  exact PairGraph.addResult_rew _ _ _ _
theorem additionCode_valid {n x y z : V}
    (hx : IsSemiterm SourceL n x) (hy : IsSemiterm SourceL n y) (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (additionCode x y z) := templateThree_valid _ hx hy hz
#print axioms additionCode_graph
#print axioms additionCode_defined
#print axioms additionCode_quote
#print axioms additionCode_valid
end generic
end PA194SourceTemplates
