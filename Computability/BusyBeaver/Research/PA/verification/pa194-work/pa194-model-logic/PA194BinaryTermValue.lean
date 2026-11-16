import PA194AdditionCode
import PA194MultiplicationCode
import PA194PAeqParameterCompose
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqOrdinalValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def binaryValue (p : Semiproposition SourceL 3) (z left right : V) : V :=
  domainCode z ^⋏ (^∃ (^∃ (left ^⋏ (right ^⋏
    templateThree p (^#(1 : V)) (^#(0 : V)) (termBShift SourceL (termBShift SourceL z))))))
noncomputable def binaryValueGraph (p : Semiproposition SourceL 3) : 𝚺₁.Semisentence 4 := .mkSigma
  “out z left right. ∃ d z1 z2 b1 b0 tail inner1 inner2 ex2 ex1,
    !(templateOneGraph domainTemplate) d z ∧ !(termBShiftGraph SourceL) z1 z ∧ !(termBShiftGraph SourceL) z2 z1 ∧
    !qqBvarDef b1 1 ∧ !qqBvarDef b0 0 ∧ !(templateThreeGraph p) tail b1 b0 z2 ∧
    !qqAndDef inner1 right tail ∧ !qqAndDef inner2 left inner1 ∧
    !qqExsDef ex2 inner2 ∧ !qqExsDef ex1 ex2 ∧ !qqAndDef out d ex1”
theorem binaryValue_graph (p : Semiproposition SourceL 3) (out z left right : V) :
    (binaryValueGraph p).val.Evalb ![out,z,left,right] ↔ out = binaryValue p z left right := by
  simp [binaryValueGraph,binaryValue,domainCode,templateThree_graph,Matrix.comp_vecCons'']
instance binaryValue_defined (p : Semiproposition SourceL 3) :
    𝚺₁-Function₃ (binaryValue p : V → V → V → V) via binaryValueGraph p := .mk fun v => by
  change (binaryValueGraph p).val.Evalb v ↔ v 0 = binaryValue p (v 1) (v 2) (v 3)
  have hv : ![v 0,v 1,v 2,v 3] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using binaryValue_graph p (v 0) (v 1) (v 2) (v 3)
theorem binaryValue_valid (p : Semiproposition SourceL 3) {n z left right : V}
    (hz : IsSemiterm SourceL n z) (hl : IsSemiformula SourceL ((n+1)+1) left)
    (hr : IsSemiformula SourceL ((n+1)+1) right) : IsSemiformula SourceL n (binaryValue p z left right) := by
  apply IsSemiformula.and.mpr
  refine ⟨domainCode_valid hz, IsSemiformula.exs.mpr (IsSemiformula.exs.mpr
    (IsSemiformula.and.mpr ⟨hl, IsSemiformula.and.mpr ⟨hr, ?_⟩⟩))⟩
  exact templateThree_valid p (by simp) (by simp) (by simpa using hz.bShift.bShift)
#print axioms binaryValue_graph
#print axioms binaryValue_valid
end generic
end PA194PAeqOrdinalValues
