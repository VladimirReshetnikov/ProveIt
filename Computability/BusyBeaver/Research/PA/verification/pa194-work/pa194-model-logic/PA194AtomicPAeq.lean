import PA194TermScope
import PA194FoundationOrderIso
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


namespace PA194TermDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues
open M6.PA.RelationalSource
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def orderIsoTemplate : Semiproposition SourceL 2 := PairGraph.orderIso (.bvar 0) (.bvar 1)
noncomputable def orderIsoCode (x y : V) : V := templateTwo orderIsoTemplate x y
noncomputable def atomicEquality (param s t : V) : V :=
  ^∃ (^∃ (translate (binaryParameters param 1) s ^⋏
    (translate (binaryParameters param 0) t ^⋏ orderIsoCode (^#(1 : V)) (^#(0 : V)))))
noncomputable def atomicEqualityGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out param s t. ∃ p1 p0 left right b1 b0 eq inner1 inner2 ex1,
    !binaryParametersGraph p1 param 1 ∧ !binaryParametersGraph p0 param 0 ∧
    !translateGraph left p1 s ∧ !translateGraph right p0 t ∧
    !qqBvarDef b1 1 ∧ !qqBvarDef b0 0 ∧ !(templateTwoGraph orderIsoTemplate) eq b1 b0 ∧
    !qqAndDef inner1 right eq ∧ !qqAndDef inner2 left inner1 ∧
    !qqExsDef ex1 inner2 ∧ !qqExsDef out ex1”
theorem atomicEquality_graph (out param s t : V) :
    atomicEqualityGraph.val.Evalb ![out,param,s,t] ↔ out = atomicEquality param s t := by
  simp [atomicEqualityGraph,atomicEquality,orderIsoCode,binaryParameters_graph,translate_graph,Matrix.comp_vecCons'']
instance atomicEquality_defined : 𝚺₁-Function₃ (atomicEquality : V → V → V → V) via atomicEqualityGraph := .mk fun v => by
  change atomicEqualityGraph.val.Evalb v ↔ v 0 = atomicEquality (v 1) (v 2) (v 3)
  have hv : ![v 0,v 1,v 2,v 3] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using atomicEquality_graph (v 0) (v 1) (v 2) (v 3)

theorem atomicEquality_valid {s n param a b : V} (hparam : ParametersValid s n param)
    (ha : IsSemiterm PA194PAeq.language s a) (hb : IsSemiterm PA194PAeq.language s b)
    (hla : a < len (nth param 1)) (hlb : b < len (nth param 1)) :
    IsSemiformula SourceL n (atomicEquality param a b) := by
  have hp1 : ParametersValid s ((n+1)+1) (binaryParameters param 1) := binaryParameters_valid hparam (by simp)
  have hp0 : ParametersValid s ((n+1)+1) (binaryParameters param 0) := binaryParameters_valid hparam (by simp)
  have hf1 := shiftTerms_valid hparam.2.1
  have hla' : a < len (nth (binaryParameters param 1) 1) := by
    simpa [binaryParameters,shiftTerms_length hparam.2.1,shiftTerms_length hf1] using hla
  have hlb' : b < len (nth (binaryParameters param 0) 1) := by
    simpa [binaryParameters,shiftTerms_length hparam.2.1,shiftTerms_length hf1] using hlb
  have hleft := scope_translate ha.isUTerm s ((n+1)+1) (binaryParameters param 1) ha hp1 hla'
  have hright := scope_translate hb.isUTerm s ((n+1)+1) (binaryParameters param 0) hb hp0 hlb'
  apply IsSemiformula.exs.mpr
  apply IsSemiformula.exs.mpr
  apply IsSemiformula.and.mpr
  refine ⟨hleft,IsSemiformula.and.mpr ⟨hright,?_⟩⟩
  apply templateTwo_valid orderIsoTemplate <;> simp
#print axioms atomicEquality_graph
#print axioms atomicEquality_valid
end generic
end PA194TermDispatcher
