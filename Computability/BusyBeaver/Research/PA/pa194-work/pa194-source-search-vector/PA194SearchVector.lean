import PA194SearchModel
import DiophantineConsistency.PRABoundedSearchUniversal
import DiophantineConsistency.PRABoundedSearchBound
/-! Exact all-model Foundation vector lookup for source search.

The coded compiler's sequent representation and validity remain separate
obligations. The induction below is internal IΣ₁ induction. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace PA194SearchVector
open PA194SearchModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRASubReconstruct PRAEqualityCode PRAIsZero PRANonzeroCharacter PRABooleanOps PRAOpenFormulaCompiler
 PRABoundedSearchCode PRABoundedSearchInvariant PRABoundedSearchUniversal PRABoundedSearchBound
 PA194BranchSeed PA194StackCode PA194StackHistory PA194TermShiftCodeModel PA194SourceShiftHistory PA194TermRecursion

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

 theorem component_first (v : M) : F (stackComponent firstProjection) (fun _ => v) = fstIdx v := by
  rcases zero_or_succ v with (rfl | ⟨v,rfl⟩)
  · rw [stackComponent, modelComposition]
    have hv : (fun i : Fin 1 => F (getCode (.cons predCode (.nil 1)) i) (fun _ => 0)) = (fun _ => F predCode (fun _ => 0)) := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]
    change F firstProjection (fun _ => F predCode (fun _ => F (Code.zero 0) Fin.elim0)) = _
    rw [modelPredZero, modelPi1Code firstProjection firstProjection_certified]
    change π₁ (0 : M) = fstIdx 0
    simp [fstIdx]
  · change F (stackComponent firstProjection) (fun _ => v+1) = fstIdx (v+1)
    rw [stackComponent, modelComposition]
    have hv : (fun i : Fin 1 => F (getCode (.cons predCode (.nil 1)) i) (fun _ => v+1)) = (fun _ => F predCode (fun _ => v+1)) := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]
    rw [modelPredAddOne, modelPi1Code firstProjection firstProjection_certified]
    simp [fstIdx]

 theorem component_second (v : M) : F (stackComponent secondProjection) (fun _ => v) = sndIdx v := by
  rcases zero_or_succ v with (rfl | ⟨v,rfl⟩)
  · rw [stackComponent, modelComposition]
    have hv : (fun i : Fin 1 => F (getCode (.cons predCode (.nil 1)) i) (fun _ => 0)) = (fun _ => F predCode (fun _ => 0)) := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]
    change F secondProjection (fun _ => F predCode (fun _ => F (Code.zero 0) Fin.elim0)) = _
    rw [modelPredZero, modelPi2Code secondProjection secondProjection_certified]
    change π₂ (0 : M) = sndIdx 0
    simp [sndIdx]
  · change F (stackComponent secondProjection) (fun _ => v+1) = sndIdx (v+1)
    rw [stackComponent, modelComposition]
    have hv : (fun i : Fin 1 => F (getCode (.cons predCode (.nil 1)) i) (fun _ => v+1)) = (fun _ => F predCode (fun _ => v+1)) := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]
    rw [modelPredAddOne, modelPi2Code secondProjection secondProjection_certified]
    simp [sndIdx]

 theorem lookup_zero (v : M) : F lookup ![0,v] = v.[0] := by
   rw [lookup, modelLookupValue, modelDropBase]
   rw [component_first, nth_zero]

 theorem lookup_succ (i v : M) : F lookup ![i+1,v] = F lookup ![i,sndIdx v] := by
   rw [lookup, modelLookupValue, modelDropShift, ← modelLookupValue]
   rw [component_second]

 theorem lookup_predicate_def (G H : M → M → M) (v : M)
     (hG : 𝚺₁-Function₂ G) (hH : 𝚺₁-Function₂ H) :
     𝚺₁-Predicate (fun i => ∀ w ≤ v, G i w = H w i) := by
   haveI := hG
   haveI := hH
   definability

 theorem lookup_nth (i v : M) : F lookup ![i,v] = v.[i] := by
   haveI : 𝚺₁-Function₂ (fun i v : M => F lookup ![i,v]) := by
     have h : 𝚺₁.DefinableFunction (fun x : Fin 2 → M => F lookup x) :=
       HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) lookup)
     convert h using 1
     funext x
     exact congrArg (fun e : Fin 2 → M => F lookup e) (Matrix.fun_eq_vec_two x).symm
   have hdef := lookup_predicate_def (fun i v : M => F lookup ![i,v]) nth v inferInstance inferInstance
   suffices ∀ w ≤ v, F lookup ![i,w] = w.[i] from this v (by simp)
   induction i using ISigma1.sigma1_succ_induction
   · exact hdef
   case zero => intro w _; exact lookup_zero w
   case succ k ih =>
     intro w hw
     rw [lookup_succ, nth_succ]
     exact ih (sndIdx w) (le_trans (by simp) hw)



theorem find_vector (bound v target j : M)
    (hj : j < bound)
    (hvalid : ∀ i, i < bound → IsUFormula M6.PA.RelationalSource.language v.[i])
    (hmatch : shift M6.PA.RelationalSource.language v.[j] = target) :
    let found := F search ![bound,v,target]
    found < bound ∧ shift M6.PA.RelationalSource.language v.[found] = target := by
  have hv : ∀ i, i < bound → IsUFormula M6.PA.RelationalSource.language (F lookup ![i,v]) := by
    intro i hi
    rw [lookup_nth]
    exact hvalid i hi
  have hm : shift M6.PA.RelationalSource.language (F lookup ![j,v]) = target := by
    rw [lookup_nth]
    exact hmatch
  have h := find_match bound v target j hj hv hm
  change F search ![bound,v,target] < bound ∧
    shift M6.PA.RelationalSource.language (F lookup ![F search ![bound,v,target],v]) = target at h
  rw [lookup_nth] at h
  exact h

#print axioms lookup_nth
#print axioms find_vector
end models
end PA194SearchVector
