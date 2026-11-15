import PA194CloseHistory
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance repeatLiftZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance repeatLiftOne : One M := ⟨F oneCode Fin.elim0⟩
local instance repeatLiftAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance repeatLiftMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance repeatLiftLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance repeatLiftIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Lifting along any two matched model-length histories, assuming the push history. -/
theorem closeTrace_leaf (seed limit fs es : M)
    (hf : (closeIterConstruction (M := M)).CSeq ![seed] fs)
    (hl : limit + 1 = lh fs) (hs : IsSemiformula SourceL 0 seed)
    (he : ∀ j < limit, znth es (j+1) = simPushFree (znth es j))
    (ht : numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr (znth es limit) seed) 1)) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr (znth es 0) (znth fs limit)) 1) := by
  have hdef : 𝚺₁-Predicate (fun i : M => i ≤ limit → ∀ j ≤ limit, i+j = limit →
      numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr (znth es j) (znth fs i)) 1)) := by
    definability
  have hall : ∀ i : M, i ≤ limit → ∀ j ≤ limit, i+j = limit →
      numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr (znth es j) (znth fs i)) 1) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _ j _ hj
      have : j = limit := by simpa using hj
      subst j
      rw [closeIter_trace_start seed fs hf]
      exact ht
    case succ i ih =>
      intro hi j hj hij
      have hilt : i < limit := lt_iff_succ_le.mpr hi
      have hjlt : j < limit := by
        have hh : j+1 ≤ limit := by
          rw [←hij]
          have hh' : (0 : M) ≤ i := zero_le
          simpa only [add_assoc,add_comm,add_left_comm,zero_add] using add_le_add_right hh' (j+1)
        exact lt_iff_succ_le.mpr hh
      have hj1 : j+1 ≤ limit := lt_iff_succ_le.mp hjlt
      have heq : i+(j+1)=limit := by simpa only [add_assoc,add_comm,add_left_comm] using hij
      have hp := ih (le_of_lt hilt) (j+1) hj1 heq
      rw [he j hjlt] at hp
      rw [closeIter_trace_step seed limit fs i hf hl hilt]
      exact closeOne_leaf (znth es j) (znth fs i) (closeIter_trace_scoped seed limit fs i hf hl hs (le_of_lt hilt)) hp
  simpa using hall limit (le_refl limit) 0 (zero_le) (by simp)

#print axioms closeTrace_leaf
end models
end PA194BindSource
