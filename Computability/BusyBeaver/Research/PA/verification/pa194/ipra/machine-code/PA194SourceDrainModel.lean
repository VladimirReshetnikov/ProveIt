import PA194SourceDrainInvariant
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceDrainModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisterRelation PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194IteratedSimulation PA194ClockInvariantDefinable PA194ControllerRunAdd PA194SourceDrainInvariant
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem argsAtZero (args : Fin 11 → M) : argsAt args (0 : M) = args := by
  have hs : F subCode ![args 0,(0 : M)] = args 0 := by
    have h := modelSubAdd (M := M) (0 : M) (args 0)
    change F subCode ![(0 : M)+args 0,(0 : M)] = args 0 at h
    simpa only [zero_add] using h
  funext i
  fin_cases i <;> simp [argsAt,hs]

theorem fourSucc (j : M) : four (j+1) = (((four j+1)+1)+1)+1 := by
  dsimp only [four]
  ac_rfl

theorem argsAdvance (args : Fin 11 → M) (j d : M)
    (h0 : F subCode ![args 0,j] = d+1) (h1 : F subCode ![args 0,j+1] = d) :
    let a := argsAt args j
    let a1 := Function.update a 0 d
    let a2 := Function.update a1 8 (a1 8+1)
    let a3 := Function.update a2 6 (a2 6+1)
    a3 = argsAt args (j+1) := by
  dsimp only
  funext i
  fin_cases i <;> simp [argsAt,h0,h1,add_assoc]

theorem runDrain (args : Fin 11 → M) (tail j : M) (hj : j ≤ args 0) :
    F run ![four j,sourceState 27 args tail] = frame args tail j := by
  let start := sourceState 27 args tail
  let f : M → M := fun t => F run ![t,start]
  let g : M → M := frame args tail
  have hf : 𝚺₁-Function₁ f := bindBinary _ start (binaryCodeDef (M := M) run)
  have hg : 𝚺₁-Function₁ g := frameDef args tail
  have hp := invariantDef f g (args 0) hf hg
  have hmain : ∀ j : M, args 0 < j ∨ f (four j) = g j := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => exact hp
    | zero =>
      right
      dsimp only [f,g,four,start]
      simp only [zero_add]
      rw [run,iterateZero,frameCorrect,argsAtZero]
    | succ j ih =>
      classical
      by_cases hbig : args 0 < j+1
      · exact Or.inl hbig
      · right
        have hj1 : j+1 ≤ args 0 := not_lt.mp hbig
        have hjlt : j < args 0 := lt_of_lt_of_le (lt_add_of_pos_right j (Arithmetic.zero_lt_one : (0 : M) < 1)) hj1
        have hjnot : ¬ args 0 < j := not_lt_of_ge (le_of_lt hjlt)
        have hprev := ih.resolve_left hjnot
        obtain ⟨d,hd⟩ := le_iff_exists_add.mp hj1
        have h1 : F subCode ![args 0,j+1] = d := by
          rw [hd]; exact modelSubAdd (j+1) d
        have h0 : F subCode ![args 0,j] = d+1 := by
          rw [hd]
          have he : (j+1)+d = j+(d+1) := by ac_rfl
          rw [he]; exact modelSubAdd j (d+1)
        have hm : argsAt args j 0 = d+1 := by simp [argsAt,h0]
        have hloop := drainLoop (argsAt args j) tail d hm
        have hargs := argsAdvance args j d h0 h1
        change F run ![four (j+1),start] = frame args tail (j+1)
        rw [fourSucc]
        change F (iterate step) ![(((four j+1)+1)+1)+1,start] = _
        rw [iterateSucc,iterateSucc,iterateSucc,iterateSucc]
        change F step ![F step ![F step ![F step ![F run ![four j,start]]]]] = _
        change F run ![four j,start] = frame args tail j at hprev
        rw [hprev,frameCorrect,hloop,hargs,←frameCorrect]
  exact (hmain j).resolve_left (not_lt_of_ge hj)
#print axioms argsAtZero
#print axioms argsAdvance
#print axioms runDrain
end models
end PA194SourceDrainModel
