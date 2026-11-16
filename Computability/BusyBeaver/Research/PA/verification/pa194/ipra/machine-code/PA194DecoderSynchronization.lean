import PA194DecoderInvariant3
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194DecoderSynchronization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubtraction
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194ClockInvariantDefinable PA194DecoderInvariant3 PA194DecoderRoundCode PA194DiagonalIteration
open PA194UnpairRound PA194UnpairDrainComplete PA194DiagonalLink
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

noncomputable def argsAt (initial : Fin 11 → M) (x y left : M) : Fin 11 → M :=
  Function.update (Function.update (Function.update initial 6 x) 7 y) 8 left

theorem stateShape (initial : Fin 11 → M) (tail x y left : M) :
    sourceState 34 (argsAt initial x y left) tail = pair (modelNumeral M 34)
      (pair (initial 0) (pair (initial 1) (pair (initial 2) (pair (initial 3) (pair (initial 4)
        (pair (initial 5) (pair x (pair y (pair left tail))))))))) := by
  simp [sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,argsAt]

theorem countPositive (x n total : M) (heq : x+n=total) (hbound : n+1 ≤ total) : ∃ w, x=w+1 := by
  have hlt : n < x+n := by rw [heq]; exact lt_of_lt_of_le (lt_add_one n) hbound
  have hx : 0 < x := by
    have h : (0 : M)+n < x+n := by simpa only [zero_add] using hlt
    exact (add_lt_add_iff_right n).mp h
  have h1 : (1 : M) ≤ x := by simpa using (lt_iff_succ_le.mp hx)
  obtain ⟨w,hw⟩ := le_iff_exists_add.mp h1
  exact ⟨w,by simpa [add_comm] using hw⟩

theorem synchronization (initial : Fin 11 → M) (tail steps : M)
    (hsteps : steps ≤ initial 8) :
    ∃ x y left : M,
      F (iterate advance) ![steps,sourceState 34 initial tail] = sourceState 34 (argsAt initial x y left) tail ∧
      left+steps = initial 8 ∧
      pair x y = F PA194DiagonalCode.run ![steps,pair (initial 6) (initial 7)] := by
  let start := sourceState 34 initial tail
  let seed := pair (initial 6) (initial 7)
  let f : M → M := fun j => F (iterate advance) ![j,start]
  let g : M → M := fun j => F PA194DiagonalCode.run ![j,seed]
  have hf : 𝚺₁-Function₁ f := bindBinary _ start (binaryCodeDef (M := M) (iterate advance))
  have hg : 𝚺₁-Function₁ g := bindBinary _ seed (binaryCodeDef (M := M) PA194DiagonalCode.run)
  have hp := bodyDef f g initial tail (initial 8) hf hg
  have main : ∀ j : M, body f g initial tail (initial 8) j := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => exact hp
    | zero =>
      right
      refine ⟨initial 6,initial 7,initial 8,?_,?_,?_⟩
      · dsimp only [f,start]
        rw [PA194DiagonalIteration.iterZero]
        simp [sourceState,PA194SourceRegisterRelation.pack,regsOfArgs]
      · simp
      · dsimp only [g,seed,PA194DiagonalCode.run]
        rw [PA194DiagonalIteration.iterZero]
    | succ u ih =>
      classical
      by_cases hbig : initial 8 < u+1
      · exact Or.inl hbig
      · right
        have hle : u+1 ≤ initial 8 := not_lt.mp hbig
        have hnot : ¬ initial 8 < u := not_lt_of_ge (le_of_lt (lt_of_lt_of_le (lt_add_one u) hle))
        obtain ⟨x,y,left,hstate,hcount,hpair⟩ := ih.resolve_left hnot
        obtain ⟨w,hw⟩ := countPositive left u (initial 8) hcount hle
        let current := argsAt initial x y left
        have hs : f u = sourceState 34 current tail := by
          change f u = sourceState 34 (argsAt initial x y left) tail
          rw [stateShape]; exact hstate
        have hc8 : current 8 = w+1 := by simp [current,argsAt,hw]
        by_cases hx : x = (0 : M)
        · let a1 := Function.update current 8 w
          let a2 := Function.update a1 7 (a1 7+1)
          let out := PA194UnpairDrainInvariant.argsAt a2 (a2 7)
          have hc6 : current 6 = (0 : M) := by simp [current,argsAt,hx]
          have hr := advanceZero current tail w hc8 hc6
          change F advance ![sourceState 34 current tail] = sourceState 34 out tail at hr
          have hmatch := zeroRoundMatches current tail w hc8 hc6
          change F PA194DiagonalCode.next ![pair (current 6) (current 7)] = pair (out 6) (out 7) at hmatch
          refine ⟨out 6,out 7,out 8,?_,?_,?_⟩
          · change f (u+1) = _
            dsimp only [f]
            rw [PA194DiagonalIteration.iterSucc]
            change F advance ![f u] = _
            rw [hs,hr]
            simp [sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,out,a2,a1,current,argsAt,PA194UnpairDrainInvariant.argsAt]
          · simp [out,a2,a1,current,argsAt,PA194UnpairDrainInvariant.argsAt,←hw,add_assoc,add_comm,add_left_comm,hcount]
            simpa [add_comm] using hcount
          · change pair (out 6) (out 7) = g (u+1)
            dsimp only [g,PA194DiagonalCode.run]
            rw [PA194DiagonalIteration.iterSucc]
            change pair (out 6) (out 7) = F PA194DiagonalCode.next ![g u]
            rw [←hpair]
            simpa [current,argsAt] using hmatch.symm
        · have hxpos : (0 : M) < x := lt_of_le_of_ne (zero_le : (0 : M) ≤ x) (Ne.symm hx)
          have hx1 : (1 : M) ≤ x := by simpa using (lt_iff_succ_le.mp hxpos)
          obtain ⟨a,ha⟩ := le_iff_exists_add.mp hx1
          have hxa : x = a+1 := by simpa [add_comm] using ha
          let a1 := Function.update current 8 w
          let a2 := Function.update a1 7 (a1 7+1)
          let out := Function.update a2 6 a
          have hc6 : current 6 = a+1 := by simp [current,argsAt,hxa]
          have hr := advancePositive current tail w a hc8 hc6
          change F advance ![sourceState 34 current tail] = sourceState 34 out tail at hr
          have hmatch := positiveRoundMatches current tail w a hc8 hc6
          change F PA194DiagonalCode.next ![pair (current 6) (current 7)] = pair (out 6) (out 7) at hmatch
          refine ⟨out 6,out 7,out 8,?_,?_,?_⟩
          · change f (u+1) = _
            dsimp only [f]
            rw [PA194DiagonalIteration.iterSucc]
            change F advance ![f u] = _
            rw [hs,hr]
            simp [sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,out,a2,a1,current,argsAt]
          · simp [out,a2,a1,current,argsAt,←hw,add_assoc,add_comm,add_left_comm,hcount]
            simpa [add_comm] using hcount
          · change pair (out 6) (out 7) = g (u+1)
            dsimp only [g,PA194DiagonalCode.run]
            rw [PA194DiagonalIteration.iterSucc]
            change pair (out 6) (out 7) = F PA194DiagonalCode.next ![g u]
            rw [←hpair]
            simpa [current,argsAt] using hmatch.symm
  have h := (main steps).resolve_left (not_lt_of_ge hsteps)
  obtain ⟨x,y,left,hstate,hcount,hpair⟩ := h
  refine ⟨x,y,left,?_,hcount,hpair⟩
  change f steps = sourceState 34 (argsAt initial x y left) tail
  rw [stateShape]
  exact hstate
#print axioms synchronization
end models
end PA194DecoderSynchronization
