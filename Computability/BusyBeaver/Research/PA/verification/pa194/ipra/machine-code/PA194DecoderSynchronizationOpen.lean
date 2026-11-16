import PA194DecoderRoundOpen
import PA194SourceReconstruct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194DecoderSynchronizationOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition PRASubtraction PRAOpenInduction
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PackedClock PackedRootModel PackedDecoderModel
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194DiagonalIteration PA194DecoderRoundCode PA194DecoderRoundOpen PA194UnpairDrainOpen
abbrev T := Semiterm language Nat 1
def add (a b : T) : T := app2 addCode a b
def pairT (a b : T) : T := app2 pairCode a b
def stateT : T := app1 (constantCode 34) (.bvar 0)
def sourceT (r : Fin 9 → T) (tail : T) : T :=
  pairT stateT (pairT (r 0) (pairT (r 1) (pairT (r 2) (pairT (r 3) (pairT (r 4)
    (pairT (r 5) (pairT (r 6) (pairT (r 7) (pairT (r 8) tail)))))))))
def initialRegs (i : Fin 9) : T := .fvar i.val
def seedT : T := pairT (.fvar 6) (.fvar 7)
noncomputable def diagT : T := app2 PA194DiagonalCode.run (.bvar 0) seedT
noncomputable def runningRegs (i : Fin 9) : T :=
  if i.val = 6 then app1 decodeLeft diagT
  else if i.val = 7 then app1 decodeRight diagT
  else if i.val = 8 then app2 subCode (.fvar 8) (.bvar 0)
  else .fvar i.val
noncomputable def body : Semiformula language Nat 1 := .or
  (.rel Language.ORing.Rel.lt ![(.fvar 8 : T),(.bvar 0 : T)])
  (.rel Language.ORing.Rel.eq ![
    app2 (iterate advance) (.bvar 0) (sourceT initialRegs (.fvar 11)),
    sourceT runningRegs (.fvar 11)])
theorem body_open : body.Open := by simp [body,Semiformula.Open,Semiformula.qr]
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
noncomputable def argsAt (initial : Fin 11 → M) (x y left : M) : Fin 11 → M :=
  Function.update (Function.update (Function.update initial 6 x) 7 y) 8 left

theorem body_eval (x : M) (e : Nat → M) :
    body.Eval ![x] e ↔ e 8 < x ∨
      let initial : Fin 11 → M := fun i => e i.val
      let d := F PA194DiagonalCode.run ![x,pair (initial 6) (initial 7)]
      F (iterate advance) ![x,sourceState 34 initial (e 11)] =
        sourceState 34 (argsAt initial (pi₁ d) (pi₂ d) (F subCode ![initial 8,x])) (e 11) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : T) : (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  have hstate : Semiterm.val ![x] e stateT = modelNumeral M 34 := by
    rw [stateT,PA194DiagonalIteration.valApp1,Semiterm.val_bvar]
    exact modelConstant 34 x
  simp [sourceT,pairT,seedT,diagT,initialRegs,runningRegs,sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,argsAt,
    PA194DiagonalIteration.valApp1,PA194DiagonalIteration.valApp2,hstate,Semiterm.val_bvar,Semiterm.val_fvar,
    Matrix.cons_val_zero,Matrix.cons_val_one,modelPairCode,modelDecodeLeft,modelDecodeRight,Function.update]
  rfl

theorem synchronization (initial : Fin 11 → M) (tail steps : M) (hsteps : steps ≤ initial 8) :
    let d := F PA194DiagonalCode.run ![steps,pair (initial 6) (initial 7)]
    F (iterate advance) ![steps,sourceState 34 initial tail] =
      sourceState 34 (argsAt initial (pi₁ d) (pi₂ d) (F subCode ![initial 8,steps])) tail := by
  let e : Nat → M := fun n => if h : n<11 then initial ⟨n,h⟩ else tail
  have he : (fun i : Fin 11 => e i.val) = initial := by funext i; simp [e,i.isLt]
  have he8 : e 8 = initial 8 := by simp [e]
  have he11 : e 11 = tail := by simp [e]
  have main : body.Eval ![steps] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      right
      rw [he,he11]
      change F (iterate advance) ![(0 : M),sourceState 34 initial tail] = _
      rw [PA194DiagonalIteration.iterZero]
      change sourceState 34 initial tail = sourceState 34 (argsAt initial
        (pi₁ (F (iterate PA194DiagonalCode.next) ![(0 : M),pair (initial 6) (initial 7)]))
        (pi₂ (F (iterate PA194DiagonalCode.next) ![(0 : M),pair (initial 6) (initial 7)]))
        (F subCode ![initial 8,(0 : M)])) tail
      have hz : F subCode ![initial 8,(0 : M)] = initial 8 := PRASubtraction.modelSubZero _
      rw [PA194DiagonalIteration.iterZero,pi₁_pair,pi₂_pair,hz]
      congr 1
      funext i; fin_cases i <;> simp [argsAt]
    · intro u hu
      apply (body_eval (F Code.succ (fun _ => u)) e).mpr
      rw [he,he8,he11]
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      rw [hs]
      by_cases hbig : initial 8 < u+1
      · exact Or.inl hbig
      · right
        have hle : u+1 ≤ initial 8 := not_lt.mp hbig
        have hnot : ¬ initial 8 < u := not_lt_of_ge (le_of_lt (lt_of_lt_of_le (lt_add_one u) hle))
        have hp := (body_eval u e).mp hu
        rw [he8,he,he11] at hp
        have hp := hp.resolve_left hnot
        obtain ⟨w,hw⟩ := le_iff_exists_add.mp hle
        have h1 : F subCode ![initial 8,u+1] = w := by rw [hw]; exact modelSubAdd (u+1) w
        have h0 : F subCode ![initial 8,u] = w+1 := by
          rw [hw]
          have heq : (u+1)+w = u+(w+1) := by ac_rfl
          rw [heq]; exact modelSubAdd u (w+1)
        let d := F PA194DiagonalCode.run ![u,pair (initial 6) (initial 7)]
        let x := pi₁ d
        let y := pi₂ d
        let current := argsAt initial x y (w+1)
        have hp' : F (iterate advance) ![u,sourceState 34 initial tail] = sourceState 34 current tail := by
          simpa only [d,x,y,current,h0] using hp
        have hc8 : current 8 = w+1 := by simp [current,argsAt]
        have heval : F PA194DiagonalCode.run ![u+1,pair (initial 6) (initial 7)] = F PA194DiagonalCode.next ![d] := by
          change F (iterate PA194DiagonalCode.next) ![u+1,pair (initial 6) (initial 7)] = _
          rw [PA194DiagonalIteration.iterSucc]
          rfl
        change F (iterate advance) ![u+1,sourceState 34 initial tail] = _
        rw [PA194DiagonalIteration.iterSucc,hp']
        rw [heval,h1]
        by_cases hx : x = (0 : M)
        · let a1 := Function.update current 8 w
          let a2 := Function.update a1 7 (a1 7+1)
          let out := PA194UnpairDrainOpen.argsAt a2 (a2 7)
          have hc6 : current 6 = (0 : M) := by simp [current,argsAt,hx]
          have hr := PA194DecoderRoundOpen.advanceZero current tail w hc8 hc6
          change F advance ![sourceState 34 current tail] = sourceState 34 out tail at hr
          rw [hr]
          have hd : F PA194DiagonalCode.next ![d] = pair (y+1) (0 : M) := by
            rw [←pair_unpair d]
            change F PA194DiagonalCode.next ![pair x y] = _
            rw [hx,PA194DiagonalCode.nextZero]
          rw [hd,pi₁_pair,pi₂_pair]
          congr 1
          funext i; fin_cases i <;> simp [out,a2,a1,current,argsAt,PA194UnpairDrainOpen.argsAt,PA194UnpairDrainOpenComplete.subSelf,hx]
        · have hxpos : (0 : M) < x := lt_of_le_of_ne (zero_le : (0 : M) ≤ x) (Ne.symm hx)
          have hx1 : (1 : M) ≤ x := by simpa using (lt_iff_succ_le.mp hxpos)
          obtain ⟨a,ha⟩ := le_iff_exists_add.mp hx1
          have hxa : x = a+1 := by simpa [add_comm] using ha
          let a1 := Function.update current 8 w
          let a2 := Function.update a1 7 (a1 7+1)
          let out := Function.update a2 6 a
          have hc6 : current 6 = a+1 := by simp [current,argsAt,hxa]
          have hr := PA194DecoderRoundOpen.advancePositive current tail w a hc8 hc6
          change F advance ![sourceState 34 current tail] = sourceState 34 out tail at hr
          rw [hr]
          have hd : F PA194DiagonalCode.next ![d] = pair a (y+1) := by
            rw [←pair_unpair d]
            change F PA194DiagonalCode.next ![pair x y] = _
            rw [hxa,PA194DiagonalCode.nextPositive]
          rw [hd,pi₁_pair,pi₂_pair]
          congr 1
          funext i; fin_cases i <;> simp [out,a2,a1,current,argsAt,hxa]
  have h := (body_eval steps e).mp main
  rw [he8,he,he11] at h
  exact h.resolve_left (not_lt_of_ge hsteps)
#print axioms synchronization
end models
end PA194DecoderSynchronizationOpen
