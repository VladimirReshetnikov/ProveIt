import PA194Transfer45Loop
import PA194IterateAddOpen
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Transfer45Open
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition PRASubtraction PRAOpenInduction
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisterRelation PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194Transfer45Loop PA194DiagonalIteration PA194IteratedSimulation
abbrev T := Semiterm language Nat 1
def add (a b : T) : T := app2 addCode a b
def pairT (a b : T) : T := app2 pairCode a b
def stateT : T := app1 (constantCode 45) (.bvar 0)
def sourceT (r : Fin 9 → T) (tail : T) : T :=
  pairT stateT
    (pairT (r 0) (pairT (r 1) (pairT (r 2) (pairT (r 3) (pairT (r 4)
      (pairT (r 5) (pairT (r 6) (pairT (r 7) (pairT (r 8) tail)))))))))
def initialRegs (i : Fin 9) : T := .fvar i.val
def runningRegs (i : Fin 9) : T :=
  if i.val = 3 then add (.fvar 3) (.bvar 0)
  else if i.val = 6 then app2 subCode (.fvar 6) (.bvar 0)
  else .fvar i.val
def threeT : T := add (add (.bvar 0) (.bvar 0)) (.bvar 0)
def body : Semiformula language Nat 1 := .or
  (.rel Language.ORing.Rel.lt ![(.fvar 6 : T),(.bvar 0 : T)])
  (.rel Language.ORing.Rel.eq ![
    app2 PA194SourceControllerCode.run threeT (sourceT initialRegs (.fvar 11)),
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
noncomputable def argsAt (args : Fin 11 → M) (j : M) : Fin 11 → M :=
  Function.update (Function.update args 6 (F subCode ![args 6,j])) 3 (args 3+j)
def three (j : M) : M := (j+j)+j

theorem body_eval (x : M) (e : Nat → M) :
    body.Eval ![x] e ↔ e 6 < x ∨
      F PA194SourceControllerCode.run ![three x,sourceState 45 (fun i : Fin 11 => e i.val) (e 11)] =
        sourceState 45 (argsAt (fun i : Fin 11 => e i.val) x) (e 11) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : T) : (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  have hstate : Semiterm.val ![x] e stateT = modelNumeral M 45 := by
    rw [stateT,PA194DiagonalIteration.valApp1,Semiterm.val_bvar]
    exact modelConstant 45 x
  simp [sourceT,pairT,add,threeT,initialRegs,runningRegs,sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,argsAt,three,
    PA194DiagonalIteration.valApp2,hstate,Semiterm.val_bvar,Semiterm.val_fvar,Matrix.cons_val_zero,Matrix.cons_val_one,
    modelPairCode,Function.update]
  rfl

theorem runDrain (args : Fin 11 → M) (tail j : M) (hj : j ≤ args 6) :
    F PA194SourceControllerCode.run ![three j,sourceState 45 args tail] = sourceState 45 (argsAt args j) tail := by
  let e : Nat → M := fun n => if h : n<11 then args ⟨n,h⟩ else tail
  have he : (fun i : Fin 11 => e i.val) = args := by funext i; simp [e,i.isLt]
  have he6 : e 6 = args 6 := by simp [e]
  have he11 : e 11 = tail := by simp [e]
  have main : body.Eval ![j] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      right
      rw [he,he11]
      have hz : F subCode ![args 6,(0 : M)] = args 6 := PRASubtraction.modelSubZero _
      have hid : argsAt args (0 : M) = args := by funext i; fin_cases i <;> simp [argsAt,hz]
      dsimp only [three]
      simp only [zero_add]
      change F (iterate step) ![(0 : M),sourceState 45 args tail] = _
      rw [iterZero,hid]
    · intro u hu
      apply (body_eval (F Code.succ (fun _ => u)) e).mpr
      rw [he,he6,he11]
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      rw [hs]
      by_cases hbig : args 6 < u+1
      · exact Or.inl hbig
      · right
        have hle : u+1 ≤ args 6 := not_lt.mp hbig
        have hnot : ¬ args 6 < u := not_lt_of_ge (le_of_lt (lt_of_lt_of_le (lt_add_one u) hle))
        have hp := (body_eval u e).mp hu
        rw [he,he6,he11] at hp
        have hp := hp.resolve_left hnot
        obtain ⟨d,hd⟩ := le_iff_exists_add.mp hle
        have h1 : F subCode ![args 6,u+1] = d := by rw [hd]; exact modelSubAdd (u+1) d
        have h0 : F subCode ![args 6,u] = d+1 := by
          rw [hd]
          have heq : (u+1)+d = u+(d+1) := by ac_rfl
          rw [heq]; exact modelSubAdd u (d+1)
        have hm : argsAt args u 6 = d+1 := by simp [argsAt,h0]
        have hloop := transferLoop (argsAt args u) tail d hm
        have hargs : Function.update (Function.update (argsAt args u) 6 d) 3 ((Function.update (argsAt args u) 6 d) 3+1) = argsAt args (u+1) := by
          funext i; fin_cases i <;> simp [argsAt,h0,h1,add_assoc]
        have hthree : three (u+1) = ((three u+1)+1)+1 := by dsimp [three]; ac_rfl
        rw [hthree]
        change F (iterate step) ![((three u+1)+1)+1,sourceState 45 args tail] = _
        rw [iterSucc,iterSucc,iterSucc]
        change F step ![F step ![F step ![F PA194SourceControllerCode.run ![three u,sourceState 45 args tail]]]] = _
        rw [hp,hloop,hargs]
  have h := (body_eval j e).mp main
  rw [he6,he,he11] at h
  exact h.resolve_left (not_lt_of_ge hj)
#print axioms runDrain
end models
end PA194Transfer45Open
