import PA194DecoderClock
import PA194DecoderSynchronizationOpen
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194DecoderClockOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194IteratedSimulation PA194CumulativeClock PA194DecoderRoundCode PA194DecoderClock PA194DiagonalIteration
abbrev T := Semiterm language Nat 1
noncomputable def body : Semiformula language Nat 1 := .rel Language.ORing.Rel.eq ![
  app2 PA194SourceControllerCode.run (app2 totalClock (.bvar 0) (.fvar 0)) (.fvar 0),
  app2 (iterate advance) (.bvar 0) (.fvar 0)]
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

theorem body_eval (x : M) (e : Nat → M) :
    body.Eval ![x] e ↔ F PA194SourceControllerCode.run ![F totalClock ![x,e 0],e 0] = F (iterate advance) ![x,e 0] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  simp only [body,Semiformula.EvalAux,eqRel,Matrix.cons_val_zero,Matrix.cons_val_one,
    PA194DiagonalIteration.valApp2,Semiterm.val_bvar,Semiterm.val_fvar]

theorem accumulate (start steps : M) :
    F PA194SourceControllerCode.run ![F totalClock ![steps,start],start] = F (iterate advance) ![steps,start] := by
  let e : Nat → M := fun _ => start
  have main : body.Eval ![steps] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      change F PA194SourceControllerCode.run ![F totalClock ![(0 : M),start],start] = F (iterate advance) ![0,start]
      rw [totalClock,clockZero]
      change F (iterate step) ![(0 : M),start] = F (iterate advance) ![0,start]
      rw [PA194DiagonalIteration.iterZero,PA194DiagonalIteration.iterZero]
    · intro n ih
      apply (body_eval (F Code.succ (fun _ => n)) e).mpr
      have hprev := (body_eval n e).mp ih
      simp only [e] at hprev ⊢
      rw [←modelAddOne]
      change F PA194SourceControllerCode.run ![F totalClock ![n+1,start],start] = F (iterate advance) ![n+1,start]
      rw [totalClock,clockSucc]
      have hv : (fun _ : Fin 1 => F (iterate advance) ![n,start]) = ![F (iterate advance) ![n,start]] := by funext i; fin_cases i; rfl
      rw [hv]
      change F (iterate step) ![F totalClock ![n,start]+F roundClock ![F (iterate advance) ![n,start]],start] = _
      rw [PA194IterateAddOpen.iterateAdd]
      change F PA194SourceControllerCode.run ![F roundClock ![F (iterate advance) ![n,start]],F PA194SourceControllerCode.run ![F totalClock ![n,start],start]] = _
      rw [hprev,←advanceModel,PA194DiagonalIteration.iterSucc]
  exact (body_eval steps e).mp main
#print axioms accumulate
end models
end PA194DecoderClockOpen
