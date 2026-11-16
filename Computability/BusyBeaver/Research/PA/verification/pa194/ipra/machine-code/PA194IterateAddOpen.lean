import PA194DiagonalIteration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194IterateAddOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PackedClock PackedRootModel
open PA194IteratedSimulation PA194DiagonalIteration
abbrev T := Semiterm language Nat 1
def body (f : Code 1) : Semiformula language Nat 1 := .rel Language.ORing.Rel.eq ![
  app2 (iterate f) (app2 addCode (.fvar 0) (.bvar 0)) (.fvar 1),
  app2 (iterate f) (.bvar 0) (app2 (iterate f) (.fvar 0) (.fvar 1))]
theorem body_open (f : Code 1) : (body f).Open := by simp [body,Semiformula.Open,Semiformula.qr]
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem body_eval (f : Code 1) (x : M) (e : Nat → M) :
    (body f).Eval ![x] e ↔ F (iterate f) ![e 0+x,e 1] = F (iterate f) ![x,F (iterate f) ![e 0,e 1]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (body f) ↔ _
  simp only [body,Semiformula.EvalAux,eqRel,Matrix.cons_val_zero,Matrix.cons_val_one,
    PA194DiagonalIteration.valApp2,Semiterm.val_bvar,Semiterm.val_fvar]
  rfl

theorem iterateAdd (f : Code 1) (a b seed : M) :
    F (iterate f) ![a+b,seed] = F (iterate f) ![b,F (iterate f) ![a,seed]] := by
  let e : Nat → M := fun j => if j=0 then a else seed
  have he0 : e 0 = a := by simp [e]
  have he1 : e 1 = seed := by simp [e]
  have main : (body f).Eval ![b] e := by
    apply modelOpenInduction (M := M) (body f) (body_open f) e
    · apply (body_eval f (0 : M) e).mpr
      rw [he0,he1,add_zero,iterZero]
    · intro u hu
      apply (body_eval f (F Code.succ (fun _ => u)) e).mpr
      have hprev := (body_eval f u e).mp hu
      rw [he0,he1] at hprev ⊢
      rw [←modelAddOne]
      change F (iterate f) ![a+(u+1),seed] = F (iterate f) ![u+1,F (iterate f) ![a,seed]]
      rw [←add_assoc,iterSucc,iterSucc,hprev]
  have h := (body_eval f b e).mp main
  simpa only [he0,he1] using h
#print axioms iterateAdd
end models
end PA194IterateAddOpen
