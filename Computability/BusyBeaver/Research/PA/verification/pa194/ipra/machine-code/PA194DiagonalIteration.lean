import PA194DiagonalCode
import DiophantineConsistency.PRAOpenInduction
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194DiagonalIteration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubtraction PRAOpenInduction
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PackedClock PackedRootModel PackedDecoderModel
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194DiagonalCode PA194TargetCantor PA194MachineProjections PA194IteratedSimulation
noncomputable def scoreCode : Code 1 := bin fixedCantor decodeLeft decodeRight
abbrev T := Semiterm language Nat 1
def app1 (f : Code 1) (a : T) : T := .func f ![a]
def app2 (f : Code 2) (a b : T) : T := .func f ![a,b]
noncomputable def body : Semiformula language Nat 1 := .rel Language.ORing.Rel.eq ![
    app1 scoreCode (app2 run (.bvar 0) (.fvar 0)),
    app2 addCode (app1 scoreCode (.fvar 0)) (.bvar 0)]
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

theorem modelScore (s : M) : F scoreCode ![s] = cantor (pi₁ s) (pi₂ s) := by
  have hv : (![s] : Fin 1 → M) = (fun _ => s) := by funext i; fin_cases i; rfl
  rw [hv,scoreCode,modelBin,modelDecodeLeft,modelDecodeRight]
  exact modelCantorSelected fixedCantor fixedCantor_certified _ _

theorem valApp1 (x : M) (e : Nat → M) (f : Code 1) (a : T) :
    Semiterm.val ![x] e (app1 f a) = F f (fun _ => Semiterm.val ![x] e a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i; exact Fin.cases rfl (fun k => Fin.elim0 k) i

theorem valApp2 (x : M) (e : Nat → M) (f : Code 2) (a b : T) :
    Semiterm.val ![x] e (app2 f a b) = F f ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  funext i; fin_cases i <;> rfl

theorem body_eval (x : M) (e : Nat → M) :
    body.Eval ![x] e ↔ F scoreCode ![F run ![x,e 0]] = F scoreCode ![e 0] + x := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  simp only [body,Semiformula.EvalAux,eqRel]
  have hv (a b : T) : (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
    funext i; fin_cases i <;> rfl
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,valApp1,valApp2,Semiterm.val_bvar,Semiterm.val_fvar]
  have hv1 (z : M) : (fun _ : Fin 1 => z) = ![z] := by funext i; fin_cases i; rfl
  simp only [hv1]
  rfl

theorem iterZero (f : Code 1) (seed : M) : F (iterate f) ![(0 : M),seed] = seed := by
  have h := modelBase (M := M) (.proj 0) (unary f (.proj 1)) ![seed]
  change F (iterate f) ![0,seed] = F (.proj 0) ![seed] at h
  rw [modelProjection] at h
  exact h

theorem iterSucc (f : Code 1) (n seed : M) :
    F (iterate f) ![n+1,seed] = F f ![F (iterate f) ![n,seed]] := by
  have h := modelStep (M := M) (.proj 0) (unary f (.proj 1)) ![n,seed]
  change F (iterate f) ![F Code.succ (fun _ => n),seed] =
    F (unary f (.proj 1)) ![n,F (iterate f) ![n,seed],seed] at h
  rw [←modelAddOne] at h
  change F (iterate f) ![n+1,seed] = _ at h
  rw [h,modelUnary,modelProjection]
  congr 1
  funext i; fin_cases i; rfl

theorem scoreIteration (start steps : M) :
    F scoreCode ![F run ![steps,start]] = F scoreCode ![start]+steps := by
  let e : Nat → M := fun _ => start
  have main : body.Eval ![steps] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval (0 : M) e).mpr
      change F scoreCode ![F (iterate next) ![(0 : M),start]] = F scoreCode ![start]+0
      rw [iterZero,add_zero]
    · intro u hu
      apply (body_eval (F Code.succ (fun _ => u)) e).mpr
      have hu' := (body_eval u e).mp hu
      simp only [e] at hu' ⊢
      rw [←modelAddOne]
      change F scoreCode ![F (iterate next) ![u+1,start]] = _
      rw [iterSucc]
      change F scoreCode ![F next ![F run ![u,start]]] = _
      rw [modelScore,scoreNext,←modelScore,hu']
      change (F scoreCode ![start]+u)+1 = F scoreCode ![start]+(u+1)
      exact add_assoc _ _ _
  exact (body_eval steps e).mp main
#print axioms scoreIteration
end models
end PA194DiagonalIteration
