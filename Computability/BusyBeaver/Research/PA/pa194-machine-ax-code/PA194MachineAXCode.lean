import PA194MachineStack
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194MachineAXCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor PA194TargetLeaves
 PA194TargetStep PA194TargetExtendedStep PA194TargetGate PA194MachineStack
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

noncomputable def pair {n : Nat} (a b : Code n) : Code n := bin fixedCantor a b
noncomputable def axStackCode {n : Nat} (t A d h y x w : Code n) : Code n :=
  let D := bin addCode d x
  let H := bin addCode h y
  pair (unary diagonal A)
    (pair (app3 head6 D A H)
      (pair (bin head5 D H)
        (pair (app3 head4 D A H)
          (pair (app3 head3 D A H)
            (pair (app3 head2 D A H)
              (pair (bin machineHead1 D H)
                (pair (app4 rho8 D A H d)
                  (pair (machineAll d h) (pair t w)))))))))
noncomputable def axTopCode {n : Nat} (A d h y x : Code n) : Code n :=
  let D := bin addCode d x
  let H := bin addCode h y
  selectAmong (bin equalityCode D A) (.zero n)
    (selectAmong (bin equalityCode H A) (.zero n) (app3 oldBundle H D A))

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

theorem pair_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (pair a b) e = cantor (F a e) (F b e) := by
  rw [pair,modelBin,modelCantorSelected fixedCantor fixedCantor_certified]
theorem add_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (bin addCode a b) e = F a e + F b e := by
  rw [modelBin]
  rfl

theorem axStack_model {n : Nat} (t A d h y x w : Code n) (e : Fin n → M) :
    F (axStackCode t A d h y x w) e =
      axStack (F d e+F x e) (F h e+F y e) (F A e) (F d e) (F h e) (F t e) (F w e) := by
  have hdiag : F diagonal (fun _ => F A e) = diagonalValue (F A e) := by
    have hv : (fun _ : Fin 1 => F A e) = ![F A e] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv,diagonal_model]
  simp only [axStackCode,pair_model,app3_model,app4_model,modelUnary,add_model,modelBin,
    head6_model,head5_model,head4_model,head3_model,head2_model,machineHead1_model,rho8_model,
    machineAll_model,hdiag,axStack]
  rfl

theorem axTop_model {n : Nat} (A d h y x : Code n) (e : Fin n → M) :
    F (axTopCode A d h y x) e = axTop (F h e+F y e) (F d e+F x e) (F A e) := by
  simp only [axTopCode,modelChooseEqual,PRAMultiplication.modelZero,app3_model,oldBundle_model,add_model,axTop]
  by_cases hd : F d e + F x e = F A e <;> by_cases hh : F h e + F y e = F A e <;> simp [hd,hh] <;> rfl

theorem axCode_preserves {n : Nat} (t A d h y x w : Code n) (e : Fin n → M)
    (hs : SoundStore (F t e) (F w e) (F h e)) :
    SoundStore (F (axTopCode A d h y x) e) (F (axStackCode t A d h y x w) e) 0 := by
  rw [axTop_model,axStack_model]
  exact ax_preserves (F t e) (F w e) (F h e) (F d e) (F x e) (F y e) (F A e) hs

#print axioms axCode_preserves
#print axioms axStack_model
#print axioms axTop_model
end models
end PA194MachineAXCode
