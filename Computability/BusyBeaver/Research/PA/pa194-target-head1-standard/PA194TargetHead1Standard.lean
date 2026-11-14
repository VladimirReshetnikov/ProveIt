import PA194TargetCantor
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194TargetHead1Standard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PA194NumeralCode PA194TargetCantor
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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
theorem localAdd_eq (a b : M) : a+b = F addCode ![a,b] := rfl
theorem localMul_eq (a b : M) : a*b = F mulCode ![a,b] := rfl
theorem localOne_eq : (1 : M) = F (numeralCode 0 1) Fin.elim0 := by
  symm; simpa using modelNumeralCode 0 1 (Fin.elim0 : Fin 0 → M)
theorem localTwo_eq : (2 : M) = F (numeralCode 0 2) Fin.elim0 := by
  symm; simpa using modelNumeralCode 0 2 (Fin.elim0 : Fin 0 → M)
theorem localFour_eq : (4 : M) = F (numeralCode 0 4) Fin.elim0 := by
  symm; simpa using modelNumeralCode 0 4 (Fin.elim0 : Fin 0 → M)

end models
section standard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
theorem eval_machineHead1 (a b : Nat) :
    eval machineHead1 (a ::ᵥ b ::ᵥ List.Vector.nil) = PA196.Commands.Code.head1 a b := by
  have h := machineHead1_model (M := Nat) a b
  change eval machineHead1 (List.Vector.ofFn ![a,b]) = _ at h
  rw [ofFn_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  have hp (x y : Nat) := modelCantorSelected (M := Nat) fixedCantor fixedCantor_certified x y
  have heval (x y : Nat) : Structure.func (L := language) fixedCantor ![x,y] = M6.Source.Cantor.pair x y := by
    change eval fixedCantor (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_fixedCantor x y
  have hpair := fun x y => (hp x y).symm.trans (heval x y)
  have hadd (x y : Nat) := localAdd_eq (M := Nat) x y
  have hmul (x y : Nat) := localMul_eq (M := Nat) x y
  have hA (x y : Nat) : Structure.func (L := language) addCode ![x,y] = x+y := by
    change eval addCode (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_addCode x y
  have hM (x y : Nat) : Structure.func (L := language) mulCode ![x,y] = x*y := by
    change eval mulCode (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_mulCode x y
  have hadd' := fun x y => (hadd x y).trans (hA x y)
  have hmul' := fun x y => (hmul x y).trans (hM x y)
  have h1 := localOne_eq (M := Nat)
  have h2 := localTwo_eq (M := Nat)
  have h4 := localFour_eq (M := Nat)
  change _ = eval (numeralCode 0 1) (List.Vector.ofFn Fin.elim0) at h1
  change _ = eval (numeralCode 0 2) (List.Vector.ofFn Fin.elim0) at h2
  change _ = eval (numeralCode 0 4) (List.Vector.ofFn Fin.elim0) at h4
  have e1 : eval (numeralCode 0 1) (List.Vector.ofFn Fin.elim0) = 1 := by decide
  have e2 : eval (numeralCode 0 2) (List.Vector.ofFn Fin.elim0) = 2 := by decide
  have e4 : eval (numeralCode 0 4) (List.Vector.ofFn Fin.elim0) = 4 := by decide
  rw [e1] at h1
  rw [e2] at h2
  rw [e4] at h4
  simp only [head1Value,exValue,negValue,allValue,impValue, hpair,
    PA196.Commands.Code.head1,PA196.Commands.Code.ex,PA196.Commands.Code.N,
    PA196.Commands.Code.U,PA196.Commands.Code.I]
  simp only [hadd', hmul',h1,h2,h4]

noncomputable def head1_code_derivation (a b : Nat) :
    PA194DerivationCompiler.Derivation (eval machineHead1 (a ::ᵥ b ::ᵥ List.Vector.nil)) := by
  rw [eval_machineHead1]
  exact .h1 a b

#print axioms eval_machineHead1
#print axioms head1_code_derivation

end standard
end PA194TargetHead1Standard
