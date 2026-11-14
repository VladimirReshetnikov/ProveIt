import PA194TargetMP
/-! The target generalization checker operation, not proof-history validation. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194TargetGen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor

noncomputable def allBinary : Code 2 := machineAll (.proj 0) (.proj 1)
def previous : Code 2 := unary predCode (.proj 0)
/-- Inputs are an accepted premise and a quantifier label. -/
noncomputable def checkGen : Code 2 :=
  selectAmong (bin equalityCode (.proj 0) (.zero 2)) (.zero 2)
    (unary .succ (machineAll (.proj 1) previous))
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

theorem check_model (premise label : M) : F checkGen ![premise,label] =
    if premise = 0 then 0 else allValue label (F predCode (fun _ => premise))+1 := by
  simp only [checkGen,previous,modelChooseEqual,modelProjection,PRAMultiplication.modelZero,
    modelUnary,machineAll_model,modelSucc]
  rfl

theorem check_correct (premise label y : M) : F checkGen ![premise,label] = y+1 ↔
    ∃ a, premise = a+1 ∧ y = allValue label a := by
  rw [check_model]
  constructor
  · intro h
    split at h
    · exact False.elim (zero_ne_add_one y h)
    · rename_i hne
      rcases zero_or_succ premise with hz | ⟨a,ha⟩
      · exact False.elim (hne hz)
      · refine ⟨a,ha,?_⟩
        rw [ha,modelPredAddOne] at h
        exact (add_right_cancel h).symm
  · rintro ⟨a,rfl,rfl⟩
    have hn : a+1 ≠ 0 := by simp
    rw [if_neg hn,modelPredAddOne]

#print axioms check_correct
end models
section standard
open PA194TargetHead1Standard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

theorem eval_allBinary (a b : Nat) :
    eval allBinary (a ::ᵥ b ::ᵥ List.Vector.nil) = PA196.Commands.Code.U a b := by
  have h := machineAll_model (M := Nat) (.proj 0 : Code 2) (.proj 1) ![a,b]
  simp only [modelProjection, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change eval allBinary (List.Vector.ofFn ![a,b]) = _ at h
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
  have h2 := localTwo_eq (M := Nat)
  have h4 := localFour_eq (M := Nat)
  change _ = eval (PA194NumeralCode.numeralCode 0 2) (List.Vector.ofFn Fin.elim0) at h2
  change _ = eval (PA194NumeralCode.numeralCode 0 4) (List.Vector.ofFn Fin.elim0) at h4
  have e2 : eval (PA194NumeralCode.numeralCode 0 2) (List.Vector.ofFn Fin.elim0) = 2 := by decide
  have e4 : eval (PA194NumeralCode.numeralCode 0 4) (List.Vector.ofFn Fin.elim0) = 4 := by decide
  rw [e2] at h2
  rw [e4] at h4
  simp only [allValue,impValue,hpair,PA196.Commands.Code.U]
  simp only [hadd',hmul',h2,h4]

#print axioms eval_allBinary
end standard

end PA194TargetGen
