import PA194Head1Graph
/-! The target modus-ponens checker operation, not a complete proof-history
checker. Accepted values are theorem numbers plus one. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194TargetMP
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor

def previousMinor : Code 3 := unary predCode (.proj 0)
noncomputable def expectedMajor : Code 3 := unary .succ (machineImp previousMinor (.proj 2))
/-- Inputs are accepted minor, accepted major, and requested conclusion.
Zero rejects; a successor is the accepted conclusion plus one. -/
noncomputable def impBinary : Code 2 := machineImp (.proj 0) (.proj 1)
noncomputable def checkMP : Code 3 :=
  selectAmong (bin equalityCode (.proj 0) (.zero 3)) (.zero 3)
    (selectAmong (bin equalityCode (.proj 1) (.zero 3)) (.zero 3)
      (selectAmong (bin equalityCode (.proj 1) expectedMajor) (unary .succ (.proj 2)) (.zero 3)))

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

theorem check_model (minor major b : M) : F checkMP ![minor,major,b] =
    if minor = 0 then 0 else if major = 0 then 0 else
      if major = impValue (F predCode (fun _ => minor)) b + 1 then b+1 else 0 := by
  simp only [checkMP,expectedMajor,previousMinor,modelChooseEqual,modelProjection,
    PRAMultiplication.modelZero,modelUnary,machineImp_model,modelSucc]
  rfl

theorem check_correct (minor major b : M) : F checkMP ![minor,major,b] = b+1 ↔
    ∃ a, minor = a+1 ∧ major = impValue a b + 1 := by
  rw [check_model]
  constructor
  · intro h
    split at h
    · exact False.elim (zero_ne_add_one b h)
    · rename_i hminor
      split at h
      · exact False.elim (zero_ne_add_one b h)
      · split at h
        · rename_i hmajor
          rcases zero_or_succ minor with hm | ⟨a,ha⟩
          · exact False.elim (hminor hm)
          · refine ⟨a,ha,?_⟩
            rw [ha,modelPredAddOne] at hmajor
            exact hmajor
        · exact False.elim (zero_ne_add_one b h)
  · rintro ⟨a,rfl,rfl⟩
    have hm : a+1 ≠ 0 := by simp
    have hn : impValue a b+1 ≠ 0 := by simp
    rw [if_neg hm,if_neg hn,modelPredAddOne,if_pos rfl]

#print axioms check_correct
#print axioms check_model
end models
section standard
open PA194TargetHead1Standard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

theorem eval_impBinary (a b : Nat) :
    eval impBinary (a ::ᵥ b ::ᵥ List.Vector.nil) = PA196.Commands.Code.I a b := by
  have h := machineImp_model (M := Nat) (.proj 0 : Code 2) (.proj 1) ![a,b]
  simp only [modelProjection, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change eval impBinary (List.Vector.ofFn ![a,b]) = _ at h
  rw [ofFn_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  have hp (x y : Nat) := modelCantorSelected (M := Nat) fixedCantor fixedCantor_certified x y
  have heval (x y : Nat) : Structure.func (L := language) fixedCantor ![x,y] = M6.Source.Cantor.pair x y := by
    change eval fixedCantor (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_fixedCantor x y
  have hpair := fun x y => (hp x y).symm.trans (heval x y)
  have hmul (x y : Nat) := localMul_eq (M := Nat) x y
  have hM (x y : Nat) : Structure.func (L := language) mulCode ![x,y] = x*y := by
    change eval mulCode (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_mulCode x y
  have hmul' := fun x y => (hmul x y).trans (hM x y)
  have h4 := localFour_eq (M := Nat)
  change _ = eval (PA194NumeralCode.numeralCode 0 4) (List.Vector.ofFn Fin.elim0) at h4
  have e4 : eval (PA194NumeralCode.numeralCode 0 4) (List.Vector.ofFn Fin.elim0) = 4 := by decide
  rw [e4] at h4
  simp only [impValue, hpair, PA196.Commands.Code.I]
  simp only [hmul',h4]

#print axioms eval_impBinary
end standard

end PA194TargetMP
