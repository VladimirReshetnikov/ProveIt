import PA194TargetLeavesStandard
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetGate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable
 PA194NumeralCode PA194TargetCantor PA194TargetLeaves PA194TargetLeavesStandard

noncomputable def machineConj {n : Nat} (p q : Code n) : Code n :=
  machineNeg (machineImp p (machineNeg q))
noncomputable def memVac : Code 3 :=
  machineImp (machineMem (.proj 0) (.proj 1))
    (machineAll (.proj 2) (machineMem (.proj 0) (.proj 1)))
noncomputable def point : Code 3 := machineImp (.proj 2) (machineMem (.proj 2) (.proj 1))
noncomputable def separation : Code 3 :=
  machineAll (.proj 1) (machineConj (machineImp (machineMem (.proj 0) (.proj 1)) point)
    (machineImp (machineMem (.proj 2) (.proj 1)) (.proj 2)))
noncomputable def separationTail : Code 3 :=
  machineAll (.proj 2) (machineImp separation (machineNeg point))
noncomputable def oldBundle : Code 3 := machineNeg (machineImp memVac separationTail)
/-- Zero means rejection; a successful guarded bundle is returned plus one. -/
noncomputable def checkGate : Code 3 :=
  selectAmong (bin equalityCode (.proj 2) (.proj 0)) (.zero 3)
    (selectAmong (bin equalityCode (.proj 2) (.proj 1)) (.zero 3) (unary .succ oldBundle))

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

noncomputable def conjValue (p q : M) := negValue (impValue p (negValue q))
noncomputable def memVacValue (a b c : M) := impValue (memValue a b) (allValue c (memValue a b))
noncomputable def pointValue (b c : M) := impValue c (memValue c b)
noncomputable def separationValue (a b c : M) :=
  allValue b (conjValue (impValue (memValue a b) (pointValue b c)) (impValue (memValue c b) c))
noncomputable def separationTailValue (a b c : M) :=
  allValue c (impValue (separationValue a b c) (negValue (pointValue b c)))
noncomputable def oldBundleValue (a b c : M) := negValue (impValue (memVacValue a b c) (separationTailValue a b c))

theorem conj_model {n : Nat} (p q : Code n) (e : Fin n → M) :
    F (machineConj p q) e = conjValue (F p e) (F q e) := by
  simp only [machineConj,machineNeg_model,machineImp_model,conjValue]
theorem memVac_model (a b c : M) : F memVac ![a,b,c] = memVacValue a b c := by
  simp only [memVac,machineImp_model,machineAll_model,mem_model,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,memVacValue]
  rfl
theorem point_model (a b c : M) : F point ![a,b,c] = pointValue b c := by
  simp only [point,machineImp_model,mem_model,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,pointValue]
  rfl
theorem separation_model (a b c : M) : F separation ![a,b,c] = separationValue a b c := by
  simp only [separation,machineAll_model,conj_model,machineImp_model,mem_model,point_model,modelProjection,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,separationValue]
  rfl
theorem separationTail_model (a b c : M) : F separationTail ![a,b,c] = separationTailValue a b c := by
  simp only [separationTail,machineAll_model,machineImp_model,machineNeg_model,separation_model,point_model,modelProjection,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,separationTailValue]
  rfl
theorem oldBundle_model (a b c : M) : F oldBundle ![a,b,c] = oldBundleValue a b c := by
  simp only [oldBundle,machineNeg_model,machineImp_model,memVac_model,separationTail_model,oldBundleValue]
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem checkGate_model (a b c : M) : F checkGate ![a,b,c] =
    if c = a then 0 else if c = b then 0 else oldBundleValue a b c + 1 := by
  simp only [checkGate,modelChooseEqual,modelProjection,PRAMultiplication.modelZero,modelUnary,modelSucc,oldBundle_model,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl
theorem gate_accepts_iff (a b c : M) :
    F checkGate ![a,b,c] = oldBundleValue a b c + 1 ↔ c ≠ a ∧ c ≠ b := by
  rw [checkGate_model]
  by_cases ha : c = a <;> by_cases hb : c = b <;>
    simp [ha,hb,zero_ne_add_one]

#print axioms checkGate_model
#print axioms gate_accepts_iff
end models
section standard
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

theorem eval_oldBundle (a b c : Nat) :
    eval oldBundle (a ::ᵥ b ::ᵥ c ::ᵥ List.Vector.nil) = PA196.Commands.Code.oldBundle a b c := by
  have hh := oldBundle_model (M := Nat) a b c
  change eval oldBundle (List.Vector.ofFn ![a,b,c]) = _ at hh
  rw [ofFn_three] at hh
  rw [hh]
  simp only [oldBundleValue,memVacValue,separationTailValue,separationValue,pointValue,conjValue,
    PA196.Commands.Code.oldBundle,PA196.Commands.Code.memVac,PA196.Commands.Code.separationTail,
    PA196.Commands.Code.separation,PA196.Commands.Code.point,PA196.Commands.Code.conj,
    (primitive_standard _ _).1,(primitive_standard _ _).2.1,(primitive_standard _ 0).2.2.1,
    (primitive_standard _ _).2.2.2.2.1]

noncomputable def oldBundle_derivation (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    PA194DerivationCompiler.Derivation (eval oldBundle (a ::ᵥ b ::ᵥ c ::ᵥ List.Vector.nil)) := by
  rw [eval_oldBundle]
  exact .gate a b c ha hb

#print axioms eval_oldBundle
#print axioms oldBundle_derivation
end standard
end PA194TargetGate
