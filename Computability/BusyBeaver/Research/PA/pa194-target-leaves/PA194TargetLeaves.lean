import PA194TargetCantor
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetLeaves
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PA194NumeralCode PA194TargetCantor

noncomputable def machineMem {n : Nat} (a b : Code n) : Code n :=
  bin addCode (machineImp a b) (numeralCode n 1)
noncomputable def machineEq {n : Nat} (a b : Code n) : Code n :=
  bin addCode (machineImp a b) (numeralCode n 3)
noncomputable def head2 : Code 3 :=
  machineImp (machineAll (.proj 0) (machineAll (.proj 1) (.proj 2)))
    (machineAll (.proj 1) (machineAll (.proj 0) (.proj 2)))
noncomputable def head3 : Code 3 :=
  machineImp (machineMem (.proj 2) (.proj 0))
    (machineImp (machineEq (.proj 2) (.proj 1)) (machineMem (.proj 1) (.proj 0)))
noncomputable def head4 : Code 3 :=
  machineImp (machineEq (.proj 2) (.proj 0))
    (machineImp (machineMem (.proj 1) (.proj 2)) (machineMem (.proj 1) (.proj 0)))
noncomputable def head5 : Code 2 := machineEx (.proj 0) (machineEq (.proj 1) (.proj 0))
noncomputable def head6 : Code 3 :=
  machineImp (machineAll (.proj 0) (.proj 1))
    (machineImp (machineAll (.proj 0) (machineImp (.proj 1) (.proj 2)))
      (machineAll (.proj 0) (.proj 2)))
noncomputable def rho8 : Code 4 :=
  machineImp (machineImp (machineImp (.proj 2) (.proj 3)) (.proj 0))
    (machineImp (machineImp (.proj 0) (.proj 2)) (machineImp (.proj 1) (.proj 2)))
noncomputable def diagonal : Code 1 := machineImp (.proj 0) (machineAll (.proj 0) (.proj 0))

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

noncomputable def memValue (a b : M) := impValue a b + 1
noncomputable def eqValue (a b : M) := impValue a b + 3
noncomputable def head2Value (d a h : M) := impValue (allValue d (allValue a h)) (allValue a (allValue d h))
noncomputable def head3Value (d a h : M) := impValue (memValue h d) (impValue (eqValue h a) (memValue a d))
noncomputable def head4Value (d a h : M) := impValue (eqValue h d) (impValue (memValue a h) (memValue a d))
noncomputable def head5Value (d h : M) := exValue d (eqValue h d)
noncomputable def head6Value (d a h : M) := impValue (allValue d a) (impValue (allValue d (impValue a h)) (allValue d h))
noncomputable def rho8Value (a b c u : M) := impValue (impValue (impValue c u) a) (impValue (impValue a c) (impValue b c))
noncomputable def diagonalValue (c : M) := impValue c (allValue c c)

theorem mem_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (machineMem a b) e = memValue (F a e) (F b e) := by
  rw [machineMem,modelBin,machineImp_model,modelNumeralCode]
  simp only [Nat.cast_one]
  rfl
theorem eq_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (machineEq a b) e = eqValue (F a e) (F b e) := by
  rw [machineEq,modelBin,machineImp_model,modelNumeralCode]
  rfl

theorem head2_model (d a h : M) : F head2 ![d,a,h] = head2Value d a h := by
  simp only [head2,machineImp_model,machineAll_model,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,head2Value]
  rfl
theorem head3_model (d a h : M) : F head3 ![d,a,h] = head3Value d a h := by
  simp only [head3,machineImp_model,mem_model,eq_model,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,head3Value]
  rfl
theorem head4_model (d a h : M) : F head4 ![d,a,h] = head4Value d a h := by
  simp only [head4,machineImp_model,mem_model,eq_model,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,head4Value]
  rfl
theorem head5_model (d h : M) : F head5 ![d,h] = head5Value d h := by
  simp only [head5,machineEx_model,eq_model,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,head5Value]
theorem head6_model (d a h : M) : F head6 ![d,a,h] = head6Value d a h := by
  simp only [head6,machineImp_model,machineAll_model,modelProjection,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,head6Value]
  rfl
theorem rho8_model (a b c u : M) : F rho8 ![a,b,c,u] = rho8Value a b c u := by
  simp only [rho8,machineImp_model,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_def,rho8Value]
  rfl
theorem diagonal_model (c : M) : F diagonal ![c] = diagonalValue c := by
  simp only [diagonal,machineImp_model,machineAll_model,modelProjection,Matrix.cons_val_zero,diagonalValue]

#print axioms head2_model
#print axioms head3_model
#print axioms head4_model
#print axioms head5_model
#print axioms head6_model
#print axioms rho8_model
#print axioms diagonal_model
end models
end PA194TargetLeaves
