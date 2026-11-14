import DiophantineConsistency.PRAHistoryIterator
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ParamIterator
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryIterator PRAHistoryPairCode

theorem getCode_pack {n : ℕ} (m : ℕ) (f : Fin m → Code n) :
    getCode (pack m f) = f := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (fun j => f j.succ)) j

def firstHistory {k : ℕ} (cons : Code 2) (base : Code k) : Code k :=
  bin cons (.zero k) base

def nextValue {k : ℕ} (base : Code k) (step : Code (k+2)) : Code (k+2) :=
  .comp (.prec base step) (pack (k+1) (Fin.cases
    (.comp .succ (.cons (.proj 0) (.nil (k+2))))
    (fun j => .proj j.succ.succ)))

def historyStep {k : ℕ} (cons : Code 2) (base : Code k) (step : Code (k+2)) : Code (k+2) :=
  bin cons (.proj 1) (nextValue base step)

def historyCode {k : ℕ} (cons : Code 2) (base : Code k) (step : Code (k+2)) : Code (k+1) :=
  .prec (firstHistory cons base) (historyStep cons base step)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)

theorem modelNextValue {k : ℕ} (base : Code k) (step : Code (k+2)) (i h : M) (v : Fin k → M) :
    F (nextValue base step) (Fin.cases i (Fin.cases h v)) =
      F (.prec base step) (Fin.cases (F Code.succ (fun _ => i)) v) := by
  rw [nextValue,modelComposition, getCode_pack]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change F (.comp .succ (.cons (.proj 0) (.nil (k+2)))) (Fin.cases i (Fin.cases h v)) = F Code.succ (fun _ => i)
    rw [modelComposition]
    congr 1
    funext q
    refine Fin.cases ?_ (fun r => Fin.elim0 r) q
    exact modelProjection 0 _
  · change F (.proj j.succ.succ) (Fin.cases i (Fin.cases h v)) = v j
    exact modelProjection j.succ.succ _

theorem modelFirstHistory {k : ℕ} (cons : Code 2) (base : Code k) (v : Fin k → M) :
    F (firstHistory cons base) v = F cons ![F (.zero k) v, F base v] := by
  rw [firstHistory, modelBin]

theorem modelHistoryStepValue {k : ℕ} (cons : Code 2) (base : Code k) (step : Code (k+2))
    (i h : M) (v : Fin k → M) :
    F (historyStep cons base step) (Fin.cases i (Fin.cases h v)) =
      F cons ![h, F (.prec base step) (Fin.cases (F Code.succ (fun _ => i)) v)] := by
  rw [historyStep,modelBin,modelProjection,modelNextValue]
  rfl
theorem modelHistoryBase {k : ℕ} (cons : Code 2) (base : Code k) (step : Code (k+2)) (v : Fin k → M) :
    F (historyCode cons base step) (Fin.cases (F (.zero 0) Fin.elim0) v) =
      F cons ![F (.zero 0) Fin.elim0, F base v] := by
  rw [historyCode, modelBase, modelFirstHistory, PRAMultiplication.modelZero]

theorem modelHistoryStep {k : ℕ} (cons : Code 2) (base : Code k) (step : Code (k+2))
    (i : M) (v : Fin k → M) :
    F (historyCode cons base step) (Fin.cases (F .succ (fun _ => i)) v) =
      F cons ![F (historyCode cons base step) (Fin.cases i v),
        F (.prec base step) (Fin.cases (F .succ (fun _ => i)) v)] := by
  have h := modelStep (M := M) (firstHistory cons base) (historyStep cons base step) (Fin.cases i v)
  change F (historyCode cons base step) (Fin.cases (F .succ (fun _ => i)) v) =
    F (historyStep cons base step) (Fin.cases i (Fin.cases
      (F (historyCode cons base step) (Fin.cases i v)) v)) at h
  rw [modelHistoryStepValue] at h
  exact h

#print axioms modelHistoryBase
#print axioms modelHistoryStep
#print axioms modelNextValue
#print axioms modelFirstHistory
#print axioms modelHistoryStepValue
end models
end PA194ParamIterator
