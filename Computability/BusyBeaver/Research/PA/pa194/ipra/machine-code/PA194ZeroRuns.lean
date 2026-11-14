import PA194BinaryDouble
import PA194StateFifteen
import PackedIterationModel
set_option autoImplicit false
namespace PA194ZeroRuns
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194BinaryDouble PA194StateFifteen PackedIterationModel ConfigurationStep PRAModelIOpenPairing

def inc {n : Nat} (x : Code n) : Code n := unary .succ x
def pushZero : Code 1 := bin addCode (.proj 0) (.proj 0)
def zerosBody : Code 3 := unary pushZero (.proj 1)
def zeros : Code 2 := .prec (.proj 0) zerosBody

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelPushZero (x : M) : F pushZero (fun _ => x) = x+x := by
  simp only [pushZero, modelBin, modelProjection]
  rfl

theorem modelZerosZero (x : M) : F zeros ![(0 : M),x] = x := by
  have h := modelBase (M := M) (Code.proj (0 : Fin 1)) zerosBody (fun _ => x)
  rw [modelProjection] at h
  have hs : Fin.cases (F (Code.zero 0) Fin.elim0) (fun _ : Fin 1 => x) = ![(0 : M),x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  exact h

theorem modelZerosSucc (n x : M) : F zeros ![F Code.succ (fun _ => n),x] =
    F zeros ![n,x] + F zeros ![n,x] := by
  have h := modelStep (M := M) (Code.proj (0 : Fin 1)) zerosBody ![n,x]
  have hs : Fin.cases (F Code.succ (fun _ => ![n,x] 0))
      (fun i => ![n,x] i.succ) = ![F Code.succ (fun _ => n),x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  have hv : (fun i : Fin 1 => ![n,x] i.succ) = (fun _ => x) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv] at h
  simp only [Matrix.cons_val_zero] at h
  change F zeros ![F Code.succ (fun _ => n),x] = F zerosBody
    (Fin.cases n (Fin.cases (F zeros ![n,x]) (fun _ => x))) at h
  rw [h,zerosBody,modelUnary,modelProjection]
  exact modelPushZero _
theorem modelPackedZeroTransition (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 15,F pairCode ![l+l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 15,F pairCode ![l,(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 15,l+l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 15,l+l,r+r],F nextL ![TableDispatch.modelNumeral M 15,l+l,r+r],
    F nextR ![TableDispatch.modelNumeral M 15,l+l,r+r]) = stepSem (TableDispatch.modelNumeral M 15) (l+l) (r+r) at hm
  rw [←hm,modelStateFifteenEven]

#print axioms modelPackedZeroTransition

#print axioms modelPushZero
#print axioms modelZerosZero
#print axioms modelZerosSucc
end models
end PA194ZeroRuns
