import PA194BinaryDouble
import PA194StateOne
import PackedIterationModel
set_option autoImplicit false
namespace PA194UnaryRuns
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194BinaryDouble PA194StateOne PackedIterationModel ConfigurationStep PRAModelIOpenPairing

def inc {n : Nat} (x : Code n) : Code n := unary .succ x
def pushOne : Code 1 := inc (bin addCode (.proj 0) (.proj 0))
def onesBody : Code 3 := unary pushOne (.proj 1)
def ones : Code 2 := .prec (.proj 0) onesBody

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelPushOne (x : M) : F pushOne (fun _ => x) = x+x+1 := by
  simp only [pushOne, inc, modelUnary, modelBin, modelProjection, ←modelAddOne]
  rfl

theorem modelOnesZero (x : M) : F ones ![(0 : M),x] = x := by
  have h := modelBase (M := M) (Code.proj (0 : Fin 1)) onesBody (fun _ => x)
  rw [modelProjection] at h
  have hs : Fin.cases (F (Code.zero 0) Fin.elim0) (fun _ : Fin 1 => x) = ![(0 : M),x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  exact h

theorem modelOnesSucc (n x : M) : F ones ![F Code.succ (fun _ => n),x] =
    F ones ![n,x] + F ones ![n,x] + 1 := by
  have h := modelStep (M := M) (Code.proj (0 : Fin 1)) onesBody ![n,x]
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
  change F ones ![F Code.succ (fun _ => n),x] = F onesBody
    (Fin.cases n (Fin.cases (F ones ![n,x]) (fun _ => x))) at h
  rw [h,onesBody,modelUnary,modelProjection]
  exact modelPushOne _
theorem modelPackedOneTransition (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![(1 : M),F pairCode ![l,(r+r)+1]]) =
    F pairCode ![(1 : M),F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![(1 : M),l,(r+r)+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![(1 : M),l,(r+r)+1],F nextL ![(1 : M),l,(r+r)+1],
    F nextR ![(1 : M),l,(r+r)+1]) = stepSem 1 l ((r+r)+1) at hm
  rw [←hm,modelStateOneOddTape]

#print axioms modelPackedOneTransition

#print axioms modelPushOne
#print axioms modelOnesZero
#print axioms modelOnesSucc
end models
end PA194UnaryRuns
