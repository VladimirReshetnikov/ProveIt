import PA194Path25To27
import PA194Path27To28
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroThenPositive
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site27HeaderDispatch PA194EightyFourTo17 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194HeaderController BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

def clock25 (k : M) (args : Fin 11 → M) : M :=
    let v := physicalArgs args
    let e : Fin 12 → M := Fin.cases (k+1) v
    let e1 : Fin 11 → M := fun i => e i.succ
    let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
    let backClock := (e1 0+1)+((e 0+1)+1)
    let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let c0 := (modelNumeral M 12 + (((((k+1)+1)+1)+1)+((k+1)+1))) + modelNumeral M 4
    let c1 := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let c2 := ((modelNumeral M 7+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 5)+returnClock
    let c3 := ((1 : M)+(k+1))+modelNumeral M 3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    (((((((((c0+c1)+c2)+modelNumeral M 12)+k)+((modelNumeral M 3+e1 0)+modelNumeral M 2))+modelNumeral M 1)+((modelNumeral M 2+modelNumeral M 2)+e1 0))+((modelNumeral M 2+(k+1))+modelNumeral M 4))+(((modelNumeral M 2+1)+(k+1))+1))+(c3+(modelNumeral M 3+rc))

def clock27 (k : M) (e : Fin 11 → M) : M :=
    let v := physicalArgs e
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    let aa0 := (1 : M)+(1 : M)+1
    let aa1 := aa0+aa0
    let aa2 := aa1+aa1
    let aa3 := aa2+aa2
    let aa4 := aa3+aa3+1
    let aa5 := aa4+aa4
    let aa6 := aa5+aa5
    let n := (k+1)+1
    let b := F ones ![k+1,aa6+aa6]
    let base := (b+b+1)+(b+b+1)
    let e0 := v
    let e1 : Fin 10 → M := fun j => e0 j.succ
    let e2 : Fin 9 → M := fun j => e1 j.succ
    let e3 : Fin 8 → M := fun j => e2 j.succ
    let e4 : Fin 7 → M := fun j => e3 j.succ
    let e5 : Fin 6 → M := fun j => e4 j.succ
    let e6 : Fin 5 → M := fun j => e5 j.succ
    let t1 := (e0 0+1)+1
    let t2 := (e1 0+1)+1
    let t3 := (e2 0+1)+1
    let t4 := (e3 0+1)+1
    let t5 := (e4 0+1)+1
    let t6 := (e5 0+1)+1
    let c6 := (((((t1+t2)+t3)+t4)+t5)+t6)
    let q := F ones ![e6 0,F (fileCode 3) (fun i => e6 i.succ)]
    let rev : Fin 6 → M := ![v 4,v 3,v 2,v 1,v 0,base]
    let cr := (modelNumeral M 2+((v 5+1)+1))+F (PA194CarryFile.costCode 5) rev
    let croot := (((((1 : M)+k)+1)+1)+(modelNumeral M 3+(modelNumeral M 3+rc)))
    let vec : Fin 7 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,(q+q)+(q+q)]
    let ccarry := ((k+1)+F (PA194CarryFile.costCode 6) vec)+modelNumeral M 2
    let ct1 := (1 : M)+(v 5+1)
    let ct2 := (1 : M)+(v 4+1)
    let ct3 := (1 : M)+(v 3+1)
    let ct4 := (1 : M)+(v 2+1)
    let ct5 := (1 : M)+(v 1+1)
    let ct6 := (1 : M)+(v 0+1)
    let cret := (((((ct1+ct2)+ct3)+ct4)+ct5)+ct6)
    let ch := ((1 : M)+((k+1)+1))+modelNumeral M 3
    let cs := ((modelNumeral M 2+1)+(k+1))+1
    let cp := (((1 : M)+(k+1))+modelNumeral M 3)+(modelNumeral M 2+(modelNumeral M 3+rc))
    ((((((((((((modelNumeral M 13+(((((k+1)+1)+1)+1)+((k+1)+1)))+(modelNumeral M 5+rc))+modelNumeral M 8)+(n+1))+(c6+cr))+croot)+modelNumeral M 13)+ccarry)+modelNumeral M 1)+cret)+ch)+cs)+cp

def frame (path : Nat) (n : M) (e : Fin 11 → M) : M :=
  let f := F sourceFileCode e
  F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
    PA194Path27Header.modelWord (PA194SourceProgram.path path) (F zeros ![n,(1 : M)+(f+f)])]]

theorem zeroThenPositive (k m : M) (e : Fin 11 → M)
    (hz : e 8 = (0 : M)) (hp : e 0 = m+1) :
    F PA194Stepper.stepper ![clock27 k e,
      F PA194Stepper.stepper ![clock25 (k+1) e,frame 25 (((k+1)+1)+1) e]] =
    frame 28 ((k+1)+1) (Function.update e 0 m) := by
  have h25 := PA194Path25To27.zeroBranchPath25To27 (M := M) (k+1) e hz
  change F PA194Stepper.stepper ![clock25 (k+1) e,frame 25 (((k+1)+1)+1) e] =
    frame 27 ((k+1)+1) e at h25
  have h27 := PA194Path27To28.positiveBranchPath27To28 (M := M) k m e hp
  change F PA194Stepper.stepper ![clock27 k e,frame 27 ((k+1)+1) e] =
    frame 28 ((k+1)+1) (Function.update e 0 m) at h27
  exact (congrArg (fun x => F PA194Stepper.stepper ![clock27 k e,x]) h25).trans h27
#print axioms zeroThenPositive
end models
end PA194ZeroThenPositive
