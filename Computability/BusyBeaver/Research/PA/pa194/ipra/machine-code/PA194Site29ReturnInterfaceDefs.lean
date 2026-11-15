import PA194Site29ReturnPath30
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnInterfaceDefs
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194Site28CarryCodes PA194StartupSourceFrame PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def headerBase : M :=
  let d0 := (1 : M)+(1 : M)+1
  let d1 := d0+d0
  let d2 := d1+d1
  let d3 := d2+d2
  let d4 := d3+d3+1
  let d5 := d4+d4
  let d6 := d5+d5+1
  let j := d6+d6+1
  j+j
def marked (ns : Fin 7 → M) (m k n : M) : M :=
  let d := headerBase (M := M)
  let A := F ones ![k,(d+d)+(d+d)]
  let A1 := A+A+1
  let z := F ones ![m,(A1+A1)+(A1+A1)+1]
  let a0 := F ones ![ns 0,(z+z)+(z+z)+1]
  let a1 := F ones ![ns 1,(a0+a0)+(a0+a0)+1]
  let a2 := F ones ![ns 2,(a1+a1)+(a1+a1)+1]
  let a3 := F ones ![ns 3,(a2+a2)+(a2+a2)+1]
  let a4 := F ones ![ns 4,(a3+a3)+(a3+a3)+1]
  let a5 := F ones ![ns 5,(a4+a4)+(a4+a4)+1]
  let a := F ones ![ns 6,(a5+a5)+(a5+a5)+1]
  F ones ![n+1,(a+a)+(a+a)+1]
def carryOut (spare : M) : M :=
  let e := PA194Site29SeedTailRoundTrip.ext spare
  let vv := e ⟨26,by decide⟩
  let ss := ((1 : M)+1)+1
  let qq := ss+ss
  let ww := F ones ![vv,(1 : M)+qq+qq]
  let tt := ww+ww
  let vals : Fin 27 → M := fun i => e i.castSucc
  F (PA194ReturnFile.returnCode 26) (Fin.cases tt vals)
def outHalf (ns : Fin 7 → M) (m n spare : M) : M :=
  let out := carryOut spare
  let r0 := F ones ![n+1,(1 : M)+out+out]
  let r1 := F ones ![ns 6,(1 : M)+(r0+r0)+(r0+r0)]
  let r2 := F ones ![ns 5,(1 : M)+(r1+r1)+(r1+r1)]
  let r3 := F ones ![ns 4,(1 : M)+(r2+r2)+(r2+r2)]
  let r4 := F ones ![ns 3,(1 : M)+(r3+r3)+(r3+r3)]
  let r5 := F ones ![ns 2,(1 : M)+(r4+r4)+(r4+r4)]
  let r6 := F ones ![ns 1,(1 : M)+(r5+r5)+(r5+r5)]
  let r7 := F ones ![ns 0,(1 : M)+(r6+r6)+(r6+r6)]
  F ones ![m,(1 : M)+(r7+r7)+(r7+r7)]
def continuation (ns : Fin 7 → M) (m k n spare init : M) : M :=
  let e := PA194Site29SeedTailRoundTrip.ext spare
  let vv := e ⟨26,by decide⟩
  let vals : Fin 27 → M := fun i => e i.castSucc
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  F PA194Stepper.stepper ![modelNumeral M 2+(modelNumeral M 3+rc),
    F PA194Stepper.stepper ![(1 : M),
      F PA194Stepper.stepper ![(1 : M),
        F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
          F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
            F PA194Stepper.stepper ![modelNumeral M 2,
              F PA194Stepper.stepper ![(k+1)+1,
                F PA194Stepper.stepper ![(m+1)+1,
                  F PA194Stepper.stepper ![(ns 0+1)+1,
                    F PA194Stepper.stepper ![(ns 1+1)+1,
                      F PA194Stepper.stepper ![(ns 2+1)+1,
                        F PA194Stepper.stepper ![(ns 3+1)+1,
                          F PA194Stepper.stepper ![(ns 4+1)+1,
                            F PA194Stepper.stepper ![(ns 5+1)+1,
                              F PA194Stepper.stepper ![(ns 6+1)+1,
                                F PA194Stepper.stepper ![((n+1)+1)+1,
                                  F PA194Stepper.stepper ![F (PA194CarryFile.costCode 26) vals,
                                    F PA194Stepper.stepper ![modelNumeral M 2+((vv+1)+1),
                                      F PA194Stepper.stepper ![modelNumeral M 3,
                                        F PA194Stepper.stepper ![(1 : M)+(vv+1),
                                          F PA194Stepper.stepper ![F (timeCode 26) e,init]]]]]]]]]]]]]]]]]]]]]
#print axioms continuation
end models
end PA194Site29ReturnInterfaceDefs
