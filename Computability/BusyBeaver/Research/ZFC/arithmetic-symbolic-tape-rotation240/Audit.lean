import BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252
open SymbolicRotation240 (Segment Token Box SConfig)
open ArithmeticSymbolicTapeRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.tapePrefix_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.tokensPrefix_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.tokenOf_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.push_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.norm_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.dropExterior_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.normL_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.configValue_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.configValue_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240.isMatch_value

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (gap : V) (boxes : Box → V → V) (xs ys : List Segment) (suffix : V) :
    tapePrefix gap boxes (xs++ys) suffix =
      tapePrefix gap boxes xs (tapePrefix gap boxes ys suffix) :=
  tapePrefix_append gap boxes xs ys suffix
example (gap : V) (boxes : Box → V → V) (xs ys : List Token) (suffix : V) :
    tokensPrefix gap boxes (xs++ys) suffix =
      tokensPrefix gap boxes xs (tokensPrefix gap boxes ys suffix) :=
  tokensPrefix_append gap boxes xs ys suffix
example (gap : V) (boxes : Box → V → V) (x : Segment) (suffix : V) :
    tokenPrefix gap boxes (SymbolicRotation240.tokenOf x) suffix =
      segmentPrefix gap boxes x suffix := tokenOf_prefix gap boxes x suffix
example (gap : V) (boxes : Box → V → V) (x : Token) (xs : List Token) (suffix : V) :
    tokensPrefix gap boxes (SymbolicRotation240.push x xs) suffix =
      tokenPrefix gap boxes x (tokensPrefix gap boxes xs suffix) :=
  push_prefix gap boxes x xs suffix
example (gap : V) (boxes : Box → V → V) (xs : List Segment) (suffix : V) :
    tokensPrefix gap boxes (SymbolicRotation240.norm xs) suffix =
      tapePrefix gap boxes xs suffix := norm_prefix gap boxes xs suffix
example (gap : V) (boxes : Box → V → V) (xs : List Token) :
    tokensPrefix gap boxes (SymbolicRotation240.dropExterior xs) 0 =
      tokensPrefix gap boxes xs 0 := dropExterior_zero gap boxes xs
example (gap : V) (boxes : Box → V → V) (xs : List Segment) :
    tokensPrefix gap boxes (SymbolicRotation240.normL xs) 0 =
      tapePrefix gap boxes xs 0 := normL_zero gap boxes xs
example (gap : V) (boxes : Box → V → V) (q : Option (Fin 240)) (l r : List Segment) :
    configValue gap boxes ⟨q,false,l,r⟩ =
      frame (ArithmeticMachinePerm252.stateCode q : V)
        (tapePrefix gap boxes l 0) (tapePrefix gap boxes r 0) :=
  configValue_right gap boxes q l r
example (gap : V) (boxes : Box → V → V) (q : Option (Fin 240)) (l r : List Segment) :
    configValue gap boxes ⟨q,true,l,r⟩ =
      leftFrame (ArithmeticMachinePerm252.stateCode q : V)
        (tapePrefix gap boxes l 0) (tapePrefix gap boxes r 0) :=
  configValue_left gap boxes q l r
example (gap : V) (boxes : Box → V → V) (s t : SConfig)
    (h : SymbolicRotation240.isMatch s t = true) :
    configValue gap boxes s = configValue gap boxes t := isMatch_value gap boxes s t h

-- Normalization keeps an arbitrary suffix even under a box prefix parameter.
example (gap suffix : V) (boxes : Box → V → V) (x : Box) (tail : List Segment) :
    tokensPrefix gap boxes (SymbolicRotation240.norm (.box x::tail)) suffix =
      boxes x (tapePrefix gap boxes tail suffix) :=
  norm_prefix gap boxes (.box x::tail) suffix
-- An actual halting state is encoded as zero; no execution theorem is inferred.
example (gap : V) (boxes : Box → V → V) (l r : List Segment) :
    configValue gap boxes ⟨none,false,l,r⟩ =
      frame 0 (tapePrefix gap boxes l 0) (tapePrefix gap boxes r 0) := rfl
