import BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252 ArithmeticSymbolicTapePerm252
open SymbolicPerm252 (Box Token Segment SConfig)
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.bitPrefix_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.bitPrefix_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.bitPrefix_false_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.tapePrefix_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.tokensPrefix_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.push_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.norm_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.dropExterior_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.normL_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252.isMatch_value
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (b : Bool) (n m suffix : V) :
    bitPrefix b (n+m) suffix = bitPrefix b n (bitPrefix b m suffix) := bitPrefix_add b n m suffix
example (b : Bool) (suffix : V) : bitPrefix b 1 suffix = 2*suffix+digit b := bitPrefix_one b suffix
example (n : V) : bitPrefix false n (0 : V) = 0 := bitPrefix_false_zero n
example (gap : V) (boxes : Box → V → V) (xs ys : List Segment) (suffix : V) :
    tapePrefix gap boxes (xs++ys) suffix =
      tapePrefix gap boxes xs (tapePrefix gap boxes ys suffix) := tapePrefix_append gap boxes xs ys suffix
example (gap : V) (boxes : Box → V → V) (xs ys : List Token) (suffix : V) :
    tokensPrefix gap boxes (xs++ys) suffix =
      tokensPrefix gap boxes xs (tokensPrefix gap boxes ys suffix) := tokensPrefix_append gap boxes xs ys suffix
example (gap : V) (boxes : Box → V → V) (x : Token) (xs : List Token) (suffix : V) :
    tokensPrefix gap boxes (SymbolicPerm252.push x xs) suffix =
      tokenPrefix gap boxes x (tokensPrefix gap boxes xs suffix) := push_prefix gap boxes x xs suffix
example (gap : V) (boxes : Box → V → V) (xs : List Segment) (suffix : V) :
    tokensPrefix gap boxes (SymbolicPerm252.norm xs) suffix = tapePrefix gap boxes xs suffix :=
  norm_prefix gap boxes xs suffix
example (gap : V) (boxes : Box → V → V) (xs : List Token) :
    tokensPrefix gap boxes (SymbolicPerm252.dropExterior xs) 0 = tokensPrefix gap boxes xs 0 :=
  dropExterior_zero gap boxes xs
example (gap : V) (boxes : Box → V → V) (xs : List Segment) :
    tokensPrefix gap boxes (SymbolicPerm252.normL xs) 0 = tapePrefix gap boxes xs 0 := normL_zero gap boxes xs
example (gap : V) (boxes : Box → V → V) (s t : SConfig) (h : SymbolicPerm252.isMatch s t = true) :
    configValue gap boxes s = configValue gap boxes t := isMatch_value gap boxes s t h
example (gap : V) (boxes : Box → V → V) :
    configValue gap boxes ⟨some ⟨94,by decide⟩,false,[.run false 1 0],[]⟩ =
      configValue gap boxes ⟨some ⟨94,by decide⟩,false,[],[]⟩ :=
  isMatch_value gap boxes _ _ (by decide)
example (gap : V) (boxes : Box → V → V) :
    configValue gap boxes ⟨some ⟨94,by decide⟩,true,[],[.run true 1 2,.run true 2 3]⟩ =
      configValue gap boxes ⟨some ⟨94,by decide⟩,true,[],[.run true 3 5]⟩ :=
  isMatch_value gap boxes _ _ (by decide)
