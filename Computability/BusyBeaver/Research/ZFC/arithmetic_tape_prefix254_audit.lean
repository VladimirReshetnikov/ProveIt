import BusyBeaver.ZFC.ArithmeticTapePrefix254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.prefix_product_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix_add_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix_bit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix_half
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.exp_le_prefix_add_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254.onesPrefix_definable
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (n suffix : V) : onesPrefix n suffix + 1 = Exp.exp n * (suffix+1) := onesPrefix_add_one n suffix
example (suffix : V) : onesPrefix 0 suffix = suffix := onesPrefix_zero suffix
example (n suffix : V) : onesPrefix (n+1) suffix = 2 * onesPrefix n suffix + 1 := onesPrefix_succ n suffix
example (n suffix : V) : onesPrefix n (2*suffix+1) = onesPrefix (n+1) suffix := onesPrefix_push n suffix
example (n suffix : V) : onesPrefix (n+1) suffix % 2 = 1 := onesPrefix_bit n suffix
example (n suffix : V) : onesPrefix (n+1) suffix / 2 = onesPrefix n suffix := onesPrefix_half n suffix
example (out n suffix : V) : onesPrefixDef.val.Evalb ![out,n,suffix] ↔ out = onesPrefix n suffix := by simp
example : onesPrefixDef.val.Evalb (M := V) ![0,0,0] := by simp
example : onesPrefix (0 : V) 0 = 0 := by simp
example (n suffix : V) : Exp.exp n ≤ onesPrefix n suffix+1 := exp_le_prefix_add_one n suffix
