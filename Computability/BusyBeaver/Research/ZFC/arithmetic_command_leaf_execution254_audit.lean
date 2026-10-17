import BusyBeaver.ZFC.ArithmeticCommandLeafExecution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho7 rho8 bundle)
open ArithmeticCommandStep254 ArithmeticCommandAppend254 ArithmeticCommandRun254
open ArithmeticProofWordContract254 ArithmeticCommandBlockExecution254 ArithmeticCommandLeafExecution254
open ArithmeticCommandBlocks254 (Circuit)
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.eval_nips_cont
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.select_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf_contract
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf2
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf3
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf4
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf5
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf6
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf7
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.leaf8
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandLeafExecution254.bundle_contract
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (t s d : V) (xs : List V) (h last rest : V)
    (hh : h ≠ 1) (hx : ∀ x, x ∈ xs → x ≠ 1) :
    evalValue (appendValue (nipsWord (xs.length+1)) rest)
      (stateValue t (pushL (xs++[last]) s) d h) = evalValue rest (stateValue t s d last) :=
  eval_nips_cont t s d xs h last rest hh hx
example (xs : List V) (x : V) (ys : List V) (last g h s : V)
    (hh : h ≠ 1) (hg : g ≠ 1) (hx : x ≠ 1)
    (hxs : ∀ y, y ∈ xs → y ≠ 1) (hys : ∀ y, y ∈ ys → y ≠ 1) :
    evalValue (appendValue (nipsWord (xs.length+1)) (dropWord 0 (nipsWord (ys.length+2))))
      (stateValue g (pushL (xs++x::(ys++[last])) s) 0 h) = someState x s 0 last :=
  select_entry xs x ys last g h s hh hg hx hxs hys
example (j : Nat) (a b c u x : V) (xs ys : List V)
    (hsplit : axList a 0 b c u = xs++x::ys)
    (hj : xs.length+1 = j) (hk : ys.length+2 = 11-j) : Contract (leafWord j a b c u) x :=
  leaf_contract j a b c u x xs ys hsplit hj hk
example (a b c u : V) : Contract (Circuit.leaf1.eval a b c u) (rho1 a b) := leaf1 a b c u
example (a b c u : V) : Contract (Circuit.leaf2.eval a b c u) (rho2 a b c) := leaf2 a b c u
example (a b c u : V) : Contract (Circuit.leaf3.eval a b c u) (rho3 a b c) := leaf3 a b c u
example (a b c u : V) : Contract (Circuit.leaf4.eval a b c u) (rho4 a b c) := leaf4 a b c u
example (a b c u : V) : Contract (Circuit.leaf5.eval a b c u) (rho5 a b c) := leaf5 a b c u
example (a b c u : V) : Contract (Circuit.leaf6.eval a b c u) (rho6 a b) := leaf6 a b c u
example (a b c u : V) : Contract (Circuit.leaf7.eval a b c u) (rho7 a b c) := leaf7 a b c u
example (a b c u : V) : Contract (Circuit.leaf8.eval a b c u) (rho8 a b c u) := leaf8 a b c u
example (a b c u : V) (h1 : c ≠ a) (h2 : c ≠ b) :
    Contract ((Circuit.bundleLeaf .input0 .input1 .input2).eval a b c u) (bundle a b c) :=
  bundle_contract a b c u h1 h2
