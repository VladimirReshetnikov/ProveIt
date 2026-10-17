import BusyBeaver.ZFC.ArithmeticProofConstructors254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticHistory254 ArithmeticRow254
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho7 rho8 bundle)
open ArithmeticProofConstructors254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.node_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.node_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_node
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.node_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.small_tag
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_truth
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_mp
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_gen
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_r1
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_r2
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_r3
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_r4
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_r5
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_r6
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_r7
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_r8
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors254.value_bundle
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out tag payload : V) : nodeDef.val.Evalb ![out,tag,payload] ↔ out=node tag payload := by simp
example (tag payload : V) : node tag payload≠0 := node_ne_zero tag payload
example (tag payload : V) (ht : tag<12) :
    value (node tag payload) = rowKernel tag payload
      (if tag=2 then value (second payload) else value (first (second payload)))
      (value (second (second payload))) := value_node tag payload ht
example (tag payload : Nat) : node tag payload=Code254Proof.node tag payload := node_nat tag payload
example : value (1 : V)=1 := value_truth
example (b a h p q : V) (hp : value p=a+1) (hq : value q=h+1) (he : h=wim a b) :
    value (node 1 (cantor b (cantor p q)))=b+1 := value_mp b a h p q hp hq he
example (a h p : V) (hp : value p=h+1) : value (node 2 (cantor a p))=wal a h+1 := value_gen a h p hp
example (a b : V) : value (node 3 (cantor a b))=rho1 a b+1 := value_r1 a b
example (a b c : V) : value (node 4 (cantor a (cantor b c)))=rho2 a b c+1 := value_r2 a b c
example (a b c : V) : value (node 5 (cantor a (cantor b c)))=rho3 a b c+1 := value_r3 a b c
example (a b c : V) : value (node 6 (cantor a (cantor b c)))=rho4 a b c+1 := value_r4 a b c
example (a b c : V) : value (node 7 (cantor a (cantor b c)))=rho5 a b c+1 := value_r5 a b c
example (a b : V) : value (node 8 (cantor a b))=rho6 a b+1 := value_r6 a b
example (a b c : V) : value (node 9 (cantor a (cantor b c)))=rho7 a b c+1 := value_r7 a b c
example (a b c u : V) : value (node 10 (cantor a (cantor b (cantor c u))))=rho8 a b c u+1 := value_r8 a b c u
example (a b c : V) (ha : c≠a) (hb : c≠b) : value (node 11 (cantor a (cantor b c)))=bundle a b c+1 := value_bundle a b c ha hb
example (a p : V) (hp : value p=1) : value (node 2 (cantor a p))=wal a 0+1 := value_gen a 0 p (by simpa using hp)
example (b a p q : V) (hp : value p=a+1) (hq : value q=wim a b+1) :
    value (node 1 (cantor b (cantor p q)))=b+1 := value_mp b a (wim a b) p q hp hq rfl
