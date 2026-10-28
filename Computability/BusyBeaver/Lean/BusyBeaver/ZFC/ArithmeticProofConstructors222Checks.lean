import BusyBeaver.ZFC.ArithmeticProofConstructors222

set_option autoImplicit false
set_option Elab.async false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticHistory222 ArithmeticProofConstructors222

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : value (0 : V) = 0 := value_zero

example (a conclusion p : V) (h : value p = conclusion + 1) :
    value (node 2 (cantor a p)) = wal a conclusion + 1 := value_gen a conclusion p h

example (conclusion minor major p q : V) (hp : value p = minor + 1)
    (hq : value q = major + 1) (he : major = wim minor conclusion) :
    value (node 1 (cantor conclusion (cantor p q))) = conclusion + 1 :=
  value_mp conclusion minor major p q hp hq he

example (a b c : V) : value (node 9 (cantor a (cantor b c))) =
    wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b))) + 1 := by
  simpa [ArithmeticTemplates222.growG_eq] using value_growG a b c

example (a c : V) (h : c ≠ a) : value (node 11 (cantor a (cantor a c))) =
    ArithmeticSeedTemplates222.bundle222 a a c + 1 := value_bundle a a c h h

example (a b : V) (ha : (0 : V) ≠ a) (hb : (0 : V) ≠ b) :
    value (node 11 (cantor a (cantor b 0))) =
      ArithmeticSeedTemplates222.bundle222 a b 0 + 1 := value_bundle a b 0 ha hb

example (a b : V) : value (node 11 (cantor a (cantor b a))) = 0 :=
  value_bundle_rejected a b a (Or.inl rfl)

example (a b : V) : value (node 11 (cantor a (cantor b b))) = 0 :=
  value_bundle_rejected a b b (Or.inr rfl)
end Internal

#print axioms node_defined
#print axioms value_node
#print axioms value_truth
#print axioms value_mp
#print axioms value_gen
#print axioms value_r1
#print axioms value_r2
#print axioms value_r3
#print axioms value_r4
#print axioms value_r5
#print axioms value_r6
#print axioms value_growG
#print axioms value_r8
#print axioms value_bundle
#print axioms value_bundle_rejected

end SetTheory.BusyBeaver.ZFC.ArithmeticProofConstructors222Checks
