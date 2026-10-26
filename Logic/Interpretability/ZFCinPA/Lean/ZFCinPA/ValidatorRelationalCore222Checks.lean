import ZFCinPA.ValidatorRelationalCore222

set_option autoImplicit false
set_option Elab.async false

namespace LeanProofs.ZFCinPA.ValidatorRelationalCore222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The literal legal seed case c=0 and a=b=1 remains admitted. -/
theorem zero_equal_labels : Vac (0 : V) (wel 1 1) :=
  vac_rel 1 1 0 zero_ne_one zero_ne_one

/-- Quantifying the vacuous membership formula needs no extra condition
on the newly added binder j. -/
theorem quantified_membership (a b i j : V) (ha : i ≠ a) (hb : i ≠ b) :
    Vac i (wal j (wel a b)) := vac_all j (vac_rel a b i ha hb)

theorem two_binder (h p q x y : V)
    (hpq : CProv (wim h (wim (weq x y) (wim p q))))
    (vxh : Vac x h) (vxq : Vac x q)
    (vyh : Vac y h) (vyall : Vac y (wal x p)) :
    CProv (wim h (wim (wal x p) (wal y q))) :=
  all_relational h p q x y hpq vxh vxq vyh vyall

/-- The result is an actual proof-code witness for the new history,
not merely a propositional validity claim. -/
theorem zero_equal_labels_witness :
    ∃ code : V, ArithmeticHistory222.value code =
      wim (wel (1 : V) 1) (wal 0 (wel 1 1)) + 1 :=
  zero_equal_labels

#print axioms vac_rel
#print axioms vac_neg
#print axioms vac_imp
#print axioms vac_all
#print axioms vac_conj
#print axioms conj_rule
#print axioms all_under_two
#print axioms all_relational
#print axioms zero_equal_labels
#print axioms zero_equal_labels_witness

end LeanProofs.ZFCinPA.ValidatorRelationalCore222Checks
