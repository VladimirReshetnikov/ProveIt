import BusyBeaver.ZFC.TarskiCalculus

/-!
A finite counterinterpretation isolates the role of rho6 in falsity.
Lukasiewicz rho8, modus ponens and even unrestricted generalization do not
derive primitive bot -> R(0,0). Interpret bot as true, all atoms as false,
and every quantifier as the identity. This is a counterinterpretation of
the weakened proof rules, not a model of the full Tarski calculus.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski.PrimitiveBottomAudit

open NF

inductive Pure : NF → Prop
  | rho8 (c u a b : NF) : Pure (luk c u a b)
  | mp {a b : NF} : Pure (imp a b) → Pure a → Pure b
  | gen (i : Nat) {a : NF} : Pure a → Pure (all i a)

def value : NF → Bool
  | bot => true
  | rel _ _ => false
  | NF.eq _ _ => false
  | imp a b => !value a || value b
  | all _ a => value a

theorem valid_rho8 (c u a b : NF) : value (luk c u a b) = true := by
  simp only [luk, value]
  cases value c <;> cases value u <;> cases value a <;> cases value b <;> rfl

theorem pure_valid {a : NF} (h : Pure a) : value a = true := by
  induction h with
  | rho8 c u a b => exact valid_rho8 c u a b
  | @mp a b _ _ ihab iha =>
    simp only [value, iha, Bool.not_true, Bool.false_or] at ihab
    exact ihab
  | gen i _ ih => exact ih

theorem no_efq : ¬ Pure (imp bot (rel 0 0)) := by
  intro h
  have impossible := pure_valid h
  cases impossible

end SetTheory.BusyBeaver.ZFC.Tarski.PrimitiveBottomAudit

#print axioms SetTheory.BusyBeaver.ZFC.Tarski.PrimitiveBottomAudit.no_efq
