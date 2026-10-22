import BusyBeaver.ZFC.KLowerQHyp

namespace EnvelopeInterfaceAudit
open SetTheory SetTheory.Form
open SetTheory.BusyBeaver.ZFC SetTheory.BusyBeaver.ZFC.KLower
universe u
variable {V : Type u} {mem : V → V → Prop}

example (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V}
    (ht : ∀ z, ¬ mem z t) (a : V) (ha : mem t a) :
    ∃ E, E ≠ t ∧ ¬ mem t E ∧ ∀ z, mem t z → mem z a → mem z E :=
  envelope hs hirr ht a ha

example (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V}
    (ht : ∀ z, ¬ mem z t) (U E : V) (hEt : E ≠ t) (htE : ¬ mem t E)
    (hUE : ∀ z, mem t z → mem z U → mem z E) (θ : Form) (ρ : Nat → V) :
    ∃ S, mem t S ∧ (∀ w, mem w S → w = E ∨ w = t ∨ mem w U) ∧
      ∀ z, mem t z → (mem z S ↔ mem z U ∧ Sat mem (scons z ρ) θ) :=
  dt_comp_env hs hirr ht U E hEt htE hUE θ ρ

example (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V}
    (ht : ∀ z, ¬ mem z t) (U : V) (θ : Form) (ρ : Nat → V) :
    ∃ S, mem t S ∧ ∀ z, mem t z → (mem z S ↔ mem z U ∧ Sat mem (scons z ρ) θ) :=
  dt_comp hs hirr ht U θ ρ

example (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V}
    (ht : ∀ z, ¬ mem z t) : KQHyp.QHyp (tmem mem t) := tag_qhyp hs hirr ht

#print axioms dt_comp
#print axioms dt_comp_env
#print axioms envelope
#print axioms tag_collection
#print axioms tag_qhyp
#print axioms zf_consistent_of_formSeed
end EnvelopeInterfaceAudit
