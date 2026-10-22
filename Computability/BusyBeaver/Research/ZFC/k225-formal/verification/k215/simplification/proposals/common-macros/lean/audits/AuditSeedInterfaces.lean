import BusyBeaver.ZFC.KLowerQHyp

namespace SeedInterfaceAudit

open SetTheory SetTheory.Form
open SetTheory.BusyBeaver.ZFC SetTheory.BusyBeaver.ZFC.KLower
open SetTheory.BusyBeaver.ZFC.KSeed222

universe u
variable {V : Type u} {mem : V → V → Prop}

example (hs : FormSeed mem) (w : V) : ∃ t, ∀ z, ¬ mem z t := raw_empty hs w

example (hs : FormSeed mem) (x : V) : ∃ s, IsSing mem s x := raw_singleton hs x

example (hs : FormSeed mem) {t : V} (ht : ∀ z, ¬ mem z t) (x y : V) :
    ∃ p, ∀ z, mem z p ↔ z = x ∨ z = y := raw_pair hs ht x y

example (hs : FormSeed mem) (a : V) :
    ∃ v, mem a v ∧ ∀ y, mem y v → ∀ z, mem z y → mem z v := raw_transitive hs a

example (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) (a : V) :
    ∃ p, ∀ z, mem z p ↔ ∀ w, mem w z → mem w a := raw_power hs hirr a

-- The old explicit irreflexivity parameter remains accepted.
example (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) (a : V) (θ : Form) (ρ : Nat → V) :
    ∃ b, ∀ z, mem z b ↔ z = a ∨ (mem z a ∧ Sat mem (scons z ρ) θ) :=
  raw_aug hs hirr a θ ρ

-- The strengthened theorem also works without that parameter.
example (hs : FormSeed mem) (a : V) (θ : Form) (ρ : Nat → V) :
    ∃ b, ∀ z, mem z b ↔ z = a ∨ (mem z a ∧ Sat mem (scons z ρ) θ) :=
  raw_aug_core hs a θ ρ

example (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V}
    (ht : ∀ z, ¬ mem z t) (B : V) (hBt : B ≠ t) (θ : Form) (ρ : Nat → V) :
    ∃ S, ∀ z, mem z S ↔ z = B ∨ z = t ∨ (mem z B ∧ Sat mem (scons z ρ) θ) :=
  raw_tagged hs hirr ht B hBt θ ρ

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

#print axioms seedProp_iff_closure
#print axioms raw_singleton
#print axioms raw_pair
#print axioms raw_transitive
#print axioms raw_power
#print axioms raw_aug_core
#print axioms raw_aug
#print axioms raw_tagged
#print axioms dt_comp
#print axioms envelope
#print axioms tag_qhyp
#print axioms zf_consistent_of_formSeed

end SeedInterfaceAudit
