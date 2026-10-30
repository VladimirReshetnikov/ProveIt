import BusyBeaver.ZFC.CompositionModel
import BusyBeaver.ZFC.ProfileAxioms

/-!
The interface of the bisimulation quotient for the 221's lower chain.

A CP/GIC model has literal power containers, which the tagged domain of Elliot Glazer's K lacks.
`QHyp mem` lists exactly what the quotient's ZF proof uses, at the level of interpreted
membership `Member` and coded bisimilarity `Eqv`: equality-free collection, the equivalence laws
and extensionality of `Eqv`, profile pairs, and interpreted union, power and singleton-closed
containers. The `KQ1*` modules build the quotient on this interface; a CP/GIC model supplies it
through `QuotientModel.ofCPGIC`.
-/

namespace SetTheory.BusyBeaver.ZFC.KQHyp

open Profile ProfilePairs ProfileCollection ProfileComposition ProfileAxioms ProfileModel

universe u
variable {V : Type u}

structure QHyp (mem : V → V → Prop) : Prop where
  gic : ModelsGIC mem
  refl : ∀ x, Eqv mem x x
  symm : ∀ {x y : V}, Eqv mem x y → Eqv mem y x
  trans : ∀ {x y z : V}, Eqv mem x y → Eqv mem y z → Eqv mem x z
  ext : ∀ x y, (∀ z, Member mem z x ↔ Member mem z y) → Eqv mem x y
  pairs : ∀ a b, ∃ p, Pair mem p a b
  union : ∀ a, ∃ b, ∀ z, Member mem z b ↔ ∃ x, Member mem x a ∧ Member mem z x
  power : ∀ a, ∃ p, ∀ x, Member mem x p ↔ InterpretedSub mem x a
  singleton : ∀ root, ∃ v, Member mem root v ∧ ∀ x, Member mem x v →
    ∃ s, Member mem s v ∧ ∀ z, Member mem z s ↔ Eqv mem z x

end SetTheory.BusyBeaver.ZFC.KQHyp
