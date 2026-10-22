import BusyBeaver.ZFC.KIndisc222

/-! Compatibility client: old quotient, equality-free, and shared syntax APIs survive. -/
namespace SetTheory.BusyBeaver.ZFC.AuditSeedLegacy222
open Tarski KSeed222 Code254

example {V : Type} (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) :
    KIndisc222.FullSeed (KIndisc222.qmem mem) :=
  KIndisc222.fullSeed_of_derivable mem hirr hT

example {V : Type} (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (ψ : NF) (hψ : KThmK.EqFree ψ) (e : Nat → V) :
    SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0) :=
  seed_eqFree mem hirr hT ψ hψ e

example (a b : Nat) (m : NF) : enc (bundleNF a b (enc m) m) = KCode222.bundle222 a b (enc m) :=
  enc_bundleNF a b m

#print axioms KSeed222.seed_eqFree
#print axioms KIndisc222.fullSeed_of_derivable

end SetTheory.BusyBeaver.ZFC.AuditSeedLegacy222
