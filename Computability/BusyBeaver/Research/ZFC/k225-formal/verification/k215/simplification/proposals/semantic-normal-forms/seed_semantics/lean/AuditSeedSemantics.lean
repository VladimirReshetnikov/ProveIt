import BusyBeaver.ZFC.KSeedModel222

namespace K215SeedApiAudit
open SetTheory.BusyBeaver.ZFC
open Tarski Code254 KCode222 KSeed222
universe u
variable {V : Type u}

example (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b)
    (h : SeedProp mem (matrixRel mem e a b c) (e a)) :
    Tarski.Sat mem e (dec (bundle222 a b c)) :=
  bundle_of_seed mem hirr e a b c hca hcb h

example (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (a b c : Nat) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (h : Tarski.Sat mem e (dec (bundle222 a b c))) :
    SeedProp mem (matrixRel mem e a b c) (e a) :=
  seed_of_bundle mem hirr e a b c hab hca hcb h

example (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (ψ : NF) (hψ : KThmK.EqFree ψ) (e : Nat → V) :
    SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0) :=
  seed_eqFree mem hirr hT ψ hψ e

#print axioms BundleSemantics.bundle_iff_seed
#print axioms bundle_of_seed
#print axioms seed_of_bundle
#print axioms seed_eqFree
end K215SeedApiAudit
