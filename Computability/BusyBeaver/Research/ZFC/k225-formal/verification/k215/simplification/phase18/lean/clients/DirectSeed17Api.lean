import BusyBeaver.ZFC.KSeedDirect222
import BusyBeaver.ZFC.KLowerSeed

namespace DirectSeed17Api

open SetTheory.BusyBeaver.ZFC
open KSeed222 KIndisc222

universe u
variable {V : Type u}

theorem original_domain (mem : V → V → Prop)
    (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) : FullSeed mem :=
  ⟨hirr, seed_direct mem hT⟩

theorem literal_equality_seed (mem : V → V → Prop)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (e : Nat → V) : SeedProp mem (fun x y => x = y) (e 0) := by
  simpa [Tarski.Sat, Tarski.update] using seed_direct mem hT (.eq 0 1) e

theorem formula_seed (mem : V → V → Prop)
    (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) : KLower.FormSeed mem :=
  KLower.formSeed_of_fullSeed (original_domain mem hirr hT)

#print axioms original_domain
#print axioms literal_equality_seed
#print axioms formula_seed

end DirectSeed17Api
