import BusyBeaver.ZFC.KSeed222
import BusyBeaver.ZFC.KEind222

/-! Shared named seed syntax and semantic interface. Definitions are moved unchanged
from KSeedModel222 and KIndisc222 so the direct and optional quotient routes use
exactly the same public constants. -/

namespace SetTheory.BusyBeaver.ZFC.KSeed222
open Tarski Code254 KCode222 NF

/-- The bundle as a named formula with container `k` and matrix `m`. -/
def negNF (x : NF) : NF := imp x NF.bot

def reqNF (b k : Nat) (m : NF) : NF := all b (imp m (negNF (all b (imp m (negNF (rel b k))))))

def closNF (a b k : Nat) (m : NF) : NF :=
  all b (imp (rel b k) (negNF (all a (imp m (negNF (all a (imp (all k (imp (rel k a) (rel k b)))
    (reqNF b k m))))))))

def bundleNF (a b k : Nat) (m : NF) : NF :=
  negNF (imp (imp (rel a b) (all k (rel a b))) (all k (imp (closNF a b k m) (negNF (reqNF b k m)))))

theorem enc_bundleNF (a b : Nat) (m : NF) : enc (bundleNF a b (enc m) m) = bundle222 a b (enc m) := by
  simp only [bundleNF, closNF, reqNF, negNF, enc, bundle222, nks, clos, req, vrel, wn]

/-- Named formulas whose interpreted codes are derivable in the 222/221 calculus. -/
def DerivableNF (f : NF) : Prop := C222 (enc (KEind222.th f))

end SetTheory.BusyBeaver.ZFC.KSeed222

namespace SetTheory.BusyBeaver.ZFC.KIndisc222
open Tarski KSeed222
universe u
variable {V : Type u}

/-- The seed property for every named relation, with input name `0` and output name `1`. -/
structure FullSeed (mem : V → V → Prop) : Prop where
  irr : ∀ x, ¬ mem x x
  seed : ∀ (ψ : NF) (e : Nat → V),
    SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0)

end SetTheory.BusyBeaver.ZFC.KIndisc222
