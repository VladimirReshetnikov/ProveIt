import BusyBeaver.ZFC.ArithmeticDagRun

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticDagRun

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDagRun.occ_of_occB
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDagRun.run_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDagRun.run_iterate

example (p : RMDag.Prog) (rows : Nat → Option ArithmeticControlBisim.Row)
    (f : Nat) (e : RMDag.Edge) (c : Nat) (E : RMDag.Exit → Nat)
    (h : occB p rows f e c E = true) : Occ p rows f e c E :=
  occ_of_occB p rows f e c E h

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {p : RMDag.Prog} {rows : Nat → Option ArithmeticControlBisim.Row}
  {step : V → V} {run : V → V → V}

example (run_one : ∀ x, run 1 x = step x)
    (spec : ∀ c row x, rows c = some row → step (ArithmeticControlFile.liveValue (c : V) x) =
      ArithmeticControlBisim.sem ArithmeticControlFile.regValue ArithmeticControlTable.write
        ArithmeticControlFile.liveValue row x) (r : Nat) (x : V) :
    IRun p rows run (.inc r) x .normal (lupd x r (lreg x r + 1)) :=
  run_inc run_one spec r x

example [𝚺₁-Function₂[V] run] (hz : ∀ x, run 0 x = x)
    (ha : ∀ t u x, run (t+u) x = run u (run t x))
    {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a,b))
    (G H : V → V) [𝚺₁-Function₁[V] G] (N : V)
    (hp : ∀ t, t < N → IRun p rows run a (G t) .normal (H t) ∧
      IRun p rows run b (H t) (.cont 1) (G (t+1)))
    {X : RMDag.Exit} {y : V} (hf : IRun p rows run (.node n) (G N) X y) :
    IRun p rows run (.node n) (G 0) X y :=
  run_iterate (run_zero := hz) (run_add := ha) hn G H N hp hf
