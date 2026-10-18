import BusyBeaver.ZFC.RuntimeInstanceRouting245

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open Routing245Simulation
open RegisterPath RegisterPathClean Permutation252Frame
open SymbolicRouting245 SiteRouting245 RuntimePerm252 RuntimeInstanceRouting245

#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.covered_of_allSites
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.related_active
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.clean_suffix
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.source_from_walk
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.related_step
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.stopped_terminal
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.related_halt
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.positive_simulation
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.partialRun_eq_registerRun
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.register_halts_iff_binary
#print axioms SetTheory.BusyBeaver.ZFC.RuntimeInstanceRouting245.allSites_halts_iff_binary

example (p : Program) (t : RMBisim.Tree) (ht : RMBisim.ptree p = t)
    (hs : SiteCoverage.allSites checkSite [] t = true) : Covered p := covered_of_allSites p t ht hs

example (p : Program) (a : Configuration) (c : Config 245) (h : Related p a c) :
    c.state ≠ none := related_active p a c h

example (p : Program) (P : List Bool) (e : Edge) (d : Nat)
    (hc : Clean p P) (hw : walk p (p.nnodes + 1) p.root P 0 = some (e, d)) :
    ∀ b ∈ P.drop d, b = false := clean_suffix p P e d hc hw

example (p : Program) (logical : Configuration) (binary : Config 245)
    (gap : Nat) (spares : List Nat) (e : Edge) (d : Nat)
    (hclean : Clean p logical.path) (hframe : DispatchFrame64 dispatch binary logical gap spares)
    (hw : walk p (p.nnodes + 1) p.root logical.path 0 = some (e, d))
    (hc : checkSite (consume logical.path d) e = true) :
    Represents (logical.path.length + gap - 64) (vregs logical.registers ++ spares)
      (start (consume logical.path d)) binary :=
  source_from_walk p logical binary gap spares e d hclean hframe hw hc

example (p : Program) (hcov : Covered p) (a b : Configuration) (c : Config 245)
    (hc : Related p a c) (hs : RegisterPath.step p a = some b) :
    ∃ k, 0 < k ∧ Related p b (machineRouting245.runFrom c k) := related_step p hcov a b c hc hs

example (p : Program) (hcov : Covered p) (a : Configuration)
    (hs : RegisterPath.step p a = none) : AtHalt p a := stopped_terminal p hcov a hs

example (p : Program) (hcov : Covered p) (a : Configuration) (c : Config 245)
    (hc : Related p a c) (hh : AtHalt p a) : BinaryHalts machineRouting245 c :=
  related_halt p hcov a c hc hh

example (p : Program) (hcov : Covered p) :
    PositiveSimulation machineRouting245 (RegisterPath.step p) (AtHalt p) (Related p) :=
  positive_simulation p hcov

example (p : Program) (N : Nat) (c : Configuration) :
    partialRun (RegisterPath.step p) N c = RegisterPath.run p N c := partialRun_eq_registerRun p N c

example (p : Program) (hcov : Covered p) (a : Configuration) (c : Config 245)
    (hc : Related p a c) : RegisterPath.Halts p a ↔ BinaryHalts machineRouting245 c :=
  register_halts_iff_binary p hcov a c hc

example (p : Program) (t : RMBisim.Tree) (ht : RMBisim.ptree p = t)
    (hs : SiteCoverage.allSites checkSite [] t = true) (a : Configuration) (c : Config 245)
    (hc : Related p a c) : RegisterPath.Halts p a ↔ BinaryHalts machineRouting245 c :=
  allSites_halts_iff_binary p t ht hs a c hc

example (p : Program) (N : Nat) (a b : Configuration) (c : Config 245)
    (hcov : Covered p) (hc : Related p a c) (hr : RegisterPath.run p N a = some b) :
    ∃ k, N ≤ k ∧ Related p b (machineRouting245.runFrom c k) := by
  apply RuntimePerm252.prefix_run (positive_simulation p hcov) N a b c hc
  simpa only [partialRun_eq_registerRun] using hr
