import BusyBeaver.ZFC.RuntimePerm252
import BusyBeaver.ZFC.InstructionPrefix250
import BusyBeaver.ZFC.SiteCoverage

/-!
Whole-frame prefix250 runtime equivalence, conditional on exact site coverage.

Adapted from RuntimeInstancePerm252 and Mira-Cult, Jeff, and Wade's framework
as attributed there. The generic positive-segment proof is reused unchanged.
The relation retains the clean PC and entire dispatch frame and additionally
requires a nonempty finite physical spare suffix. The checked instruction
adapter preserves that resource: INC appends [1], and other operations retain
it. Positive decrement and PC overflow can increase the header distance.

A failed logical step is recognized as an actual halt leaf only using the
explicit coverage hypothesis. Both halting directions are proved by finite
induction through RuntimePerm252.PositiveSimulation. This module supplies no
closed all-sites theorem, no finite blank bootstrap and no consistency theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.RuntimeInstancePrefix250

open RegisterPath RegisterPathClean Permutation252Frame
open SymbolicPrefix250 SitePrefix250 Prefix250Simulation
open RuntimePerm252

def Covered (p : Program) : Prop :=
  ∀ P, ∃ e d, walk p (p.nnodes + 1) p.root P 0 = some (e, d) ∧
    checkSite (consume P d) e = true

theorem covered_of_allSites (p : Program) (t : RMBisim.Tree)
    (ht : RMBisim.ptree p = t) (hs : SiteCoverage.allSites checkSite [] t = true) :
    Covered p := by
  intro P
  obtain ⟨e, d, hw⟩ := SiteCoverage.allSites_walk_total checkSite p t ht hs P
  exact ⟨e, d, hw, SiteCoverage.allSites_walk checkSite p t ht hs P e d hw⟩

def Related (p : Program) (logical : Configuration) (binary : Config 250) : Prop :=
  Clean p logical.path ∧ ∃ gap spares, spares ≠ [] ∧
    DispatchFrame dispatch binary logical gap spares

theorem related_active (p : Program) (logical : Configuration) (binary : Config 250)
    (hc : Related p logical binary) : binary.state ≠ none := by
  rcases hc with ⟨_, gap, spares, _, _, _, lp, rp, hz⟩
  have hs : binary.state = some dispatch := hz.1
  rw [hs]
  simp

theorem clean_suffix (p : Program) (P : List Bool) (e : Edge) (d : Nat)
    (hc : Clean p P) (hw : walk p (p.nnodes + 1) p.root P 0 = some (e, d)) :
    ∀ b ∈ P.drop d, b = false := by
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  have hv : bit (P.drop d) i = b := by simp [bit, hi]
  exact hv.symm.trans ((bit_drop P d i).trans (hc e d hw (d + i) (by omega)))

theorem source_from_walk (p : Program) (logical : Configuration) (binary : Config 250)
    (gap : Nat) (spares : List Nat) (e : Edge) (d : Nat)
    (hclean : Clean p logical.path) (hframe : DispatchFrame dispatch binary logical gap spares)
    (hw : walk p (p.nnodes + 1) p.root logical.path 0 = some (e, d))
    (hcheck : checkSite (consume logical.path d) e = true) :
    Represents (logical.path.length + gap - 40) (vregs logical.registers ++ spares)
      (start (consume logical.path d)) binary := by
  apply source_represents logical binary gap spares (consume logical.path d) hframe
  · rw [consume_length]
  · simpa only [consume_length] using clean_suffix p logical.path e d hclean hw
  · exact checkSite_length _ _ hcheck

/-- A full logical step is implemented by a positive actual binary segment,
and the new logical state is clean regardless of its preceding path. -/
theorem related_step (p : Program) (hcov : Covered p)
    (logical next : Configuration) (binary : Config 250)
    (hc : Related p logical binary) (hs : RegisterPath.step p logical = some next) :
    ∃ k, 0 < k ∧ Related p next (machinePrefix250.runFrom binary k) := by
  rcases hc with ⟨hclean, gap, spares, hspares, hframe⟩
  obtain ⟨e, d, hw, hcheck⟩ := hcov logical.path
  have he : execute e (consume logical.path d) logical.registers = some next := by
    simpa only [RegisterPath.step, hw] using hs
  obtain ⟨k, hk, gap', spares', hspares', hf⟩ := InstructionPrefix250.execute_frame
    (consume logical.path d) e logical.registers spares
    (logical.path.length + gap - 40) binary next hcheck hframe.2.1 hspares
    (source_from_walk p logical binary gap spares e d hclean hframe hw hcheck) he
  exact ⟨k, hk, RegisterPathClean.step_clean p logical next hs, gap', spares', hspares', hf⟩

theorem stopped_terminal (p : Program) (hcov : Covered p) (logical : Configuration)
    (hs : RegisterPath.step p logical = none) : AtHalt p logical := by
  obtain ⟨e, d, hw, hcheck⟩ := hcov logical.path
  cases e with
  | node r => simp [checkSite, checkOperation] at hcheck
  | halt => exact ⟨d, hw⟩
  | inc r | brk r | cont r => simp [RegisterPath.step, hw, execute] at hs
  | decnz r => cases hv : logical.registers r <;> simp [RegisterPath.step, hw, execute, hv] at hs

theorem related_halt (p : Program) (hcov : Covered p)
    (logical : Configuration) (binary : Config 250)
    (hc : Related p logical binary) (hh : AtHalt p logical) : BinaryHalts machinePrefix250 binary := by
  rcases hc with ⟨hclean, gap, spares, hspares, hframe⟩
  obtain ⟨d, hw⟩ := hh
  obtain ⟨e, d', hw', hcheck⟩ := hcov logical.path
  rw [hw] at hw'
  cases hw'
  obtain ⟨k, _, hk⟩ := InstructionPrefix250.halt_frame (consume logical.path d)
    logical.registers spares (logical.path.length + gap - 40) binary hcheck hspares
    (source_from_walk p logical binary gap spares .halt d hclean hframe hw hcheck)
  exact ⟨k, hk⟩

theorem positive_simulation (p : Program) (hcov : Covered p) :
    PositiveSimulation machinePrefix250 (RegisterPath.step p) (AtHalt p) (Related p) where
  active := related_active p
  step := related_step p hcov
  stopped := fun logical _ _ hs => stopped_terminal p hcov logical hs
  halt := related_halt p hcov

theorem partialRun_eq_registerRun (p : Program) (N : Nat) (c : Configuration) :
    partialRun (RegisterPath.step p) N c = RegisterPath.run p N c := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih => cases hs : RegisterPath.step p c <;> simp [partialRun, RegisterPath.run, hs, ih]

theorem register_halts_iff_binary (p : Program) (hcov : Covered p)
    (logical : Configuration) (binary : Config 250) (hc : Related p logical binary) :
    RegisterPath.Halts p logical ↔ BinaryHalts machinePrefix250 binary := by
  simpa only [AbstractHalts, RegisterPath.Halts, partialRun_eq_registerRun] using
    RuntimePerm252.halts_iff (positive_simulation p hcov) logical binary hc

theorem allSites_halts_iff_binary (p : Program) (t : RMBisim.Tree)
    (ht : RMBisim.ptree p = t) (hs : SiteCoverage.allSites checkSite [] t = true)
    (logical : Configuration) (binary : Config 250) (hc : Related p logical binary) :
    RegisterPath.Halts p logical ↔ BinaryHalts machinePrefix250 binary :=
  register_halts_iff_binary p (covered_of_allSites p t ht hs) logical binary hc

end SetTheory.BusyBeaver.ZFC.RuntimeInstancePrefix250
