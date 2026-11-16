module
public import PA196.Coverage
public import PA196.ConjugacyReverse
public import PA196.Startup
@[expose] public section

/-! Literal tape/source equivalence for the supplied PA196 machine.

These are simulation theorems. Source nonhalting is an explicit hypothesis
here and is discharged separately using the new command calculus's soundness.
-/
namespace PA196.PhysicalEndpoint
open M6.Zip M6.Source

theorem halt_after_reach {M : TMN} {a b : Conf}
    (hr : Reach M a b) (hh : Halts M a) : Halts M b := by
  obtain ⟨n,hn⟩ := hr
  obtain ⟨z,⟨k,hk⟩,hz⟩ := hh
  by_cases hnk : n ≤ k
  · refine ⟨z,⟨k-n,?_⟩,hz⟩
    have he : k = n + (k-n) := by omega
    rw [he,run_add,hn] at hk
    exact hk
  · have he : n = k + (n-k) := by omega
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n-k ≠ 0)
    rw [he,run_add,hk,hm] at hn
    simp [M6.Zip.run,hz] at hn

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The actual startup has gap 48, the base of the reachable frame invariant. -/
theorem clean_frame : Conjugacy.mapConf Startup.clean =
    PrimitiveSimulation.frame (Program.path 25) 0 Startup.physicalFile := by decide +kernel

theorem initial_file_valid : 10 ≤ Startup.physicalFile.length := by decide

theorem blank_nonhalting_of_source
    (h : ¬ CycleHalts Program.sites ⟨.at 25,readFile Startup.physicalFile⟩) :
    ¬ Halts Literal.machine Startup.blank := by
  have hn := CompilerCorrectness.source_nonhalt_to_physical Program.sites Program.path 3812
    Coverage.complete 25 0 Startup.physicalFile (by decide) initial_file_valid h
  intro hh
  have hc := halt_after_reach Startup.startup_reach hh
  have hs := Conjugacy.halts_transport (c := Startup.clean) (by decide) hc
  rw [clean_frame] at hs
  exact hn hs

theorem source_halt_to_physical
    (sites : Array Site) (paths : Nat → Path) (count : Nat)
    (coverage : CompilerCorrectness.Coverage sites paths count)
    (i gap : Nat) (vs : List Nat) (hi : i < count) (hv : 10 ≤ vs.length)
    (hh : CycleHalts sites ⟨.at i,readFile vs⟩) :
    Halts Table.machine (PrimitiveSimulation.frame (paths i) gap vs) := by
  obtain ⟨steps,hs⟩ := hh
  induction steps generalizing i gap vs with
  | zero => cases hs
  | succ steps ih =>
    obtain ⟨code,hcode,himpl⟩ := coverage i hi
    have hstep : cycleStep sites ⟨.at i,readFile vs⟩ = restart (execute code (readFile vs)) := by
      simp only [cycleStep,M6.Source.step,hcode]
    simp only [cycleRun,hstep] at hs
    cases code with
    | halt => exact himpl gap vs hv
    | inc r next =>
      obtain ⟨j,gap',ws,hj,hw,he,hr⟩ := himpl gap vs hv
      rw [he] at hs
      exact Halts.of_reach hr.reach (ih j gap' ws hj hw hs)
    | dec r z next =>
      obtain ⟨j,gap',ws,hj,hw,he,hr⟩ := himpl gap vs hv
      rw [he] at hs
      exact Halts.of_reach hr.reach (ih j gap' ws hj hw hs)
    | jump next =>
      obtain ⟨j,gap',ws,hj,hw,he,hr⟩ := himpl gap vs hv
      rw [he] at hs
      exact Halts.of_reach hr.reach (ih j gap' ws hj hw hs)

theorem blank_halting_of_source
    (h : CycleHalts Program.sites ⟨.at 25,readFile Startup.physicalFile⟩) :
    Halts Literal.machine Startup.blank := by
  have hh := source_halt_to_physical Program.sites Program.path 3812 Coverage.complete
    25 0 Startup.physicalFile (by decide) initial_file_valid h
  rw [← clean_frame] at hh
  exact Halts.of_reach Startup.startup_reach
    (Conjugacy.halts_reflection (by decide) hh)

theorem blank_halting_iff_source :
    Halts Literal.machine Startup.blank ↔
      CycleHalts Program.sites ⟨.at 25,readFile Startup.physicalFile⟩ := by
  constructor
  · intro h
    exact Classical.byContradiction (fun hn => blank_nonhalting_of_source hn h)
  · exact blank_halting_of_source

#print axioms clean_frame
#print axioms blank_nonhalting_of_source
#print axioms source_halt_to_physical
#print axioms blank_halting_iff_source
end PA196.PhysicalEndpoint
