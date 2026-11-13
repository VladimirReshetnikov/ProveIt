module
public import M6.Coverage
public import M6.Conjugacy
public import M6.Startup
public import M6.Bounds
public import M6.PaperCorrection
public import M6.SourceTransport
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.PhysicalEndpoint
open M6.Zip

/-- Determinism transports any alleged halt past a checked finite prefix. -/
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

/-- The real26-spare startup zipper is exactly the canonical source-A frame. -/
theorem clean_frame : Conjugacy.mapConf Startup.clean =
    PrimitiveSimulation.frame (Program.path 25) 10 Startup.physicalFile := by decide +kernel

/-- A physical-source compiler endpoint only. The source nonhalting hypothesis
    is explicit; this theorem does not yet discharge it from ordinary PA consistency. -/
theorem blank_nonhalting_of_source
    (h : ¬ Source.CycleHalts Program.sites
      ⟨.at 25,Source.readFile Startup.physicalFile⟩) :
    ¬ Halts Literal.machine Startup.blank := by
  have hn := CompilerCorrectness.source_nonhalt_to_physical Program.sites Program.path 3948
    Coverage.complete 25 10 Startup.physicalFile (by decide)
    PaperCorrection.corrected_file_valid h
  intro hh
  have hc := halt_after_reach Startup.startup_reach hh
  have hs := Conjugacy.halts_transport (c := Startup.clean) (by decide) hc
  rw [clean_frame] at hs
  exact hn hs

/-- The new physical machine reduces to the original source from the actual
zeroed command store at candidate2. Ordinary PA consistency is not substituted
for this explicitly stated hypothesis. -/
theorem blank_nonhalting_of_original_source
    (h : ¬ Source.CycleHalts SourceCrosswalk.originalSites
      ⟨.at 0,Source.readFile Startup.physicalFile⟩) :
    ¬ Halts Literal.machine Startup.blank :=
  blank_nonhalting_of_source (SourceTransport.nonhalting_from_A _ h)

#print axioms blank_nonhalting_of_original_source
#print axioms clean_frame
#print axioms blank_nonhalting_of_source
end M6.PhysicalEndpoint
