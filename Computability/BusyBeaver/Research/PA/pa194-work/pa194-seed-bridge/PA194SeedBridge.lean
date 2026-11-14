import PA194SourceHalting
import PA194SourceProgram

/-! Conditional source/parent blank-start endpoint. Both the per-site coverage
and exact startup reachability remain explicit hypotheses. -/
set_option autoImplicit false
namespace PA194SeedBridge
open M6.Zip M6.Source PA194RuntimeEngine PA194PrimitiveSimulation PA194CompilerCorrectness
open PA194SourceHalting PA194SourceProgram

def blank : Conf := ⟨74, [], []⟩
def seedFile : List Nat := [0,0,0,0,0,0,2,0,0] ++ List.replicate 26 1
def seedFrame : Conf := frame (path 25) 0 seedFile

theorem seedFile_valid : 10 ≤ seedFile.length := by decide

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

/-- From the explicit complete coverage and startup hypotheses, the exact
parent halts from blank iff its formal source halts from the seeded store. -/
theorem parent_blank_iff_source
    (hcoverage : Coverage sites path 3673) (hstartup : Reach machine blank seedFrame) :
    Halts machine blank ↔ CycleHalts sites ⟨.at 25, readFile seedFile⟩ := by
  have hs := source_halts_iff_parent sites path 3673 hcoverage 25 0 seedFile (by decide) seedFile_valid
  constructor
  · intro hh
    exact hs.mpr (halt_after_reach hstartup hh)
  · intro hh
    exact Halts.of_reach hstartup (hs.mp hh)

#print axioms parent_blank_iff_source
end PA194SeedBridge
