module
public import M6.Legacy213.SourceProgram
@[expose] public section
namespace M6.Legacy213.PathBounds
open M6.Source M6.Legacy213.SourceProgram
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem all_short : sites.toList.all (fun s => decide (s.path.length ≤ 64)) = true := by decide +kernel

theorem path_short (i : Nat) : (path i).length ≤ 64 := by
  unfold path
  cases hs : sites[i]? with
  | none => simp [hs]
  | some s =>
    have hm : s ∈ sites.toList := by
      have h : sites.toList[i]? = some s := by simpa using hs
      exact List.mem_of_getElem? h
    have hh := List.all_eq_true.mp all_short s hm
    simpa [hs] using hh
end M6.Legacy213.PathBounds
