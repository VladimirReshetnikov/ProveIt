import GowersSzemeredi.Proofs16AdaptiveRelationIteration
import GowersSzemeredi.Proofs16ExplicitGraphCutoff

/-! Graph accuracy schedules determine both the bounded-relation tolerance
and the coefficient cutoff at each exact state of the density iteration. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def adaptiveGraphState (e : Nat → Real) (H m Q k : Nat) : Nat → Nat :=
  adaptiveRelationBudget (fun d => (e d)^4 / 6)
    (fun d => relationProfileCutoff ((e d)^4) H m) Q k

/-- A finite list of reachable states makes the ambient-size threshold
explicit even for a nonmonotone accuracy schedule. -/
def adaptiveGraphModulusBound (e : Nat → Real) (H m Q k d : Nat) : Nat :=
  (Finset.range (k + 1)).sup fun s =>
    ⌈1 / relationProfileSmoothing ((e ((adaptiveGraphState e H m Q k)^[s] d))^4) H m⌉₊

theorem adaptiveGraphModulusBound_spec (e : Nat → Real) (H m Q k d N s : Nat)
    (hs : s ≤ k) (hN : adaptiveGraphModulusBound e H m Q k d ≤ N) :
    1 / relationProfileSmoothing ((e ((adaptiveGraphState e H m Q k)^[s] d))^4) H m ≤ N := by
  apply (Nat.le_ceil _).trans
  exact_mod_cast (Finset.le_sup (f := fun j =>
    ⌈1 / relationProfileSmoothing ((e ((adaptiveGraphState e H m Q k)^[j] d))^4) H m⌉₊)
    (Finset.mem_range.mpr (by omega : s < k + 1))).trans hN

end LeanProofs.GowersSzemeredi
