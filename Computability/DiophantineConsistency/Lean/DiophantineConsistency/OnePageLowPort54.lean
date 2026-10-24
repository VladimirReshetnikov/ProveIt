import DiophantineConsistency.NativeLowPort54

/-! # The one-page support and exact symbolic compact54 low port -/

namespace DiophantineConsistency.OnePageTuple54

open NativeStencil54
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The exact same fixed assignment support, written as short intervals. -/
def assignmentPositions : List ℕ :=
  List.range 457 ++ ((List.range 11).map (539+·)) ++ ((List.range 10).map (528+·)) ++
  ((List.range 11).map (517+·)) ++ ((List.range 10).map (495+·)) ++
  ((List.range 8).map (567+·)) ++ ((List.range 8).map (575+·)) ++
  [583,1203,1807,507,508]

theorem assignmentPositions_eq : assignmentPositions = entries.map Prod.fst := by rfl

private def sortedPositions : List ℕ :=
  List.range 457 ++ ((List.range 10).map (495+·)) ++ [507,508] ++
  ((List.range 11).map (517+·)) ++ ((List.range 10).map (528+·)) ++
  ((List.range 11).map (539+·)) ++ ((List.range 8).map (567+·)) ++
  ((List.range 8).map (575+·)) ++ [583,1203,1807]

private theorem positions_perm : assignmentPositions.Perm sortedPositions := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [assignmentPositions,sortedPositions,List.count_append,List.count_cons,List.count_nil]
  omega

private theorem sortedPositions_chain : sortedPositions.IsChain (· < ·) := by decide

theorem assignmentPositions_nodup : assignmentPositions.Nodup :=
  positions_perm.nodup_iff.mpr (List.isChain_iff_pairwise.mp sortedPositions_chain).nodup

attribute [local irreducible] radix Nat.pow

def lowPort (ρ : ℕ) : ℕ := ρ^4831-1-
  (((assignmentPositions.filter (fun e => e != 1)).map fun e => ρ^e).sum)-2*ρ^507

private theorem lowPort_formula (ρ : ℕ) : lowPort ρ = ρ^4831-1-
    (((entries.map Prod.fst).filter (fun e => e != 1)).map (fun e => ρ^e)).sum-2*ρ^507 := by
  unfold lowPort
  rw [assignmentPositions_eq]

/-- Exact MC subtraction identity, without evaluating the huge radix power. -/
theorem lowPort_eq : lowPort radix = NativeLowPort54.lowPort := by
  rw [lowPort_formula]
  have h (ρ : ℕ) : ρ^4831-1-
      (((entries.map Prod.fst).filter (fun e => e != 1)).map (fun e => ρ^e)).sum-2*ρ^507 =
      ρ^4831-1-((((entries.map Prod.fst).filter (fun e => e != 1)).map (fun e => ρ^e)).sum+2*ρ^507) := by
    rw [Nat.sub_sub]
  exact h radix

end DiophantineConsistency.OnePageTuple54
