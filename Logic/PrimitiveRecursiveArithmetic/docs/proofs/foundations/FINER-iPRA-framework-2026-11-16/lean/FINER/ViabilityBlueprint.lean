import FINER.TraceBlueprint
import IPRADerivations.Core.Search

/-!
# Backward viability and least successful replay

The implementation packs the finite viability table into a natural number,
checks the backward equations, and replays the least viable successor using the
checked `Core.Search` backend.  This file is a blueprint, not a compiled claim.
-/

namespace LeanProofs.IPRA.FINER

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

structure FiniteRelationalRun where
  horizon : ℕ
  stateBound : ℕ → ℕ
  edge : ℕ → PR 2
  accept : PR 1
  initial : ℕ
  viabilitySoundnessSentence : Fm PTm 0
  initialViableSentence : Fm PTm 0
  initialNotViableSentence : Fm PTm 0
  pathCertificateSentence : Fm PTm 0
  noPathSentence : Fm PTm 0

/-- The generated backward table agrees with existence of a bounded accepted
path from every table entry. -/
theorem viability_table_sound (R : FiniteRelationalRun) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] R.viabilitySoundnessSentence := by
  sorry

/-- Initial viability yields a canonical least successful transcript. -/
theorem least_viable_path (R : FiniteRelationalRun) :
    [R.initialViableSentence] ⊢[PRAAx] R.pathCertificateSentence := by
  -- Forward quantifier-free induction; each successor comes from
  -- `Search.search_found` applied to edge-and-next-viability.
  sorry

/-- Viability zero is finite evidence that no accepted path exists. -/
theorem no_path_of_not_viable (R : FiniteRelationalRun) :
    [R.initialNotViableSentence] ⊢[PRAAx] R.noPathSentence := by
  sorry

end LeanProofs.IPRA.FINER
