/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeBinaryAssignments

namespace OAI

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ] {n : ℕ}

theorem finiteChoiceLeafInput_of_not_mem (l : List σ) :
    ∀ (v : Fin l.length → Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) (j : σ),
      j ∉ l → finiteChoiceLeafInput l v x j = x (0, j) := by
  induction l with
  | nil => intro v x j _; rfl
  | cons i l ih =>
      intro v x j hj
      simp only [List.mem_cons, not_or] at hj
      rw [finiteChoiceLeafInput, ih (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) j hj.2]
      simp [finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hj.1]

theorem finiteChoiceLeafInput_get (l : List σ) :
    l.Nodup → ∀ (v : Fin l.length → Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ)
      (j : Fin l.length), finiteChoiceLeafInput l v x (l.get j) = x (v j, l.get j) := by
  induction l with
  | nil => intro _ v x j; exact Fin.elim0 j
  | cons i l ih =>
      intro hl v x j
      obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
      refine Fin.cases ?_ (fun k => ?_) j
      · change finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) i =
          x (v 0, i)
        rw [finiteChoiceLeafInput_of_not_mem l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) i hi]
        simp [finiteChoiceReplaceInput, finiteChoiceReplaceIndex]
      · change finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) (l.get k) =
          x (v k.succ, l.get k)
        rw [ih hl (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) k]
        have hki : l.get k ≠ i := by
          intro heq
          apply hi
          rw [← heq]
          exact List.get_mem l k
        change x (if (v k.succ, l.get k) = (0, i) then (v 0, i) else (v k.succ, l.get k)) = _
        rw [ite_eq_right (fun h => hki (congrArg Prod.snd h))]

end Erdos3

end

end OAI
