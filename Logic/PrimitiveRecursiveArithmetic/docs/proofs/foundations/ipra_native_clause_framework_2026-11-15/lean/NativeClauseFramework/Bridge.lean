import ConciseIPRA.NativeClausalDiagonal
import ConciseIPRA.NativeBiInterpretation

/-!
# Native-clause / ordinary-iPRA exchange

Candidate integration code for the framework report.  It is written against the
API present in ProveIt commit 8649990597d73657bde480b6c389de7f85bc0cb0.

This file contains no `sorry`, but it was not compiled in the artifact runtime:
no Lean executable was installed there.  Treat it as candidate source until it
is checked in the pinned ProveIt workspace.
-/

namespace LeanProofs.IPRA.NativeClauseFramework

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n : ℕ}
variable {Γ : List (Cl n)} {Δ : List (NFm n)} {A B : NFm n}

/-- Discharge a finite list of ordinary native assumptions by `KPrf.cut`. -/
theorem cutAsmList
    (h : KPrf (Δ.map Cl.asm ++ Γ) A)
    (hs : ∀ X ∈ Δ, KPrf Γ X) : KPrf Γ A := by
  apply h.cut
  intro c hc
  rw [List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hc
    exact .inr ⟨X, rfl, hs X hX⟩
  · exact .inl hc

/-- The one-generated-assumption specialization of `cutAsmList`. -/
theorem cutOne (hB : KPrf Γ B) (hA : KPrf (Cl.asm B :: Γ) A) : KPrf Γ A := by
  apply hA.cut
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact .inr ⟨B, rfl, hB⟩
  · exact .inl hc

/-- Export a clause derivation to the ordinary `Prf PRAAx` reading. -/
theorem exportPRA (h : KPrf Γ A) :
    (Γ.map fun c => c.toN.toPRA) ⊢[PRAAx] A.toPRA := by
  simpa only [List.map_map, Function.comp_apply] using
    (native_iff_pra.mp h.toNPrf)

/-- A closed clause derivation exports to a closed theorem of ordinary iPRA. -/
theorem exportClosed {A : NFm 0} (h : KPrf ([] : List (Cl 0)) A) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] A.toPRA := by
  simpa using exportPRA h

/-- Import an ordinary iPRA derivation as a Q-free native-clause derivation. -/
theorem importPRA {ΓP : List (Fm PTm n)} {φ : Fm PTm n}
    (h : ΓP ⊢[PRAAx] φ) :
    KPrf ((ΓP.map NFm.ofPRA).map fun X => Cl.asm (NFm.unQ X))
      (NFm.unQ (NFm.ofPRA φ)) := by
  exact kprf_iff_nprf.mpr (pra_iff_native.mp h)

end LeanProofs.IPRA.NativeClauseFramework
