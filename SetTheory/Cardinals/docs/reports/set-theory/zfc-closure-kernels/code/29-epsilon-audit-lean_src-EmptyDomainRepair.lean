import BusyBeaver.ZFC.Code254

/-!
Correction for ProveIt commit d74c63b0c8d4f35597f1bd5976d941b9f104f94e.

The original c254_complete is logically true, but its "no model" hypothesis
is impossible because it also excludes the empty domain while the
satisfaction of every axiom is quantified over Nat → D environments.
This does not invalidate c254_sound or Tarski.alias_complete.

Use an explicit environment in the no-model premise. The existing
alias_complete proof already provides exactly such an environment.
-/

namespace SetTheory.BusyBeaver.ZFC.Code254

open SetTheory.BusyBeaver.ZFC.Tarski
open NF

/-- Exact empty-domain diagnosis for the original premise. -/
theorem original_c254_complete_premise_impossible :
    ¬ (∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ f, EncBundle f → ∀ e : Nat → D, Tarski.Sat mem e f) → False) := by
  intro hnone
  exact hnone Empty (fun _ _ => False) (fun _ hx => hx)
    (fun _ _ e => Empty.elim (e 0))

/-- The corrected no-nonempty-model version, using a pointed domain. -/
theorem c254_complete_pointed
    (hnone : ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ f, EncBundle f → ∀ e : Nat → D, Tarski.Sat mem e f) →
      (Nat → D) → False) :
    C254 F := by
  have hT : ThmG (rel 0 0) EncBundle (rel 0 0) := by
    apply alias_complete (f := rel 0 0) (fun f hf => hf.1) trivial
    intro D mem hirr hAx e
    exact (hnone D mem hirr hAx e).elim
  have := c254_of_thmG (fun f hf => by
    obtain ⟨_, a, b, c, h1, h2, he⟩ := hf
    rw [he]; exact C254.bundle a b c h1 h2) hT
  simpa [enc, wel_zero_zero] using this

/-- The same correction with nonemptiness exposed as an explicit premise. -/
theorem c254_complete_nonempty
    (hnone : ∀ (D : Type), Nonempty D →
      ∀ (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ f, EncBundle f → ∀ e : Nat → D, Tarski.Sat mem e f) → False) :
    C254 F := by
  apply c254_complete_pointed
  intro D mem hirr hAx e
  exact hnone D ⟨e 0⟩ mem hirr hAx

#print axioms original_c254_complete_premise_impossible
#print axioms c254_complete_pointed
#print axioms c254_complete_nonempty

end SetTheory.BusyBeaver.ZFC.Code254

