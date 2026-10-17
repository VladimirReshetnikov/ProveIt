/-!
An empty-domain audit independent of ProveIt.

The bad premise has exactly the quantifier shape of Code254.c254_complete
at ProveIt commit d74c63b0c8d4f35597f1bd5976d941b9f104f94e.
No facts about formula syntax or satisfaction are needed: Empty is enough.
The model-theoretic conventions must carry a domain inhabitant or an
environment when asserting that no model exists.

Standalone, core Lean 4 only. The companion EmptyDomainRepair.lean uses
the actual ProveIt definitions and gives the repaired completeness theorem.
-/

namespace Code254EmptyDomainAudit

abbrev Satisfaction (Formula : Type) :=
  (D : Type) → (D → D → Prop) → (Nat → D) → Formula → Prop

def BadNoModel (Formula : Type) (Ax : Formula → Prop)
    (Sat : Satisfaction Formula) : Prop :=
  ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
    (∀ f, Ax f → ∀ e : Nat → D, Sat D mem e f) → False

/-- The uninhabited domain makes this premise impossible for every theory. -/
theorem badNoModel_is_false (Formula : Type) (Ax : Formula → Prop)
    (Sat : Satisfaction Formula) : ¬ BadNoModel Formula Ax Sat := by
  intro h
  exact h Empty (fun _ _ => False) (fun _ hx => hx)
    (fun _ _ e => Empty.elim (e 0))

def PointedNoModel (Formula : Type) (Ax : Formula → Prop)
    (Sat : Satisfaction Formula) : Prop :=
  ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
    (∀ f, Ax f → ∀ e : Nat → D, Sat D mem e f) →
    (Nat → D) → False

def NonemptyNoModel (Formula : Type) (Ax : Formula → Prop)
    (Sat : Satisfaction Formula) : Prop :=
  ∀ (D : Type), Nonempty D → ∀ (mem : D → D → Prop),
    (∀ x, ¬ mem x x) →
    (∀ f, Ax f → ∀ e : Nat → D, Sat D mem e f) → False

/-- Carrying an environment and explicitly requiring nonemptiness agree. -/
theorem pointed_iff_nonempty (Formula : Type) (Ax : Formula → Prop)
    (Sat : Satisfaction Formula) :
    PointedNoModel Formula Ax Sat ↔ NonemptyNoModel Formula Ax Sat := by
  constructor
  · intro h D hD mem hirr hAx
    cases hD with
    | intro d => exact h D mem hirr hAx (fun _ => d)
  · intro h D mem hirr hAx e
    exact h D ⟨e 0⟩ mem hirr hAx

#print axioms badNoModel_is_false
#print axioms pointed_iff_nonempty

end Code254EmptyDomainAudit

