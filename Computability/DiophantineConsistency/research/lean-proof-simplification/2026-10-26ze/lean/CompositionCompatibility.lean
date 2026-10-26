import DiophantineConsistency.DirectComposition
namespace DiophantineConsistency.Rep
variable {σ : Type*}
/-- Substitute a finite family of represented functions into a predicate.
The polynomial data use only the supplied representations. -/
def oldCompose {n : ℕ} {P : (Fin n → ℕ) → Prop}
    {f : Fin n → (σ → ℕ) → ℕ}
    (r : Rep (Fin n) P) (g : ∀ i, GraphRep (f i)) :
    Rep σ (fun v => P (fun i => f i v)) := by
  let index (i : Fin n) : Option σ → σ ⊕ Fin n
    | none => .inr i
    | some j => .inl j
  let rows := allFin n
    (fun i v => v (.inr i) = f i (v ∘ Sum.inl))
    (fun i => Rep.reindex (g i) (index i))
  let joined := ((r.reindex Sum.inr).conjunction rows).existsBlock
  refine joined.ofIff ?_
  intro v
  change (∃ a : Fin n → ℕ, P a ∧ ∀ i, a i = f i v) ↔ P (fun i => f i v)
  constructor
  · rintro ⟨a, ha, hg⟩
    have he : a = fun i => f i v := funext hg
    simpa only [he] using ha
  · intro h
    exact ⟨fun i => f i v, h, fun i => rfl⟩

theorem compose_preserves_full_record {n : ℕ} {P : (Fin n → ℕ) → Prop}
    {f : Fin n → (σ → ℕ) → ℕ} (r : Rep (Fin n) P) (g : ∀ i, GraphRep (f i)) :
    oldCompose r g = compose r g := rfl
end DiophantineConsistency.Rep
namespace DiophantineConsistency.GraphRep
variable {σ : Type*} {n : ℕ} {f : (Fin n → ℕ) → ℕ}
  {g : Fin n → (σ → ℕ) → ℕ}
/-- Substitute the supplied graph inputs while retaining the original output
coordinate. Exactly the `n` input values become new existential witnesses. -/
def oldComposeDirect (r : GraphRep f) (s : ∀ i, GraphRep (g i)) :
    GraphRep (fun v => f (fun i => g i v)) := by
  let index : Option (Fin n) → Option σ ⊕ Fin n
    | none => .inl none
    | some i => .inr i
  let slot (i : Fin n) : Option σ → Option σ ⊕ Fin n
    | none => .inr i
    | some j => .inl (some j)
  let rows := Rep.allFin n
    (fun i (v : Option σ ⊕ Fin n → ℕ) => v (.inr i) = g i (fun j => v (.inl (some j))))
    (fun i => Rep.reindex (s i) (slot i))
  refine (((Rep.reindex r index).conjunction rows).existsBlock).ofIff ?_
  intro v
  change (∃ a : Fin n → ℕ, v none = f a ∧
    ∀ i, a i = g i (v ∘ some)) ↔ v none = f (fun i => g i (v ∘ some))
  constructor
  · rintro ⟨a, ha, hg⟩
    have he : a = fun i => g i (v ∘ some) := funext hg
    simpa only [he] using ha
  · intro h
    exact ⟨fun i => g i (v ∘ some), h, fun _ => rfl⟩

theorem composeDirect_preserves_full_record (r : GraphRep f) (s : ∀ i, GraphRep (g i)) :
    oldComposeDirect r s = composeDirect r s := rfl
end DiophantineConsistency.GraphRep
#print axioms DiophantineConsistency.Rep.compose_preserves_full_record
#print axioms DiophantineConsistency.GraphRep.composeDirect_preserves_full_record
#print axioms DiophantineConsistency.Rep.oldCompose
#print axioms DiophantineConsistency.Rep.compose
#print axioms DiophantineConsistency.GraphRep.oldComposeDirect
#print axioms DiophantineConsistency.GraphRep.composeDirect
