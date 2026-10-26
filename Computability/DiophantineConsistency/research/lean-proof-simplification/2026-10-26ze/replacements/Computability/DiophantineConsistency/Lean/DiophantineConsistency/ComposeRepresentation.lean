import DiophantineConsistency.ArithmeticRepresentation

/-!
# Finite composition of explicit Diophantine representations

The constructor keeps the values of substituted functions as a finite
existential block and constrains them with their supplied graph data.
-/

namespace DiophantineConsistency.Rep

variable {σ : Type*}

/-- A finite conjunction of supplied representations, constructed by recursion. -/
def allFin (n : ℕ) :
    ∀ P : Fin n → (σ → ℕ) → Prop,
      (∀ i, Rep σ (P i)) → Rep σ (fun v => ∀ i, P i v) := by
  induction n with
  | zero =>
      intro P rs
      exact (Rep.equality (0 : Expr σ) 0).ofIff (fun v => by simp)
  | succ n ih =>
      intro P rs
      exact ((rs 0).conjunction (ih (fun i => P i.succ) (fun i => rs i.succ))).ofIff
        (fun v => (Fin.forall_fin_succ (P := fun i => P i v)).symm)

/-- Substitute a finite family of represented functions into a predicate.
The polynomial data use only the supplied representations. -/
def compose {n : ℕ} {P : (Fin n → ℕ) → Prop}
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
  simp only [← funext_iff, exists_eq_right]

end DiophantineConsistency.Rep

namespace DiophantineConsistency.GraphRep

variable {σ : Type*}

/-- Compose an explicitly represented function with a finite family of
explicitly represented arguments. -/
def compose {n : ℕ} {f : (Fin n → ℕ) → ℕ}
    {g : Fin n → (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : ∀ i, GraphRep (g i)) :
    GraphRep (fun v => f (fun i => g i v)) := by
  let index : Option (Fin n) → Fin (n + 1)
    | none => 0
    | some i => i.succ
  let inputs (j : Fin (n + 1)) (v : Option σ → ℕ) : ℕ :=
    Fin.cases (v none) (fun i => g i (v ∘ some)) j
  let arguments : ∀ j : Fin (n + 1), GraphRep (inputs j) :=
    Fin.cases (GraphRep.coordinate none) (fun i => (s i).reindex some)
  exact (Rep.compose (Rep.reindex r index) arguments).ofIff (fun v => Iff.rfl)

end DiophantineConsistency.GraphRep
