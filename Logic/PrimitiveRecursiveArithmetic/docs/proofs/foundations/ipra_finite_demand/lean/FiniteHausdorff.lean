import Std

/-!
# Finite aggregate observations

These are native Lean definitions and proofs, not embedded iPRA derivations.
`coverCheck` is a genuinely finite Boolean certificate.  Its reflection,
composition, union and image lemmas use no choice and no unproved axioms.
The rational-metric triangle instance inherits Classical.choice through
Std's rational-order lemmas; the axiom audit records this explicitly.
For arithmetization, instantiate `α` by encoded rational vectors, and replace
the native functions by specified primitive-recursive symbols.
-/

namespace FiniteDemand.Aggregates

def Covers {α β : Type} (rel : α → β → Prop) (s : List α) (t : List β) : Prop :=
  ∀ x, x ∈ s → ∃ y, y ∈ t ∧ rel x y

def coverCheck {α β : Type} (rel : α → β → Bool) (s : List α) (t : List β) : Bool :=
  s.all (fun x => t.any (rel x))

theorem coverCheck_correct {α β : Type} (rel : α → β → Bool)
    (s : List α) (t : List β) :
    coverCheck rel s t = true ↔ Covers (fun x y => rel x y = true) s t := by
  simp [coverCheck, Covers, List.all_eq_true, List.any_eq_true]

theorem covers_refl {α : Type} {rel : α → α → Prop}
    (hr : ∀ x, rel x x) (s : List α) : Covers rel s s := by
  intro x hx
  exact ⟨x, hx, hr x⟩

theorem covers_comp {α β γ : Type}
    {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop}
    {xs : List α} {ys : List β} {zs : List γ}
    (hxy : Covers r xs ys) (hyz : Covers s ys zs)
    (step : ∀ x y z, r x y → s y z → t x z) : Covers t xs zs := by
  intro x hx
  obtain ⟨y, hy, hxy'⟩ := hxy x hx
  obtain ⟨z, hz, hyz'⟩ := hyz y hy
  exact ⟨z, hz, step x y z hxy' hyz'⟩

theorem covers_append {α β : Type} {r : α → β → Prop}
    {s₁ s₂ : List α} {t₁ t₂ : List β}
    (h₁ : Covers r s₁ t₁) (h₂ : Covers r s₂ t₂) :
    Covers r (s₁ ++ s₂) (t₁ ++ t₂) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨y, hy, h⟩ := h₁ x hx
    exact ⟨y, List.mem_append.mpr (Or.inl hy), h⟩
  · obtain ⟨y, hy, h⟩ := h₂ x hx
    exact ⟨y, List.mem_append.mpr (Or.inr hy), h⟩

theorem covers_map {α β γ δ : Type}
    {r : α → β → Prop} {s : γ → δ → Prop}
    (f : α → γ) (g : β → δ) {xs : List α} {ys : List β}
    (h : Covers r xs ys) (step : ∀ x y, r x y → s (f x) (g y)) :
    Covers s (xs.map f) (ys.map g) := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, hxy⟩ := h x hx
  exact ⟨g y, List.mem_map.mpr ⟨y, hy, rfl⟩, step x y hxy⟩

structure RationalMetric (α : Type) where
  dist : α → α → Rat
  nonneg : ∀ x y, 0 ≤ dist x y
  self : ∀ x, dist x x = 0
  symm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

def Within {α : Type} (d : α → α → Rat) (ε : Rat)
    (s t : List α) : Prop :=
  Covers (fun x y => d x y ≤ ε) s t ∧
  Covers (fun y x => d x y ≤ ε) t s

def withinCheck {α : Type} (d : α → α → Rat) (ε : Rat)
    (s t : List α) : Bool :=
  coverCheck (fun x y => decide (d x y ≤ ε)) s t &&
  coverCheck (fun y x => decide (d x y ≤ ε)) t s

theorem withinCheck_correct {α : Type} (d : α → α → Rat)
    (ε : Rat) (s t : List α) :
    withinCheck d ε s t = true ↔ Within d ε s t := by
  simp only [withinCheck, Bool.and_eq_true, coverCheck_correct, Within, Covers,
    decide_eq_true_eq]

private theorem rat_add_mono {a b c d : Rat} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a + c ≤ b + d := by
  exact Rat.le_trans (Rat.add_le_add_right.mpr h₁) (Rat.add_le_add_left.mpr h₂)

theorem within_triangle {α : Type} (M : RationalMetric α)
    {s t u : List α} {ε δ : Rat}
    (hst : Within M.dist ε s t) (htu : Within M.dist δ t u) :
    Within M.dist (ε + δ) s u := by
  constructor
  · exact covers_comp hst.1 htu.1 (fun x y z h₁ h₂ =>
      Rat.le_trans (M.triangle x y z) (rat_add_mono h₁ h₂))
  · exact covers_comp htu.2 hst.2 (fun z y x h₁ h₂ =>
      Rat.le_trans (M.triangle x y z) (rat_add_mono h₂ h₁))

theorem within_union {α : Type} {d : α → α → Rat} {ε : Rat}
    {s₁ s₂ t₁ t₂ : List α}
    (h₁ : Within d ε s₁ t₁) (h₂ : Within d ε s₂ t₂) :
    Within d ε (s₁ ++ s₂) (t₁ ++ t₂) :=
  ⟨covers_append h₁.1 h₂.1, covers_append h₁.2 h₂.2⟩

def dyadic (k : Nat) : Rat := 1 / (2 ^ k : Nat)

/-- A name is a fixed program externally; this native type does not certify PR. -/
structure AggregateName (α : Type) (d : α → α → Rat) where
  approx : Nat → List α
  nonempty : ∀ k, approx k ≠ []
  coherent : ∀ s t, Within d (dyadic s + dyadic t) (approx s) (approx t)

#print axioms coverCheck_correct
#print axioms covers_comp
#print axioms covers_map
#print axioms withinCheck_correct
#print axioms within_triangle
#print axioms within_union

end FiniteDemand.Aggregates
