import Init

/-!
The degree of ordinary n-chains is encoded as n+2, allowing two zero slots below it.
For a comparison f from the total complex to the covered space or nerve, augmented
double-complex elimination establishes ConeExact at adjacent slots. The two conclusions
below are the explicit cycle lift and the reflection of a boundary. The file is
independent of any axiom of choice or quotient construction.
-/
namespace FiniteNerve

structure ChainData where
  V : Nat → Type
  zero : (k : Nat) → V k
  add : {k : Nat} → V k → V k → V k
  bd : {k : Nat} → V (k+1) → V k
  bd_zero : ∀ k, bd (zero (k+1)) = zero k

structure Comparison (A B : ChainData) where
  apply : (k : Nat) → A.V k → B.V k
  map_zero : ∀ k, apply k (A.zero k) = B.zero k

/-- With characteristic two, the augmented differential sends (z,w) to
    (∂z, f z + ∂w). This proposition records exactness one degree at a time. -/
def ConeExact {A B : ChainData} (f : Comparison A B) (k : Nat) : Prop :=
  ∀ (x : A.V (k+1)) (y : B.V (k+2)),
    A.bd x = A.zero k → f.apply (k+1) x = B.bd y →
    ∃ (z : A.V (k+2)) (w : B.V (k+3)),
      A.bd z = x ∧ B.add (f.apply (k+2) z) (B.bd w) = y

theorem lift_cycle {A B : ChainData} {f : Comparison A B}
    (k : Nat) (h : ConeExact f k) (y : B.V (k+2))
    (closed : B.bd y = B.zero (k+1)) :
    ∃ (z : A.V (k+2)) (w : B.V (k+3)),
      A.bd z = A.zero (k+1) ∧ B.add (f.apply (k+2) z) (B.bd w) = y :=
  h (A.zero (k+1)) y (A.bd_zero k) ((f.map_zero (k+1)).trans closed.symm)

theorem reflect_boundary {A B : ChainData} {f : Comparison A B}
    (k : Nat) (h : ConeExact f (k+1)) (x : A.V (k+2))
    (closed : A.bd x = A.zero (k+1))
    (y : B.V (k+3)) (image_bounds : f.apply (k+2) x = B.bd y) :
    ∃ z : A.V (k+3), A.bd z = x := by
  obtain ⟨z, _, hz, _⟩ := h x y closed image_bounds
  exact ⟨z, hz⟩

/-- Bounded elimination behind exactness. stage k means all columns/rows
    at indices ≥ k have vanished and u is a cycle. A step supplies its filler. -/
theorem bounded_eliminate {V : Type} (stage : Nat → V → Prop)
    (add : V → V → V) (zero : V) (bd : V → V)
    (bd_zero : bd zero = zero) (bd_add : ∀ a b, bd (add a b) = add (bd a) (bd b))
    (undo : ∀ a b, add (add a b) b = a)
    (bottom : ∀ u, stage 0 u → u = zero)
    (step : ∀ k u, stage (k+1) u → ∃ v, stage k (add u (bd v))) :
    ∀ k u, stage k u → ∃ v, bd v = u := by
  intro k
  induction k with
  | zero =>
    intro u hu
    exact ⟨zero, bd_zero.trans (bottom u hu).symm⟩
  | succ k ih =>
    intro u hu
    obtain ⟨v, hv⟩ := step k u hu
    obtain ⟨w, hw⟩ := ih _ hv
    exact ⟨add w v, (bd_add w v).trans ((congrArg (fun a => add a (bd v)) hw).trans (undo u (bd v)))⟩

end FiniteNerve
