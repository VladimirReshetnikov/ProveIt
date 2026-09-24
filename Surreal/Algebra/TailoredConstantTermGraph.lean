import Surreal.Algebra.TailoredIdealTest

/-!
# Both prenex constant-term graphs for the tailored guard

The graph clauses of `odg:def:thm:numberfield`, with the two quantifier
orders displayed in `odg:def:rem:sigma2`. Five witnesses belong to the
constant guard and two universal variables to the negated detector.
-/

namespace Surreal.TailoredConstantTermGraph
open TailoredDiophantineConstants TailoredIntersectivePolynomial

variable {R O : Type*} [CommRing R] [CommRing O]

/-- A constant satisfying the universal detector condition on the input-output difference. -/
def Graph (p q : ℕ) (x n : R) : Prop :=
  Xi p q n ∧ ∀ s t : R, (x - n) * s ≠ value p q t

/-- The guard witnesses can be placed before the two universal variables. -/
theorem graph_iff_exists_forall (p q : ℕ) (x n : R) : Graph p q x n ↔
    ∃ u v w s t : R, ∀ a b : R,
      System p q n u v w s t ∧ (x - n) * a ≠ value p q b := by
  constructor
  · rintro ⟨⟨u, v, w, s, t, h⟩, hne⟩
    exact ⟨u, v, w, s, t, fun a b => ⟨h, hne a b⟩⟩
  · rintro ⟨u, v, w, s, t, h⟩
    exact ⟨⟨u, v, w, s, t, (h 0 0).1⟩, fun a b => (h a b).2⟩

/-- The universal variables can instead precede the five guard witnesses. -/
theorem graph_iff_forall_exists (p q : ℕ) (x n : R) : Graph p q x n ↔
    ∀ a b : R, ∃ u v w s t : R,
      System p q n u v w s t ∧ (x - n) * a ≠ value p q b := by
  constructor
  · rintro ⟨⟨u, v, w, s, t, h⟩, hne⟩ a b
    exact ⟨u, v, w, s, t, h, hne a b⟩
  · intro h
    obtain ⟨u, v, w, s, t, hs, _⟩ := h 0 0
    refine ⟨⟨u, v, w, s, t, hs⟩, ?_⟩
    intro a b
    obtain ⟨_, _, _, _, _, _, hne⟩ := h a b
    exact hne

/-- A constant guard and the detector determine the embedded retraction graph. -/
theorem graph_iff (p q : ℕ) (ct : R →+* O) (ι : O →+* R)
    (hsection : ∀ b : O, ct (ι b) = b)
    (hXi : ∀ n : R, Xi p q n ↔ n ∈ ι.range)
    (hdet : ∀ a : R, Detects p q a ↔ ct a ≠ 0) (x n : R) :
    Graph p q x n ↔ n = ι (ct x) := by
  rw [Graph, ← constant_eq_iff_universal p q ct hdet x n, hXi]
  constructor
  · rintro ⟨⟨b, rfl⟩, he⟩
    rw [hsection] at he
    rw [he]
  · rintro rfl
    exact ⟨⟨ct x, rfl⟩, (hsection _).symm⟩

/-- Every input has a unique output, regardless of nonuniqueness of guard witnesses. -/
theorem existsUnique_output (p q : ℕ) (ct : R →+* O) (ι : O →+* R)
    (hsection : ∀ b : O, ct (ι b) = b)
    (hXi : ∀ n : R, Xi p q n ↔ n ∈ ι.range)
    (hdet : ∀ a : R, Detects p q a ↔ ct a ≠ 0) (x : R) : ∃! n, Graph p q x n :=
  ⟨ι (ct x), (graph_iff p q ct ι hsection hXi hdet x _).mpr rfl,
    fun n hn => (graph_iff p q ct ι hsection hXi hdet x n).mp hn⟩

end Surreal.TailoredConstantTermGraph
