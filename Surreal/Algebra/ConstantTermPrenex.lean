import Surreal.Algebra.ConstantTermGraph
import Surreal.Algebra.IntersectiveIdealTest

/-!
# The two quantified constant-term graph formulas

The literal formulas in `odg:def:rem:sigma2`, including both quantifier
orders and the five ordinary-constant witnesses. The proof of the second
order recovers a fixed constant witness by specializing its universal
variables to zero.
-/

namespace Surreal.ConstantTermGraph

noncomputable section

variable {R O : Type*} [CommRing R] [CommRing O]

/-- Source 07's universal-test graph formula. -/
def UniversalGraph (a c : R) : Prop :=
  DiophantineConstants.Xi c ∧ ∀ s t : R, (a - c) * s ≠ IntersectivePolynomial.value t

/-- Five existential constant witnesses precede the two universal variables. -/
def ExistsForallGraph (a c : R) : Prop :=
  ∃ u v w p q : R, ∀ s t : R,
    DiophantineConstants.System c u v w p q ∧ (a - c) * s ≠ IntersectivePolynomial.value t

/-- The alternative order allows the five witnesses to depend on the two universal variables. -/
def ForallExistsGraph (a c : R) : Prop :=
  ∀ s t : R, ∃ u v w p q : R,
    DiophantineConstants.System c u v w p q ∧ (a - c) * s ≠ IntersectivePolynomial.value t

/-- The first prenex form is equivalent to the conjunction in the source. -/
theorem existsForallGraph_iff (a c : R) : ExistsForallGraph a c ↔ UniversalGraph a c := by
  constructor
  · rintro ⟨u, v, w, p, q, h⟩
    exact ⟨⟨u, v, w, p, q, (h 0 0).1⟩, fun s t => (h s t).2⟩
  · rintro ⟨⟨u, v, w, p, q, h⟩, hst⟩
    exact ⟨u, v, w, p, q, fun s t => ⟨h, hst s t⟩⟩

/-- The second prenex form also defines exactly the same graph. -/
theorem forallExistsGraph_iff (a c : R) : ForallExistsGraph a c ↔ UniversalGraph a c := by
  constructor
  · intro h
    obtain ⟨u, v, w, p, q, hc, _⟩ := h 0 0
    refine ⟨⟨u, v, w, p, q, hc⟩, ?_⟩
    intro s t
    obtain ⟨_, _, _, _, _, _, hst⟩ := h s t
    exact hst
  · rintro ⟨⟨u, v, w, p, q, hc⟩, hst⟩
    exact fun s t => ⟨u, v, w, p, q, hc, hst s t⟩

/-- The universal-test graph agrees with the existential graph whenever the kernel is detected. -/
theorem universalGraph_iff_graph (ct : R →+* O)
    (hdet : ∀ a : R, IntersectivePolynomial.Detects a ↔ ct a ≠ 0)
    (hkernel : ∀ a : R, (∃ y : R, a ^ 2 = 2 * y ^ 2) ↔ ct a = 0) (a c : R) :
    UniversalGraph a c ↔ Graph a c := by
  unfold UniversalGraph Graph
  rw [← IntersectivePolynomial.mem_iff_universal (RingHom.ker ct) hdet (a - c), hkernel]
  rfl

/-- Both prenex formulas have exactly the same meaning as the existential graph. -/
theorem prenex_graph_equivalences (ct : R →+* O)
    (hdet : ∀ a : R, IntersectivePolynomial.Detects a ↔ ct a ≠ 0)
    (hkernel : ∀ a : R, (∃ y : R, a ^ 2 = 2 * y ^ 2) ↔ ct a = 0) (a c : R) :
    (UniversalGraph a c ↔ Graph a c) ∧
      (ExistsForallGraph a c ↔ Graph a c) ∧ (ForallExistsGraph a c ↔ Graph a c) := by
  have h := universalGraph_iff_graph ct hdet hkernel a c
  exact ⟨h, (existsForallGraph_iff a c).trans h, (forallExistsGraph_iff a c).trans h⟩

end
end Surreal.ConstantTermGraph
