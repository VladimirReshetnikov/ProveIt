import Surreal.Algebra.ConstantTermGraph
import Mathlib.Algebra.Exact.Basic

/-!
# Definability of the canonical splitting

The algebraic content of `odg:def:cor:splitting`, including the literal
ring formula for the section, exactness, and the multiplication formula
following the corollary. The splitting is additive, with its cross terms
retained in multiplication.
-/

namespace Surreal.ConstantTermGraph

noncomputable section

variable {R O : Type*} [CommRing R] [CommRing O]

/-- Inclusion of the ordinary constants, represented entirely inside the ambient ring. -/
def SectionGraph (n x : R) : Prop := DiophantineConstants.Xi n ∧ x = n

/-- At equal input and output, the graph formula is exactly the constant predicate. -/
theorem graph_self_iff (n : R) : Graph n n ↔ DiophantineConstants.Xi n := by
  refine ⟨And.left, fun hn => ⟨hn, 0, ?_⟩⟩
  simp

/-- A checked exact splitting together with its parameter-free existential formulas. -/
structure DefinableSplitting (ct : R →+* O) (ι : O →+* R) : Prop where
  section_retraction : ∀ b : O, ct (ι b) = b
  kernel_injective : Function.Injective (fun p : RingHom.ker ct => (p : R))
  exact_kernel : Function.Exact (fun p : RingHom.ker ct => (p : R)) ct
  retraction_surjective : Function.Surjective ct
  kernel_formula : ∀ a : R, (∃ y : R, a ^ 2 = 2 * y ^ 2) ↔ ct a = 0
  retraction_formula : ∀ x n : R, Graph x n ↔ n = ι (ct x)
  section_formula : ∀ n x : R, SectionGraph n x ↔ ∃ b : O, n = ι b ∧ x = ι b

/-- The graph equivalence and the quadratic kernel test give the full definable splitting. -/
theorem definableSplitting_of_graph (ct : R →+* O) (ι : O →+* R)
    (hsection : ∀ b : O, ct (ι b) = b)
    (hgraph : ∀ x n : R, Graph x n ↔ n = ι (ct x))
    (hkernel : ∀ a : R, (∃ y : R, a ^ 2 = 2 * y ^ 2) ↔ ct a = 0) :
    DefinableSplitting ct ι := by
  refine ⟨hsection, Subtype.val_injective, ?_, fun b => ⟨ι b, hsection b⟩,
    hkernel, hgraph, ?_⟩
  · intro a
    exact ⟨fun ha => ⟨⟨a, ha⟩, rfl⟩, fun ⟨p, hp⟩ => hp ▸ p.property⟩
  · intro n x
    constructor
    · rintro ⟨hn, hx⟩
      have he := (hgraph n n).mp ((graph_self_iff n).mpr hn)
      exact ⟨ct n, he, hx.trans he⟩
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨(graph_self_iff _).mp ((hgraph _ _).mpr ?_), rfl⟩
      rw [hsection]

/-- The canonical additive decomposition, retaining the actual kernel subtype. -/
def splitAddEquiv (ct : R →+* O) (ι : O →+* R)
    (hsection : ∀ b : O, ct (ι b) = b) : R ≃+ O × RingHom.ker ct where
  toFun x := (ct x, ⟨x - ι (ct x), by
    change ct (x - ι (ct x)) = 0
    rw [map_sub, hsection, sub_self]⟩)
  invFun p := ι p.1 + p.2.val
  left_inv x := by dsimp; ring
  right_inv p := by
    rcases p with ⟨b, p, hp⟩
    change ct p = 0 at hp
    apply Prod.ext
    · simp [hsection, hp]
    · apply Subtype.ext
      simp [hsection, hp]
  map_add' x y := by
    apply Prod.ext
    · exact map_add ct x y
    · apply Subtype.ext
      dsimp
      rw [map_add, map_add]
      ring

/-- Multiplication in split coordinates has both scalar cross terms and the kernel product. -/
theorem split_multiplication (ι : O →+* R) (n m : O) (u v : R) :
    (ι n + u) * (ι m + v) = ι (n * m) + (ι n * v + ι m * u + u * v) := by
  rw [map_mul]
  ring

end
end Surreal.ConstantTermGraph
