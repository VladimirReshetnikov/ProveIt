import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Finite polynomial algebra and descent

These are the finite algebraic parts of `polynomial:thm:fta` and the
root-persistence clause of `found:thm:workspace` in the repository manuscripts.
The fields are explicit parameters: no surreal normal-form theorem, Hahn
workspace construction, or algebraic closedness of a concrete surreal
complexification is assumed to have been proved here.

The final theorem proves the image-containment clause of
`found:thm:finitepoints`. Preservation of local algebraic lengths is a separate
part of that theorem and is not asserted here.
-/

namespace Surreal
namespace FinitePolynomial

open Polynomial

variable {K L : Type*} [Field K] [Field L]

section AlgebraicallyClosed

variable [IsAlgClosed K]

/-- The existence-of-roots clause of `polynomial:thm:fta`. -/
theorem exists_root (p : K[X]) (hp : 0 < p.natDegree) :
    ∃ a : K, p.IsRoot a :=
  IsAlgClosed.exists_root p (degree_ne_of_natDegree_ne (Nat.ne_of_gt hp))

/-- The factorization identity `polynomial:eq:factorization`, with roots
listed with multiplicity. The identity also handles constant and zero
polynomials. -/
theorem factorization (p : K[X]) :
    p = C p.leadingCoeff * (p.roots.map fun a => X - C a).prod :=
  (IsAlgClosed.splits p).eq_prod_roots

/-- The total multiplicity in `polynomial:eq:factorization` is the degree. -/
theorem roots_card (p : K[X]) : p.roots.card = p.natDegree :=
  (IsAlgClosed.splits p).natDegree_eq_card_roots.symm

/-- The finite logarithmic-derivative identity
`polynomial:eq:logderivative`, with repeated roots represented by a multiset.
The nonroot hypothesis makes all displayed rational expressions meaningful. -/
theorem logarithmic_derivative (p : K[X]) {z : K} (hz : p.eval z ≠ 0) :
    p.derivative.eval z / p.eval z =
      (p.roots.map fun a => 1 / (z - a)).sum :=
  (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz

end AlgebraicallyClosed

/-- Root multiplicities persist under field extension once a polynomial
splits. This is the purely algebraic part of `found:thm:workspace` (3). -/
theorem roots_map (p : K[X]) (hp : p.Splits) (i : K →+* L) :
    (p.map i).roots = p.roots.map i :=
  hp.roots_map i

/-- A split, nonzero polynomial acquires no new root locations in an
extension field (`found:thm:workspace`, clause 3). -/
theorem root_mem_range (p : K[X]) (hp : p.Splits) (hp0 : p ≠ 0)
    (i : K →+* L) {z : L} (hz : (p.map i).IsRoot z) :
    ∃ a : K, i a = z :=
  hp.mem_range_of_isRoot hp0 hz

/-- The algebraically closed specialization of `roots_map` used for
polynomial workspace enlargement. -/
theorem roots_map_of_isAlgClosed [IsAlgClosed K] (p : K[X]) (i : K →+* L) :
    (p.map i).roots = p.roots.map i :=
  roots_map p (IsAlgClosed.splits p) i

/-- The image-containment clause of `found:thm:finitepoints`: a character of
a finite algebra over an algebraically closed field takes values in the
base field, even when its codomain is a larger field. -/
theorem finite_algebra_character_descends [IsAlgClosed K] [Algebra K L]
    {B : Type*} [CommRing B] [Algebra K B] [Module.Finite K B]
    (φ : B →ₐ[K] L) (b : B) : ∃ a : K, algebraMap K L a = φ b := by
  obtain ⟨p, hp, hroot⟩ := (IsIntegral.of_finite K b).map φ
  exact root_mem_range p (IsAlgClosed.splits p) hp.ne_zero (algebraMap K L) (by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hroot)

end FinitePolynomial
end Surreal
