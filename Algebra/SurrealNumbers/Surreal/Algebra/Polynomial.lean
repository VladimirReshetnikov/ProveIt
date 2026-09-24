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

noncomputable section

open Polynomial

variable {K L : Type*} [Field K] [Field L]

local instance polynomialDecidableEq : DecidableEq K := Classical.decEq K

/-- A factorization into linear factors determines its multiset of roots,
the uniqueness clause of `polynomial:thm:fta` in
`docs/surcomplex/polynomial-algebra/article.tex`. This direction needs no
algebraic closedness assumption. -/
theorem roots_eq_of_factorization (p : K[X]) (a : K) (s : Multiset K) (ha : a ≠ 0)
    (h : p = C a * (s.map fun b => X - C b).prod) : p.roots = s := by
  rw [h, Polynomial.roots_C_mul _ ha, Polynomial.roots_multiset_prod_X_sub_C]

/-- The scalar in a linear factorization is its leading coefficient,
the coefficient normalization in `polynomial:eq:factorization`. -/
theorem leadingCoeff_eq_of_factorization (p : K[X]) (a : K) (s : Multiset K)
    (h : p = C a * (s.map fun b => X - C b).prod) : p.leadingCoeff = a := by
  rw [h, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    (Polynomial.monic_multisetProd_X_sub_C s).leadingCoeff, mul_one]

/-- Both the nonzero scalar and the multiset in
`polynomial:eq:factorization` are unique. -/
theorem factorization_unique (p : K[X]) (a b : K) (s t : Multiset K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hs : p = C a * (s.map fun c => X - C c).prod)
    (ht : p = C b * (t.map fun c => X - C c).prod) : a = b ∧ s = t := by
  exact ⟨(leadingCoeff_eq_of_factorization p a s hs).symm.trans
      (leadingCoeff_eq_of_factorization p b t ht),
    (roots_eq_of_factorization p a s ha hs).symm.trans
      (roots_eq_of_factorization p b t hb ht)⟩

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

/-- The grouped version of `polynomial:eq:factorization`: distinct roots
index the product, and their root multiplicities give the exponents. -/
theorem factorization_grouped (p : K[X]) :
    p = C p.leadingCoeff * ∏ a ∈ p.roots.toFinset, (X - C a) ^ p.rootMultiplicity a := by
  rw [← Polynomial.prod_multiset_root_eq_finset_root]
  exact factorization p

/-- The sum of the distinct roots' multiplicities is the degree, as stated
in `polynomial:eq:factorization`. -/
theorem sum_rootMultiplicities (p : K[X]) :
    ∑ a ∈ p.roots.toFinset, p.rootMultiplicity a = p.natDegree := by
  simpa only [Polynomial.count_roots, roots_card] using
    Multiset.toFinset_sum_count_eq p.roots

/-- A nonzero polynomial has exactly one pair consisting of a nonzero
leading scalar and a multiset of linear factors (`polynomial:thm:fta`). -/
theorem exists_unique_factorization (p : K[X]) (hp : p ≠ 0) :
    ∃! data : K × Multiset K,
      data.1 ≠ 0 ∧ p = C data.1 * (data.2.map fun a => X - C a).prod := by
  refine ⟨(p.leadingCoeff, p.roots), ⟨Polynomial.leadingCoeff_ne_zero.mpr hp,
    factorization p⟩, ?_⟩
  rintro ⟨a, s⟩ ⟨ha, hs⟩
  exact Prod.ext (leadingCoeff_eq_of_factorization p a s hs).symm
    (roots_eq_of_factorization p a s ha hs).symm

/-- The finite logarithmic-derivative identity
`polynomial:eq:logderivative`, with repeated roots represented by a multiset.
The nonroot hypothesis makes all displayed rational expressions meaningful. -/
theorem logarithmic_derivative (p : K[X]) {z : K} (hz : p.eval z ≠ 0) :
    p.derivative.eval z / p.eval z =
      (p.roots.map fun a => 1 / (z - a)).sum :=
  (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz

/-- The grouped logarithmic derivative in `polynomial:eq:logderivative`,
with each distinct root weighted by its multiplicity. -/
theorem logarithmic_derivative_grouped (p : K[X]) {z : K} (hz : p.eval z ≠ 0) :
    p.derivative.eval z / p.eval z =
      ∑ a ∈ p.roots.toFinset, (p.rootMultiplicity a : K) / (z - a) := by
  rw [logarithmic_derivative p hz, Finset.sum_multiset_map_count]
  simp only [Polynomial.count_roots, nsmul_eq_mul, mul_one_div]

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

end

end FinitePolynomial
end Surreal
