import GRHArticle.ProgressionFree.PolynomialRoughReplacement
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Squarefree.Basic

/-!
# The monic rough and smooth parts of a polynomial
-/

namespace GRHArticle.ProgressionFree

open UniqueFactorizationMonoid

noncomputable local instance {F : Type*} [Field F] : DecidableEq F := Classical.decEq F

/-- The monic part made of irreducibles of degree greater than `L`. -/
noncomputable def polynomialRoughPart {F : Type*} [Field F] (L : ℕ) (f : Polynomial F) :
    Polynomial F :=
  (polynomialRoughFactors L f).prod

/-- The monic part made of irreducibles of degree at most `L`. -/
noncomputable def polynomialSmoothPart {F : Type*} [Field F] (L : ℕ) (f : Polynomial F) :
    Polynomial F :=
  ((normalizedFactors f).filter fun p ↦ p.natDegree ≤ L).prod

private theorem monic_mem_polynomial_normalizedFactors {F : Type*} [Field F]
    {f p : Polynomial F} (hp : p ∈ normalizedFactors f) : p.Monic :=
  (Polynomial.normalize_eq_self_iff_monic (irreducible_of_normalized_factor p hp).ne_zero).mp
    (normalize_normalized_factor p hp)

private theorem mem_polynomialRoughFactors {F : Type*} [Field F] {L : ℕ}
    {f p : Polynomial F} :
    p ∈ polynomialRoughFactors L f ↔ p ∈ normalizedFactors f ∧ L < p.natDegree :=
  Multiset.mem_filter

/-- The normalized rough and smooth product is exactly the original polynomial after
restoring its leading coefficient. -/
theorem polynomial_eq_leadingCoeff_mul_roughPart_mul_smoothPart {F : Type*} [Field F]
    (L : ℕ) (f : Polynomial F) :
    Polynomial.C f.leadingCoeff * polynomialRoughPart L f * polynomialSmoothPart L f = f := by
  rw [polynomialRoughPart, polynomialSmoothPart, mul_assoc, ← Multiset.prod_add]
  unfold polynomialRoughFactors
  simpa only [not_lt] using
    congrArg (fun s : Multiset (Polynomial F) ↦ Polynomial.C f.leadingCoeff * s.prod)
      (Multiset.filter_add_not (fun p : Polynomial F ↦ L < p.natDegree) (normalizedFactors f)) |>.trans
        (Polynomial.leadingCoeff_mul_prod_normalizedFactors f)

theorem monic_polynomialRoughPart {F : Type*} [Field F] (L : ℕ) (f : Polynomial F) :
    (polynomialRoughPart L f).Monic := by
  simpa only [polynomialRoughPart, Multiset.map_id] using
    Polynomial.monic_multiset_prod_of_monic (polynomialRoughFactors L f) id
      (fun _ hp ↦ monic_mem_polynomial_normalizedFactors (mem_polynomialRoughFactors.mp hp).1)

theorem natDegree_polynomialRoughPart {F : Type*} [Field F] (L : ℕ) (f : Polynomial F) :
    (polynomialRoughPart L f).natDegree = ((polynomialRoughFactors L f).map Polynomial.natDegree).sum :=
  Polynomial.natDegree_multiset_prod_of_monic (polynomialRoughFactors L f)
    (fun _ hp ↦ monic_mem_polynomial_normalizedFactors (mem_polynomialRoughFactors.mp hp).1)

theorem normalizedFactors_polynomialRoughPart {F : Type*} [Field F] (L : ℕ) (f : Polynomial F) :
    normalizedFactors (polynomialRoughPart L f) = polynomialRoughFactors L f := by
  rw [polynomialRoughPart, normalizedFactors_prod_eq _ (fun p hp ↦
    irreducible_of_normalized_factor p (mem_polynomialRoughFactors.mp hp).1)]
  rw [Multiset.map_congr rfl (f := normalize) (g := id) (fun p hp ↦
    normalize_normalized_factor p (mem_polynomialRoughFactors.mp hp).1), Multiset.map_id]

theorem squarefree_polynomialRoughPart_iff {F : Type*} [Field F] (L : ℕ) (f : Polynomial F) :
    Squarefree (polynomialRoughPart L f) ↔ (polynomialRoughFactors L f).Nodup := by
  rw [squarefree_iff_nodup_normalizedFactors (monic_polynomialRoughPart L f).ne_zero,
    normalizedFactors_polynomialRoughPart]

/-- The concrete replacement tests the squarefree monic rough part and its actual degree. -/
theorem mem_polynomialDeficitReplacement_iff {F : Type*} [Field F] (N R : ℕ) (f : Polynomial F) :
    f ∈ polynomialDeficitReplacement N R ↔ f ≠ 0 ∧ f.natDegree ≤ N ∧
      ((Squarefree (polynomialRoughPart 480 f) ∧ (polynomialRoughPart 480 f).natDegree = N - R) →
        N - f.natDegree ∈ polynomialDeficitWitness) ∧
      (¬ (Squarefree (polynomialRoughPart 480 f) ∧ (polynomialRoughPart 480 f).natDegree = N - R) →
        N - f.natDegree ∈ greedyExponents) := by
  simp only [squarefree_polynomialRoughPart_iff, natDegree_polynomialRoughPart,
    polynomialDeficitReplacement, polynomialRoughReplacementSet, Set.mem_setOf_eq,
    Finset.mem_coe]

end GRHArticle.ProgressionFree
