import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact rational arithmetic for finite ideal optimizations

An ideal table stores norms and the two tests needed for admissibility.
The evaluator enumerates all subsets, tests their triples, and performs
only finite counting and rational arithmetic.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open Finset

/-- Finite ideal data needed by the optimization. -/
structure IdealCutoffTable (ι : Type*) where
  norm : ι → ℕ
  midpoint : ι → ι → ι → Bool
  divides : ι → ι → Bool

namespace IdealCutoffTable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact finite admissibility check for either ratio convention. -/
def Admissible (T : IdealCutoffTable ι) (integral : Bool) (A : Finset ι) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    T.midpoint a b c = true → (integral = true → T.divides a b = true) → a = b

instance (T : IdealCutoffTable ι) (integral : Bool) (A : Finset ι) : Decidable (T.Admissible integral A) :=
  inferInstanceAs (Decidable (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    T.midpoint a b c = true → (integral = true → T.divides a b = true) → a = b))

/-- The table vertices in the indicated norm ball. -/
def normBall (T : IdealCutoffTable ι) (H : ℕ) : Finset ι := univ.filter (fun a ↦ T.norm a ≤ H)

omit [DecidableEq ι] in
@[simp] theorem mem_normBall (T : IdealCutoffTable ι) (H : ℕ) (a : ι) :
    a ∈ T.normBall H ↔ T.norm a ≤ H := by simp [normBall]

/-- Exhaustive enumeration of admissible subsets of one norm ball. -/
def candidates (T : IdealCutoffTable ι) (integral : Bool) (H : ℕ) : Finset (Finset ι) :=
  (T.normBall H).powerset.filter (T.Admissible integral)

@[simp] theorem mem_candidates (T : IdealCutoffTable ι) (integral : Bool) (H : ℕ) (A : Finset ι) :
    A ∈ T.candidates integral H ↔ A ⊆ T.normBall H ∧ T.Admissible integral A := by
  simp [candidates]

theorem candidates_nonempty (T : IdealCutoffTable ι) (integral : Bool) (H : ℕ) :
    (T.candidates integral H).Nonempty := by
  refine ⟨∅,(T.mem_candidates integral H ∅).mpr ⟨empty_subset _,?_⟩⟩
  intro a ha
  exact (notMem_empty a ha).elim

/-- Reciprocal weight of a finite subset, computed rationally. -/
def reciprocalWeight (T : IdealCutoffTable ι) (A : Finset ι) : ℚ :=
  ∑ a ∈ A, (T.norm a : ℚ)⁻¹

/-- The rational optimum over single subsets. -/
def lowerWeight (T : IdealCutoffTable ι) (integral : Bool) (H : ℕ) : ℚ :=
  (T.candidates integral H).sup' (T.candidates_nonempty integral H) T.reciprocalWeight

/-- The largest admissible cardinality at a cutoff. -/
def prefixMaximum (T : IdealCutoffTable ι) (integral : Bool) (k : ℕ) : ℕ :=
  (T.candidates integral k).sup Finset.card

/-- Exact rational factor, retaining repeated norms of distinct primes. -/
def roughFactor (primeNorms : Multiset ℕ) : ℚ :=
  (primeNorms.map (fun q : ℕ ↦ 1-(q : ℚ)⁻¹)).prod

/-- Rational width of the norm step. -/
def stepWeight (k : ℕ) : ℚ := 1 / ((k : ℚ)*((k : ℚ)+1))

/-- The lower optimization through `H`, from the finite ideal table. -/
def boundedLower (T : IdealCutoffTable ι) (primeNorms : Multiset ℕ) (integral : Bool) (H : ℕ) : ℚ :=
  roughFactor primeNorms * T.lowerWeight integral H

/-- The upper optimization through `H`, from the same table. -/
def boundedUpper (T : IdealCutoffTable ι) (primeNorms : Multiset ℕ) (integral : Bool) (H : ℕ) : ℚ :=
  roughFactor primeNorms * ∑ k ∈ Icc 1 H, (T.prefixMaximum integral k : ℚ) * stepWeight k

/-- Normalized lower error at `H`, computed from the full finite norm ball. -/
def lowerError (T : IdealCutoffTable ι) (primeNorms : Multiset ℕ) (H : ℕ) : ℚ :=
  1 - roughFactor primeNorms * T.reciprocalWeight (T.normBall H)

/-- Normalized upper error at `H`, computed from finite cutoff counts. -/
def upperError (T : IdealCutoffTable ι) (primeNorms : Multiset ℕ) (H : ℕ) : ℚ :=
  1 - roughFactor primeNorms * ∑ k ∈ Icc 1 H, ((T.normBall k).card : ℚ) * stepWeight k

end IdealCutoffTable
end GRHArticle.ProgressionFree.NumberFieldIdeals
