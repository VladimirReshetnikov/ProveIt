import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finsupp.Weight

/-!
The fibre estimate in the proof for unequal Cartesian grids.
Write a multivariate polynomial, after translating the base point to the origin,
as a polynomial in the base variables with univariate polynomial coefficients.
All orders below are expressed using coefficients, in arbitrary characteristic.
-/

namespace DeepFormGrid

open Polynomial

variable {K σ : Type*} [Field K]

/-- Every coefficient of total degree below m vanishes after translating the
last coordinate by u. The base coordinates of F have already been translated. -/
def JetAtLeast (F : MvPolynomial σ K[X]) (u : K) (m : ℕ) : Prop :=
  ∀ (β : σ →₀ ℕ) (j : ℕ), β.degree + j < m →
    ((F.coeff β).comp (X + C u)).coeff j = 0

/-- A nonzero base Hasse coefficient of order |β| bounds the vanishing order
on the fibre by |β| plus its one-variable root multiplicity. -/
theorem fibre_order_le {F : MvPolynomial σ K[X]} {β : σ →₀ ℕ}
    (hβ : F.coeff β ≠ 0) {u : K} {m : ℕ} (hF : JetAtLeast F u m) :
    m ≤ β.degree + rootMultiplicity u (F.coeff β) := by
  have hm : m - β.degree ≤ rootMultiplicity u (F.coeff β) := by
    apply (le_rootMultiplicity_iff hβ).2
    apply X_sub_C_pow_dvd_iff.2
    apply X_pow_dvd_iff.2
    intro j hj
    exact hF β j (by omega)
  omega

/-- Sum the fibre orders at distinct points. Select β at each base point from
the first nonzero jet of the coefficient of highest last-coordinate degree. -/
theorem fibre_sum_le (A : Finset K) {F : MvPolynomial σ K[X]} {β : σ →₀ ℕ}
    (hβ : F.coeff β ≠ 0) (m : K → ℕ) (hF : ∀ u ∈ A, JetAtLeast F u (m u)) :
    ∑ u ∈ A, m u ≤ A.card * β.degree + (F.coeff β).natDegree := by
  classical
  let g := F.coeff β
  have hsum : ∑ u ∈ A, rootMultiplicity u g ≤ g.natDegree := by
    simp only [← count_roots g]
    calc
      ∑ u ∈ A, g.roots.count u ≤ ∑ u ∈ A ∪ g.roots.toFinset, g.roots.count u :=
        Finset.sum_le_sum_of_subset (Finset.subset_union_left)
      _ = g.roots.card := Multiset.sum_count_eq_card (fun a ha =>
        Finset.mem_union_right A (Multiset.mem_toFinset.mpr ha))
      _ ≤ g.natDegree := card_roots' g
  calc
    ∑ u ∈ A, m u ≤ ∑ u ∈ A, (β.degree + rootMultiplicity u g) :=
      Finset.sum_le_sum fun u hu => fibre_order_le hβ (hF u hu)
    _ = A.card * β.degree + ∑ u ∈ A, rootMultiplicity u g := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left hsum _

#print axioms fibre_order_le
#print axioms fibre_sum_le

end DeepFormGrid
