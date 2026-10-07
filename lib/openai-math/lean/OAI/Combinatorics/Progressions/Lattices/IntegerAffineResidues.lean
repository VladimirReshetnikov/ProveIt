/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import OAI.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialResidues
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def integerJetMatrix {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℤ) (vertices : Finset α → K → ℤ)
    (rows : O → Finset α) : Matrix O J ℤ :=
  fun o j => booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (basis j)) (rows o)

theorem integerJetMatrix_apply_coefficients {α K O J : Type*} [DecidableEq α] [Fintype J]
    (basis : J → MvPolynomial K ℤ) (vertices : Finset α → K → ℤ)
    (rows : O → Finset α) (c : J → ℤ) (o : O) :
    (integerJetMatrix basis vertices rows *ᵥ c) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
        (∑ j, MvPolynomial.C (c j) * basis j)) (rows o) := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C,
    booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, integerJetMatrix basis vertices rows o j * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem integerJetMatrix_residue_eq {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℤ) (vertices vertices' : Finset α → K → ℤ)
    (rows : O → Finset α) (m : ℕ)
    (hvertices : ∀ o t, t ∈ (rows o).powerset →
      integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t)) :
    integerResidueMatrix (integerJetMatrix basis vertices rows) m =
      integerResidueMatrix (integerJetMatrix basis vertices' rows) m := by
  ext o j
  apply integerBooleanCoefficient_congr
  intro t ht
  exact integerPolynomial_eval_congr (basis j) m (hvertices o t ht)

theorem integerJetMatrix_image_eq {α K O J : Type*} [DecidableEq α] [Fintype O] [Fintype J]
    (basis : J → MvPolynomial K ℤ) (vertices vertices' : Finset α → K → ℤ)
    (rows : O → Finset α) (m : ℕ)
    (hvertices : ∀ o t, t ∈ (rows o).powerset →
      integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t))
    (hperiod : integerScalarLattice O (m : ℤ) ≤ (integerJetMatrix basis vertices rows).mulVecLin.range)
    (hperiod' : integerScalarLattice O (m : ℤ) ≤ (integerJetMatrix basis vertices' rows).mulVecLin.range) :
    (integerJetMatrix basis vertices rows).mulVecLin.range =
      (integerJetMatrix basis vertices' rows).mulVecLin.range :=
  integerMatrixImage_eq_of_residueMatrix _ _ m hperiod hperiod'
    (integerJetMatrix_residue_eq basis vertices vertices' rows m hvertices)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerBooleanInterpolant {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) : MvPolynomial K ℤ :=
  MvPolynomial.C (a ^ (h - s.card)) * ∏ r ∈ s, q r

theorem integerBooleanInterpolant_eval {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (vertices : Finset α → K → ℤ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then a else 0)
    (t : Finset α) :
    MvPolynomial.eval (vertices t) (integerBooleanInterpolant q a h s) =
      a ^ h * if s ⊆ t then 1 else 0 := by
  have hprod : (∏ r ∈ s, MvPolynomial.eval (vertices t) (q r)) =
      if s ⊆ t then a ^ s.card else 0 := by
    by_cases hst : s ⊆ t
    · rw [ite_eq_left hst]
      calc
        _ = ∏ _r ∈ s, a := Finset.prod_congr rfl (fun r hr => by rw [hq r t, ite_eq_left (hst hr)])
        _ = _ := by simp
    · rw [ite_eq_right hst]
      obtain ⟨r, hrs, hrt⟩ := Finset.not_subset.mp hst
      exact Finset.prod_eq_zero hrs (by rw [hq r t, ite_eq_right hrt])
  rw [integerBooleanInterpolant, map_mul, MvPolynomial.eval_C, map_prod, hprod]
  by_cases hst : s ⊆ t
  · simp only [ite_eq_left hst, mul_one]
    rw [← pow_add, Nat.sub_add_cancel hs]
  · simp only [ite_eq_right hst, mul_zero]

theorem integerBooleanInterpolant_jet {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (vertices : Finset α → K → ℤ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then a else 0)
    (row : Finset α) :
    booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
      (integerBooleanInterpolant q a h s)) row = if row = s then a ^ h else 0 := by
  simp_rw [integerBooleanInterpolant_eval q a h s hs vertices hq]
  rw [booleanCoefficient_const_mul, booleanCoefficient_monomial]
  split_ifs <;> simp

theorem integerBooleanInterpolant_degree {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (hq : ∀ r ∈ s, (q r).totalDegree ≤ 1) :
    (integerBooleanInterpolant q a h s).totalDegree ≤ h := by
  unfold integerBooleanInterpolant
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd s q).trans
  calc
    _ ≤ ∑ _r ∈ s, 1 := Finset.sum_le_sum hq
    _ = s.card := by simp
    _ ≤ h := hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def integerAffineCube {α K : Type*} (root : K → ℤ) (difference : α → K → ℤ)
    (t : Finset α) : K → ℤ := fun k => root k + ∑ r ∈ t, difference r k

noncomputable def integerAffineNumerator {K : Type*} [Fintype K]
    (root n : K → ℤ) : MvPolynomial K ℤ :=
  ∑ k, MvPolynomial.C (n k) * (MvPolynomial.X k - MvPolynomial.C (root k))

theorem integerAffineNumerator_eval {α K : Type*} [Fintype K]
    (root n : K → ℤ) (difference : α → K → ℤ) (t : Finset α) :
    MvPolynomial.eval (integerAffineCube root difference t) (integerAffineNumerator root n) =
      ∑ r ∈ t, ∑ k, n k * difference r k := by
  simp only [integerAffineNumerator, map_sum, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, integerAffineCube, add_sub_cancel_left,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem integerAffineNumerator_boolean {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (difference : α → K → ℤ) (n : α → K → ℤ) (a : ℤ)
    (hdual : ∀ r s, (∑ k, n r k * difference s k) = if r = s then a else 0)
    (r : α) (t : Finset α) :
    MvPolynomial.eval (integerAffineCube root difference t) (integerAffineNumerator root (n r)) =
      if r ∈ t then a else 0 := by
  rw [integerAffineNumerator_eval]
  simp only [hdual, Finset.sum_ite_eq]

theorem integerAffineNumerator_degree {K : Type*} [Fintype K] (root n : K → ℤ) :
    (integerAffineNumerator root n).totalDegree ≤ 1 := by
  unfold integerAffineNumerator
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)

theorem integerAffine_interpolation {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (difference : α → K → ℤ) (n : α → K → ℤ) (a : ℤ)
    (hdual : ∀ r s, (∑ k, n r k * difference s k) = if r = s then a else 0)
    (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    ∃ p : MvPolynomial K ℤ, p.totalDegree ≤ h ∧ ∀ row : Finset α,
      booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root difference t) p) row =
        if row = s then a ^ h else 0 := by
  let q := fun r => integerAffineNumerator root (n r)
  refine ⟨integerBooleanInterpolant q a h s,
    integerBooleanInterpolant_degree q a h s hs (fun r _ => integerAffineNumerator_degree root (n r)), ?_⟩
  exact integerBooleanInterpolant_jet q a h s hs (integerAffineCube root difference)
    (integerAffineNumerator_boolean root difference n a hdual)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem exists_integer_kernel_dual {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
    (D : Matrix α K ℤ) (a : ℤ) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range) :
    ∃ n : α → K → ℤ, ∀ r s, (∑ k, n r k * D s k) = if r = s then a else 0 := by
  have hex (r : α) : ∃ n : K → ℤ, D *ᵥ n = a • Pi.single r 1 :=
    hperiod ((integerScalarLattice_mem a _).mpr ⟨Pi.single r 1, rfl⟩)
  choose n hn using hex
  refine ⟨n, fun r s => ?_⟩
  calc
    _ = (D *ᵥ n r) s := by simp [Matrix.mulVec, dotProduct, mul_comm]
    _ = (a • (Pi.single r 1 : α → ℤ)) s := congrFun (hn r) s
    _ = _ := by
      by_cases hrs : r = s
      · subst s; simp
      · simp [hrs, Ne.symm hrs]

theorem integerKernel_interpolation {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
    (D : Matrix α K ℤ) (a : ℤ) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (root : K → ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    ∃ p : MvPolynomial K ℤ, p.totalDegree ≤ h ∧ ∀ row : Finset α,
      booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root D t) p) row =
        if row = s then a ^ h else 0 := by
  obtain ⟨n, hn⟩ := exists_integer_kernel_dual D a hperiod
  exact integerAffine_interpolation root D n a hn h s hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def realAffineCube {α K : Type*} (root : K → ℝ) (difference : α → K → ℝ)
    (t : Finset α) : K → ℝ := fun k => root k + ∑ r ∈ t, difference r k

noncomputable def realAffineDualPolynomial {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ) : MvPolynomial K ℝ :=
  ∑ j, MvPolynomial.C (n j) *
    (MvPolynomial.X (selection j) - MvPolynomial.C (root (selection j)))

theorem realAffineDualPolynomial_eval {α I K : Type*} [Fintype I]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : I → K)
    (n : I → ℝ) (t : Finset α) :
    MvPolynomial.eval (realAffineCube root difference t)
      (realAffineDualPolynomial root selection n) =
        ∑ r ∈ t, ∑ j, n j * difference r (selection j) := by
  simp only [realAffineDualPolynomial, map_sum, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, realAffineCube,
    add_sub_cancel_left, Finset.mul_sum]
  exact Finset.sum_comm

theorem realAffineDualPolynomial_boolean {α I K : Type*}
    [DecidableEq α] [Fintype I]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : I → K)
    (n : α → I → ℝ)
    (hdual : ∀ r s, (∑ j, n r j * difference s (selection j)) =
      if r = s then 1 else 0) (r : α) (t : Finset α) :
    MvPolynomial.eval (realAffineCube root difference t)
      (realAffineDualPolynomial root selection (n r)) = if r ∈ t then 1 else 0 := by
  rw [realAffineDualPolynomial_eval]
  simp only [hdual, Finset.sum_ite_eq]

theorem realAffineDualPolynomial_degree {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ) :
    (realAffineDualPolynomial root selection n).totalDegree ≤ 1 := by
  unfold realAffineDualPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)

theorem realPolynomialMass_neg {K : Type*} (p : MvPolynomial K ℝ) :
    realPolynomialMass (-p) = realPolynomialMass p := by
  classical
  simp [realPolynomialMass]

theorem realPolynomialMass_sub_le {K : Type*} (p q : MvPolynomial K ℝ) :
    realPolynomialMass (p - q) ≤ realPolynomialMass p + realPolynomialMass q := by
  simpa only [sub_eq_add_neg, realPolynomialMass_neg] using realPolynomialMass_add_le p (-q)

theorem realAffineDualPolynomial_mass {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ)
    (hroot : ∀ j, |root (selection j)| ≤ 1) {V : ℝ} (hV : 0 ≤ V)
    (hn : ∀ j, |n j| ≤ V) :
    realPolynomialMass (realAffineDualPolynomial root selection n) ≤
      (Fintype.card I : ℝ) * (2 * V) := by
  unfold realAffineDualPolynomial
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : I, 2 * V := by
      apply Finset.sum_le_sum
      intro j _
      apply (realPolynomialMass_C_mul_le _ _).trans
      have hm : realPolynomialMass
          (MvPolynomial.X (selection j) - MvPolynomial.C (root (selection j))) ≤ 2 := by
        apply (realPolynomialMass_sub_le _ _).trans
        simp only [realPolynomialMass_X, realPolynomialMass_C]
        linarith [hroot j]
      calc
        _ ≤ V * 2 := mul_le_mul (hn j) hm (realPolynomialMass_nonneg _) hV
        _ = 2 * V := mul_comm _ _
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def boundedDegreeIntegerJetMatrix {α K O : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    Matrix O (BoundedIntegerExponent K h) ℤ :=
  integerJetMatrix (fun e => MvPolynomial.monomial e.val 1) (integerAffineCube root D) rows

theorem boundedDegreeIntegerJetMatrix_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ h) ≤ (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range := by
  classical
  have hex (o : O) := integerKernel_interpolation D a hperiod root h (rows o) (hdegree o)
  choose p hp hjet using hex
  let E := boundedDegreeIntegerJetMatrix root D h rows
  have hunit (o : O) : a ^ h • Pi.single o 1 ∈ E.mulVecLin.range := by
    let c : BoundedIntegerExponent K h → ℤ := fun e => (p o).coeff e.val
    refine ⟨c, ?_⟩
    ext r
    change (integerJetMatrix (fun e : BoundedIntegerExponent K h => MvPolynomial.monomial e.val 1)
      (integerAffineCube root D) rows *ᵥ c) r = _
    rw [integerJetMatrix_apply_coefficients]
    change booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root D t)
      (∑ e : BoundedIntegerExponent K h, MvPolynomial.C ((p o).coeff e.val) *
        MvPolynomial.monomial e.val 1)) (rows r) = _
    rw [boundedIntegerPolynomial_expansion (p o) h (hp o), hjet o]
    by_cases hro : r = o
    · subst r; simp
    · simp [hinj.eq_iff, hro]
  rintro y ⟨z, rfl⟩
  change a ^ h • z ∈ E.mulVecLin.range
  have hs : (∑ o, z o • (a ^ h • Pi.single o 1)) ∈ E.mulVecLin.range :=
    E.mulVecLin.range.sum_mem (fun o _ => E.mulVecLin.range.smul_mem (z o) (hunit o))
  convert hs using 1
  ext r
  simp [Pi.single_apply, mul_comm]

theorem boundedDegreeIntegerJetMatrix_index_le {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℕ) [NeZero a]
    (hperiod : integerScalarLattice α (a : ℤ) ≤ D.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range.toAddSubgroup.index ≤
      (a ^ h) ^ Fintype.card O := by
  have hp := boundedDegreeIntegerJetMatrix_period root D (a : ℤ) hperiod h rows hinj hdegree
  rw [← Nat.cast_pow] at hp
  exact residueLatticeImage_index_le _ (a ^ h) hp

theorem integerScalarLattice_pow_le {O : Type*} [Fintype O]
    (a : ℤ) {h s : ℕ} (hh : h ≤ s) :
    integerScalarLattice O (a ^ s) ≤ integerScalarLattice O (a ^ h) := by
  rintro y ⟨z, rfl⟩
  refine ⟨a ^ (s - h) • z, ?_⟩
  change a ^ h • (a ^ (s - h) • z) = a ^ s • z
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le hh]

theorem boundedDegreeIntegerJetMatrix_common_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (s h : ℕ) (hh : h ≤ s) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ s) ≤ (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range :=
  (integerScalarLattice_pow_le a hh).trans
    (boundedDegreeIntegerJetMatrix_period root D a hperiod h rows hinj hdegree)

theorem boundedDegreeIntegerJetMatrix_residue_iff {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℕ)
    (hperiod : integerScalarLattice α (a : ℤ) ≤ D.mulVecLin.range)
    (s h : ℕ) (hh : h ≤ s) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) (v : O → ℤ) :
    v ∈ (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range ↔
      ∃ x : BoundedIntegerExponent K h → ZMod (a ^ s),
        integerResidueMatrix (boundedDegreeIntegerJetMatrix root D h rows) (a ^ s) *ᵥ x =
          integerResidueMap O (a ^ s) v := by
  have hp := boundedDegreeIntegerJetMatrix_common_period root D (a : ℤ) hperiod s h hh rows hinj hdegree
  rw [← Nat.cast_pow] at hp
  exact integerMatrixImage_residue_iff _ (a ^ s) hp v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerAffineCube_residue_eq {α K : Type*}
    (root root' : K → ℤ) (D D' : Matrix α K ℤ) (m : ℕ)
    (hroot : integerResidueMap K m root = integerResidueMap K m root')
    (hD : integerResidueMatrix D m = integerResidueMatrix D' m) (t : Finset α) :
    integerResidueMap K m (integerAffineCube root D t) =
      integerResidueMap K m (integerAffineCube root' D' t) := by
  funext k
  change ((root k + ∑ r ∈ t, D r k : ℤ) : ZMod m) =
    ((root' k + ∑ r ∈ t, D' r k : ℤ) : ZMod m)
  push_cast
  have hk : (root k : ZMod m) = (root' k : ZMod m) := congrFun hroot k
  rw [hk]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact congrFun (congrFun hD r) k

theorem boundedDegreeIntegerJetMatrix_residue_eq {α K O : Type*}
    [DecidableEq α] [Fintype K]
    (root root' : K → ℤ) (D D' : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) (m : ℕ)
    (hroot : integerResidueMap K m root = integerResidueMap K m root')
    (hD : integerResidueMatrix D m = integerResidueMatrix D' m) :
    integerResidueMatrix (boundedDegreeIntegerJetMatrix root D h rows) m =
      integerResidueMatrix (boundedDegreeIntegerJetMatrix root' D' h rows) m := by
  apply integerJetMatrix_residue_eq
  intro o t _
  exact integerAffineCube_residue_eq root root' D D' m hroot hD t

theorem boundedDegreeIntegerJetMatrix_image_eq {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root root' : K → ℤ) (D D' : Matrix α K ℤ) (a : ℕ)
    (hperiod : integerScalarLattice α (a : ℤ) ≤ D.mulVecLin.range)
    (hperiod' : integerScalarLattice α (a : ℤ) ≤ D'.mulVecLin.range)
    (s h : ℕ) (hh : h ≤ s) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h)
    (hroot : integerResidueMap K (a ^ s) root = integerResidueMap K (a ^ s) root')
    (hD : integerResidueMatrix D (a ^ s) = integerResidueMatrix D' (a ^ s)) :
    (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range =
      (boundedDegreeIntegerJetMatrix root' D' h rows).mulVecLin.range := by
  have hp := boundedDegreeIntegerJetMatrix_common_period root D (a : ℤ) hperiod s h hh rows hinj hdegree
  have hp' := boundedDegreeIntegerJetMatrix_common_period root' D' (a : ℤ) hperiod' s h hh rows hinj hdegree
  rw [← Nat.cast_pow] at hp hp'
  exact integerMatrixImage_eq_of_residueMatrix _ _ (a ^ s) hp hp'
    (boundedDegreeIntegerJetMatrix_residue_eq root root' D D' h rows (a ^ s) hroot hD)

end Erdos3

end

end OAI
