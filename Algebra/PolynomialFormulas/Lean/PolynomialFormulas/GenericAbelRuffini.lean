import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Localization.FractionRing

/-!
# A polynomial of every degree whose every root is not solvable by radicals

For `n ≥ 5`, let `Lₙ = ℚ(x₀, ..., xₙ₋₁)` and let the symmetric group act by
permuting the variables.  Over the fixed field `Kₙ = Lₙ^{Sₙ}`, the orbit
polynomial of `x₀` has degree exactly `n`, splitting field `Lₙ`, and Galois
group `Sₙ`.  Irreducibility then turns the nonsolvability of `Sₙ` into a
rootwise statement: none of the polynomial's roots in `Lₙ` belongs to the
radical closure of `Kₙ`.

The coefficient field in this construction varies with `n`; it is the
symmetric rational-function field `Kₙ`, not `ℚ`.  The separate rational
coefficient theorem in `AbelRuffini.lean` has the usual universal-formula
scope and uses degree padding, so it deliberately makes only a complete-root
set obstruction.
-/

noncomputable section

open scoped Polynomial

namespace LeanProofs.PolynomialFormulas.GenericAbelRuffini

/-- The polynomial ring in `n` independent variables over `ℚ`. -/
abbrev A (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- The rational-function field in `n` independent variables over `ℚ`. -/
abbrev L (n : ℕ) := FractionRing (A n)

/-- The symmetric group on the `n` variables. -/
abbrev G (n : ℕ) := Equiv.Perm (Fin n)

/-- Permuting variables as a multiplicative homomorphism into ring
automorphisms. -/
def renameHom (n : ℕ) : G n →* (A n ≃+* A n) where
  toFun σ := (MvPolynomial.renameEquiv ℚ σ).toRingEquiv
  map_one' := by ext i; simp
  map_mul' σ τ := by ext i; simp

instance permActionA (n : ℕ) : MulSemiringAction (G n) (A n) :=
  MulSemiringAction.compHom (A n) (renameHom n)

@[simp]
lemma smul_X (n : ℕ) (σ : G n) (i : Fin n) :
    σ • (MvPolynomial.X i : A n) = MvPolynomial.X (σ i) := by
  change MvPolynomial.rename σ (MvPolynomial.X i) = _
  simp

instance permFaithfulA (n : ℕ) : FaithfulSMul (G n) (A n) := by
  constructor
  intro σ τ h
  ext i
  have hi := h (MvPolynomial.X i : A n)
  have hii : σ i = τ i := by simpa using hi
  exact congrArg Fin.val hii

local instance permActionL (n : ℕ) : MulSemiringAction (G n) (L n) :=
  IsFractionRing.mulSemiringAction (G n) (A n) (L n)

local instance permActionAL (n : ℕ) : SMulDistribClass (G n) (A n) (L n) :=
  IsFractionRing.smulDistribClass (G n) (A n) (L n)

local instance permFaithfulL (n : ℕ) : FaithfulSMul (G n) (L n) :=
  IsFractionRing.faithfulSMul (G n) (A n) (L n)

/-- The fixed field of the variable-permuting symmetric-group action. -/
abbrev K (n : ℕ) := FixedPoints.subfield (G n) (L n)

/-- The `i`th independent variable, embedded in the rational-function field. -/
def root (n : ℕ) (i : Fin n) : L n :=
  algebraMap (A n) (L n) (MvPolynomial.X i)

@[simp]
lemma smul_root (n : ℕ) (σ : G n) (i : Fin n) :
    σ • root n i = root n (σ i) := by
  simp [root, ← algebraMap.coe_smul']

/-- The orbit/minimal polynomial of the first independent variable over the
fixed field. -/
def p (n : ℕ) [NeZero n] : Polynomial (K n) :=
  FixedPoints.minpoly (G n) (L n) (root n 0)

lemma p_monic (n : ℕ) [NeZero n] : (p n).Monic :=
  FixedPoints.minpoly.monic (G n) (L n) (root n 0)

lemma p_irreducible (n : ℕ) [NeZero n] : Irreducible (p n) :=
  FixedPoints.minpoly.irreducible (G n) (L n) (root n 0)

lemma root_injective (n : ℕ) : Function.Injective (root n) := by
  intro i j hij
  have hX : (MvPolynomial.X i : A n) = MvPolynomial.X j :=
    IsFractionRing.injective (A n) (L n) hij
  exact MvPolynomial.X_injective hX

/-- Identify the independent variables with the orbit of the first one. -/
def rootsToOrbit (n : ℕ) [NeZero n] :
    Fin n → MulAction.orbit (G n) (root n 0) :=
  fun i => ⟨root n i, by
    rw [MulAction.mem_orbit_iff]
    exact ⟨Equiv.swap 0 i, by simp⟩⟩

lemma rootsToOrbit_bijective (n : ℕ) [NeZero n] :
    Function.Bijective (rootsToOrbit n) := by
  constructor
  · intro i j hij
    exact root_injective n (congrArg Subtype.val hij)
  · rintro ⟨z, ⟨σ, rfl⟩⟩
    exact ⟨σ 0, Subtype.ext (by simp [rootsToOrbit])⟩

def orbitEquivFin (n : ℕ) [NeZero n] :
    MulAction.orbit (G n) (root n 0) ≃ Fin n :=
  (Equiv.ofBijective (rootsToOrbit n) (rootsToOrbit_bijective n)).symm

lemma quotientStabilizer_card (n : ℕ) [NeZero n] :
    Nat.card (G n ⧸ MulAction.stabilizer (G n) (root n 0)) = n := by
  simpa using Nat.card_congr
    ((MulAction.orbitEquivQuotientStabilizer (G n) (root n 0)).symm.trans
      (orbitEquivFin n))

/-- The degree of an orbit polynomial is the index of the stabilizer.  This
small standalone lemma avoids repeatedly expanding the product proof. -/
lemma natDegree_prodXSubSMul (H S : Type*) [Group H] [Fintype H] [Field S]
    [MulSemiringAction H S] (x : S) :
    (prodXSubSMul H S x).natDegree =
      Nat.card (H ⧸ MulAction.stabilizer H x) := by
  classical
  unfold prodXSubSMul
  rw [Polynomial.natDegree_prod_of_monic]
  · simp [Nat.card_eq_fintype_card]
  · intro i _
    exact Polynomial.monic_X_sub_C _

lemma p_natDegree (n : ℕ) [NeZero n] : (p n).natDegree = n := by
  unfold p FixedPoints.minpoly
  rw [Polynomial.natDegree_toSubring]
  exact (natDegree_prodXSubSMul (G n) (L n) (root n 0)).trans
    (quotientStabilizer_card n)

lemma root_mem_rootSet (n : ℕ) [NeZero n] (i : Fin n) :
    root n i ∈ (p n).rootSet (L n) := by
  have h0 : root n 0 ∈ (p n).rootSet (L n) := by
    change root n 0 ∈
      (FixedPoints.minpoly (G n) (L n) (root n 0)).rootSet (L n)
    rw [(FixedPoints.minpoly.monic (G n) (L n) (root n 0)).mem_rootSet]
    exact FixedPoints.minpoly.eval₂' (G n) (L n) (root n 0)
  simpa using Polynomial.smul_mem_rootSet (f := p n) (Equiv.swap 0 i) h0

lemma p_splits (n : ℕ) [NeZero n] :
    ((p n).map (algebraMap (K n) (L n))).Splits := by
  unfold p
  rw [FixedPoints.minpoly_eq_minpoly]
  exact Normal.splits (inferInstance : Normal (K n) (L n)) (root n 0)

/-- The root set is nonvacuous and has exactly the requested cardinality. -/
lemma p_rootSet_card (n : ℕ) [NeZero n] :
    Fintype.card ((p n).rootSet (L n)) = n := by
  rw [Polynomial.card_rootSet_eq_natDegree (p_irreducible n).separable (p_splits n)]
  exact p_natDegree n

/-- Every embedded multivariate polynomial belongs to the field generated by
the independent-variable roots. -/
lemma algebraMap_mvPolynomial_mem_adjoin (n : ℕ) (q : A n) :
    algebraMap (A n) (L n) q ∈
      IntermediateField.adjoin (K n) (Set.range (root n)) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      have h := (IntermediateField.adjoin (K n) (Set.range (root n))).algebraMap_mem
        (algebraMap ℚ (K n) a)
      rw [MvPolynomial.C_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply ℚ (A n) (L n),
        IsScalarTower.algebraMap_apply ℚ (K n) (L n)]
      exact h
  | add q r hq hr =>
      simpa using
        (IntermediateField.adjoin (K n) (Set.range (root n))).add_mem hq hr
  | mul_X q i hq =>
      simpa only [map_mul, root] using
        (IntermediateField.adjoin (K n) (Set.range (root n))).mul_mem hq
          (IntermediateField.subset_adjoin (K n) _ (Set.mem_range_self i))

lemma adjoin_roots_eq_top (n : ℕ) :
    IntermediateField.adjoin (K n) (Set.range (root n)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨q, r, _, hqr⟩ := IsFractionRing.div_surjective (A n) z
  rw [← hqr]
  exact (IntermediateField.adjoin (K n) (Set.range (root n))).div_mem
    (algebraMap_mvPolynomial_mem_adjoin n q)
    (algebraMap_mvPolynomial_mem_adjoin n r)

instance p_isSplittingField (n : ℕ) [NeZero n] :
    Polynomial.IsSplittingField (K n) (L n) (p n) := by
  rw [isSplittingField_iff_intermediateField]
  refine ⟨p_splits n, ?_⟩
  apply top_unique
  rw [← adjoin_roots_eq_top n]
  exact IntermediateField.adjoin.mono (K n) _ _
    (Set.range_subset_iff.mpr (root_mem_rootSet n))

/-- The polynomial's Galois group is the full symmetric group. -/
def galEquivPerm (n : ℕ) [NeZero n] : (p n).Gal ≃* G n :=
  (AlgEquiv.autCongr (Polynomial.IsSplittingField.algEquiv (L n) (p n)).symm).trans
    (FixedPoints.toAlgAutMulEquiv (G n) (L n)).symm

theorem p_gal_not_solvable (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    ¬ IsSolvable (p n).Gal := by
  intro hsolv
  letI : IsSolvable (p n).Gal := hsolv
  have hperm : IsSolvable (G n) :=
    solvable_of_solvable_injective (f := (galEquivPerm n).symm.toMonoidHom)
      (galEquivPerm n).symm.injective
  exact (Equiv.Perm.not_solvable (Fin n)
    (by simpa [Cardinal.mk_fin] using hn)) hperm

/-- Rootwise Abel--Ruffini: every root in the splitting field is outside the
radical closure of the coefficient field. -/
theorem every_root_not_solvableByRad (n : ℕ) [NeZero n] (hn : 5 ≤ n)
    {x : L n} (hx : x ∈ (p n).rootSet (L n)) :
    x ∉ solvableByRad (K n) (L n) := by
  intro hxrad
  apply p_gal_not_solvable n hn
  exact isSolvable_gal_of_irreducible hxrad (p_irreducible n)
    (Polynomial.aeval_eq_zero_of_mem_rootSet hx)

/-- For every `n ≥ 5`, the concrete generic polynomial is monic of degree
`n`, has nonsolvable Galois group, and none of its roots in its splitting
field is solvable by radicals over its coefficient field. -/
theorem generic_unsolvable_polynomial (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    (p n).Monic ∧ (p n).natDegree = n ∧ ¬ IsSolvable (p n).Gal ∧
      Fintype.card ((p n).rootSet (L n)) = n ∧
        ∀ x : L n, x ∈ (p n).rootSet (L n) →
          x ∉ solvableByRad (K n) (L n) :=
  ⟨p_monic n, p_natDegree n, p_gal_not_solvable n hn,
    p_rootSet_card n, fun _ hx => every_root_not_solvableByRad n hn hx⟩

/-- The same result with only the natural hypothesis `4 < n`; the required
`NeZero n` instance is constructed internally. -/
theorem every_degree_gt_four_has_polynomial_with_no_radical_root
    (n : ℕ) (hn : 4 < n) :
    letI : NeZero n := ⟨by omega⟩
    (p n).Monic ∧ (p n).natDegree = n ∧
      Fintype.card ((p n).rootSet (L n)) = n ∧
        ∀ x : L n, x ∈ (p n).rootSet (L n) →
          x ∉ solvableByRad (K n) (L n) := by
  letI : NeZero n := ⟨by omega⟩
  exact ⟨p_monic n, p_natDegree n, p_rootSet_card n,
    fun _ hx => every_root_not_solvableByRad n (Nat.succ_le_iff.mpr hn) hx⟩

end LeanProofs.PolynomialFormulas.GenericAbelRuffini
