import PolynomialFormulas.LazardInvariantGradedReynolds
import PolynomialFormulas.LazardInvariantHomogeneousCoordinates
import PolynomialFormulas.LazardInvariantNonmodularBasis

/-!
# Lazard's invariant leading-term descent (Lemma 2)

This file states the leading-term lemma separately from the finite-free
conclusion of Theorem 2.  Normal forms are represented by their coordinates
in the Artin basis.  Lazard's order first compares total degree in the root
variables and, only at equal root degree, compares the elementary-symmetric
(`e`) part.  Consequently the following coordinate condition is a
tie-breaking-independent, slightly stronger form of the paper's condition:

* all Artin rows above degree `d` vanish;
* every coefficient in row `d` is a ground-field constant; and
* at least one coefficient in row `d` is nonzero.

It follows that the leading monomial of the normal form has no `e` part.
The nonzero clause is essential: merely proving that the degree-`d` block is
constant would be vacuous when that whole block vanishes.

The proof of the nonzero clause does not inspect the implementation of the
graded block induction.  A homogeneous invariant basis vector is unimodular:
its basis-coordinate functional, precomposed with Reynolds averaging, takes
the value `1` on it.  If every highest possible Artin coefficient vanished,
all its Artin coefficients would have zero constant term, and no
symmetric-linear functional could take value `1`.  This is exactly the
leading-term descent argument hidden in Lazard's prose proof.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantLeadingTermDescent

open scoped BigOperators
open Finset MvPolynomial

set_option autoImplicit false

noncomputable section

open LazardInvariantModule
open LazardInvariantArtinBasis
open LazardInvariantArtinModuleBasis
open LazardInvariantHomogeneousCoordinates
open LazardInvariantGradedReynolds
open LazardInvariantModularCounterexample

variable (K : Type*) [Field K]
variable (n : ℕ)
variable (H : Subgroup (Equiv.Perm (Fin n))) [Fintype H]

/-- Compatibility instance for the historical characteristic-zero API.
The core proof below asks only for the sharp nonvanishing hypothesis; in
characteristic zero that fact is derived automatically. -/
instance cardNeZeroFact_of_charZero [CharZero K] :
    Fact ((Fintype.card H : K) ≠ 0) := ⟨by
  exact_mod_cast Fintype.card_ne_zero⟩

/-- Constant-term evaluation on the elementary-symmetric coefficient ring.
This is the formal operation "put every `e_i` equal to zero". -/
def symmetricConstantCoeff : SymmetricRing K (Fin n) →+* K :=
  (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).comp
    (Subalgebra.val (SymmetricRing K (Fin n))).toRingHom

@[simp]
theorem symmetricConstantCoeff_apply (c : SymmetricRing K (Fin n)) :
    symmetricConstantCoeff K n c = MvPolynomial.constantCoeff c.1 :=
  rfl

/-- The exact Artin-coordinate form of "the leading monomial after reduction
by `J` is independent of the `e_i`".  It is stronger only in an inessential
way: every term in the highest root-degree block, rather than merely the
tie-broken leading one, is required to have constant `e` coefficient. -/
structure PaperLeadingNormalForm (p : PolynomialRing K (Fin n))
    (d : ℕ) : Prop where
  above_zero : ∀ a : ArtinIndex n, d < artinDegree a →
    (symmetricArtinBasis K n).repr p a = 0
  top_constant : ∀ a : ArtinIndex n, artinDegree a = d →
    ∃ r : K, (symmetricArtinBasis K n).repr p a =
      algebraMap K (SymmetricRing K (Fin n)) r
  top_nonzero : ∃ a : ArtinIndex n, artinDegree a = d ∧
    (symmetricArtinBasis K n).repr p a ≠ 0

/-- Positive-degree homogeneous symmetric coefficients have zero constant
term. -/
lemma symmetricConstantCoeff_eq_zero_of_isHomogeneous_pos
    {c : SymmetricRing K (Fin n)} {d : ℕ}
    (hc : IsHomogeneous c.1 d) (hd : 0 < d) :
    symmetricConstantCoeff K n c = 0 := by
  rw [symmetricConstantCoeff_apply]
  exact hc.coeff_eq_zero (by
    simpa using (ne_of_lt hd))

/-- Homogeneous degree-zero symmetric coefficients really are scalars from
the ground field. -/
lemma eq_algebraMap_of_isHomogeneous_zero
    {c : SymmetricRing K (Fin n)} (hc : IsHomogeneous c.1 0) :
    ∃ r : K, c = algebraMap K (SymmetricRing K (Fin n)) r := by
  have hdegree : c.1.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin n)).2 hc
  have hr : c.1 = MvPolynomial.C (MvPolynomial.coeff 0 c.1) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := c.1)).1 hdegree
  refine ⟨MvPolynomial.coeff 0 c.1, Subtype.ext ?_⟩
  simpa [MvPolynomial.algebraMap_eq] using hr

section ArbitraryHomogeneousInvariantBasis

variable (B : HomogeneousInvariantBasis K (Fin n) H (lazardDegreeBound n))
variable [hcard : Fact ((Fintype.card H : K) ≠ 0)]

local instance averageCardInvertible :
    Invertible (Fintype.card H : SymmetricRing K (Fin n)) :=
  symmetricCardInvertibleOfNeZero K n H hcard.out

/-- Reynolds averaging with its codomain restricted to the invariant
submodule. -/
def averageToInvariants : PolynomialRing K (Fin n) →ₗ[SymmetricRing K (Fin n)]
    (subgroupRepresentation K (Fin n) H).invariants :=
  (subgroupRepresentation K (Fin n) H).averageMap.codRestrict
    (subgroupRepresentation K (Fin n) H).invariants
    (fun p => reynolds_mem_invariants K (Fin n) H p)

@[simp]
theorem averageToInvariants_of_invariant
    (p : (subgroupRepresentation K (Fin n) H).invariants) :
    averageToInvariants K n H p.1 = p := by
  apply Subtype.ext
  exact reynolds_eq_self_of_invariant K (Fin n) H p.1 p.2

/-- A basis vector of the invariant module admits a symmetric-linear
functional on the ambient polynomial ring which takes value one on it. -/
def ambientGeneratorCoordinate (g : B.Index) :
    PolynomialRing K (Fin n) →ₗ[SymmetricRing K (Fin n)]
      SymmetricRing K (Fin n) :=
  (B.basis.coord g).comp (averageToInvariants K n H)

@[simp]
theorem ambientGeneratorCoordinate_self (g : B.Index) :
    ambientGeneratorCoordinate K n H B g (B.basis g).1 = 1 := by
  simp [ambientGeneratorCoordinate]

/-- If all Artin coordinates of a polynomial have zero constant term, every
symmetric-linear functional has zero constant term on that polynomial. -/
lemma constantCoeff_linearMap_eq_zero
    (p : PolynomialRing K (Fin n)) (hp : ∀ a : ArtinIndex n,
      symmetricConstantCoeff K n ((symmetricArtinBasis K n).repr p a) = 0)
    (φ : PolynomialRing K (Fin n) →ₗ[SymmetricRing K (Fin n)]
      SymmetricRing K (Fin n)) :
    symmetricConstantCoeff K n (φ p) = 0 := by
  classical
  rw [← (symmetricArtinBasis K n).linearCombination_repr p,
    Finsupp.linearCombination_apply]
  simp only [map_finsuppSum, map_smul, Algebra.smul_def, map_mul]
  calc
    ((symmetricArtinBasis K n).repr p).sum (fun a b =>
        MvPolynomial.constantCoeff b.1 *
          MvPolynomial.constantCoeff
            (φ (symmetricArtinBasis K n a)).1) =
        ((symmetricArtinBasis K n).repr p).sum (fun _ _ => (0 : K)) := by
      apply Finsupp.sum_congr
      intro a ha
      rw [← symmetricConstantCoeff_apply K n, hp a, zero_mul]
    _ = 0 := by simp

/-- A homogeneous invariant basis generator has a nonzero Artin coordinate
in its own degree.  This is the step that prevents a vacuous "constant top
block" certificate. -/
theorem exists_nonzero_artinCoordinate_at_generatorDegree (g : B.Index) :
    ∃ a : ArtinIndex n,
      artinDegree a = B.degree g ∧
        (symmetricArtinBasis K n).repr (B.basis g).1 a ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hall : ∀ a : ArtinIndex n,
      symmetricConstantCoeff K n
        ((symmetricArtinBasis K n).repr (B.basis g).1 a) = 0 := by
    intro a
    by_cases hgt : B.degree g < artinDegree a
    · have hz : (symmetricArtinBasis K n).repr (B.basis g).1 a = 0 :=
        repr_eq_zero_of_degree_lt (symmetricArtinBasis K n) artinDegree
          (symmetricArtinBasis_isHomogeneous K n)
          (B.basis_homogeneous g) a hgt
      rw [hz]
      exact map_zero _
    · have hle : artinDegree a ≤ B.degree g := Nat.le_of_not_gt hgt
      by_cases heq : artinDegree a = B.degree g
      · rw [hnone a heq]
        exact map_zero _
      · have hlt : artinDegree a < B.degree g := lt_of_le_of_ne hle heq
        have hc := repr_isHomogeneous (symmetricArtinBasis K n) artinDegree
          (symmetricArtinBasis_isHomogeneous K n)
          (B.basis_homogeneous g) a hle
        exact symmetricConstantCoeff_eq_zero_of_isHomogeneous_pos K n hc
          (Nat.sub_pos_of_lt hlt)
  let φ := ambientGeneratorCoordinate K n H B g
  have hzero := constantCoeff_linearMap_eq_zero K n (B.basis g).1 hall φ
  have hone : symmetricConstantCoeff K n (φ (B.basis g).1) = 1 := by
    rw [ambientGeneratorCoordinate_self]
    exact map_one _
  exact one_ne_zero (hone.symm.trans hzero)

/-- Every homogeneous invariant basis generator satisfies Lazard's literal
leading-normal-form condition. -/
theorem basis_generator_has_paperLeadingNormalForm (g : B.Index) :
    PaperLeadingNormalForm K n (B.basis g).1 (B.degree g) where
  above_zero a ha :=
    repr_eq_zero_of_degree_lt (symmetricArtinBasis K n) artinDegree
      (symmetricArtinBasis_isHomogeneous K n)
      (B.basis_homogeneous g) a ha
  top_constant a ha := by
    have hle : artinDegree a ≤ B.degree g := ha.le
    have hc := repr_isHomogeneous (symmetricArtinBasis K n) artinDegree
      (symmetricArtinBasis_isHomogeneous K n)
      (B.basis_homogeneous g) a hle
    have hzero : B.degree g - artinDegree a = 0 := by omega
    rw [hzero] at hc
    exact eq_algebraMap_of_isHomogeneous_zero K n hc
  top_nonzero :=
    exists_nonzero_artinCoordinate_at_generatorDegree K n H B g

end ArbitraryHomogeneousInvariantBasis

/-- A packaged, exact statement of Lazard's Lemma 2.  The stored basis gives
the claimed generation over `K[e₁,…,eₙ]`; `leadingNormalForm` proves that
each generator's reduced Artin normal form has `e`-independent leading
monomial. -/
structure PaperLemmaTwoBasis where
  Index : Type
  indexFintype : Fintype Index
  basis : Module.Basis Index (SymmetricRing K (Fin n))
    (subgroupRepresentation K (Fin n) H).invariants
  degree : Index → ℕ
  degree_le : ∀ i, degree i ≤ lazardDegreeBound n
  homogeneous : ∀ i, IsHomogeneous (basis i).1 (degree i)
  leadingNormalForm : ∀ i,
    PaperLeadingNormalForm K n (basis i).1 (degree i)

/-- Sharp nonmodular form of Lazard's Lemma 2.  Nonvanishing of the subgroup
order in the field is exactly the hypothesis needed by Reynolds averaging.
The homogeneous invariant basis and every leading-normal-form certificate are
constructed internally. -/
theorem lazardLemmaTwo_of_card_ne_zero
    (hcard : (Fintype.card H : K) ≠ 0) :
    Nonempty (PaperLemmaTwoBasis K n H) := by
  letI : Fact ((Fintype.card H : K) ≠ 0) := ⟨hcard⟩
  let B := lazardHomogeneousInvariantBasis_of_card_ne_zero_fact K n H
  exact ⟨
    { Index := B.Index
      indexFintype := B.indexFintype
      basis := B.basis
      degree := B.degree
      degree_le := B.degree_le
      homogeneous := B.basis_homogeneous
      leadingNormalForm :=
        basis_generator_has_paperLeadingNormalForm K n H B }⟩

/-- Characteristic zero is a convenient sufficient wrapper for the sharp
subgroup-order hypothesis.  No normal-form or leading-term certificate is
supplied by the caller. -/
theorem lazardLemmaTwo [CharZero K] :
    Nonempty (PaperLemmaTwoBasis K n H) := by
  apply lazardLemmaTwo_of_card_ne_zero K n H
  exact_mod_cast Fintype.card_ne_zero

end

end LeanProofs.PolynomialFormulas.LazardInvariantLeadingTermDescent
