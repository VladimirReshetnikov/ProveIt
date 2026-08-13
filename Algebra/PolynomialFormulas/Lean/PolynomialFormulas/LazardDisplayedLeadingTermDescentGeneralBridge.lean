import PolynomialFormulas.LazardDisplayedGroebnerGeneralOrder
import PolynomialFormulas.LazardInvariantLeadingTermDescent
import PolynomialFormulas.LazardInvariantNonmodularBasis

/-!
# Arbitrary-degree combined-ring form of Lazard's leading-term descent

`LazardInvariantLeadingTermDescent` produces an intrinsic Artin-coordinate
certificate in every degree.  This file realizes those coordinates in the
literal nested ring `K[e][x]`, flattens that ring to `K[x,e]`, and proves the
claim about the *actual* leading exponent for every paper order.

The action orientation here is the identity orientation.  Both the intrinsic
basis and the general displayed construction use
`LazardInvariantArtinBasis.artinExponent` on the same `Fin n` root variables;
there is no hidden reversal or subgroup conjugation.  (The separate historical
quintic display does reverse its roots and therefore needs its explicit
conjugation bridge.)

The resulting theorem uses only root-degree primacy.  Lazard's further
equal-root-degree comparison of the formal `e` block is unnecessary after the
stronger homogeneous certificate has shown that every monomial in the entire
top root-degree row is `e`-free.
-/

namespace LeanProofs.PolynomialFormulas.LazardDisplayedLeadingTermDescentGeneralBridge

open scoped BigOperators MonomialOrder
open Finset MvPolynomial

set_option autoImplicit false

noncomputable section

/- Lean 4.32 does not accept `namespace X := Long.Namespace` as a
namespace alias.  Re-export exactly the names used below into local shim
namespaces instead. -/
namespace GO
export LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerGeneralOrder
  (Combined Exponent IsStandard LiteralTopRowConstant
    PaperLemmaTwoOrderHypotheses PaperOrderHypotheses Variable
    actualLeadingExponent_rootDegree_eq_and_coefficientPart_eq_zero
    coeff_coeff_unflatten coeff_realizeFormalCoordinates coefficientEquiv
    coefficientPart combinedSpecialization
    combinedSpecialization_injective_on_standard flatten
    isStandard_iff_root_bounds nestedSpecialization
    nestedSpecialization_realizeFormalCoordinates realizeCoordinates
    realizeFormalCoordinates rootDegree rootPart unflatten unflatten_flatten)

namespace GeneralIdeal
export LeanProofs.PolynomialFormulas.LazardDisplayedGroebnerGeneralOrder.GeneralIdeal
  (Ambient Coeff)
end GeneralIdeal
end GO

namespace Modular
export LeanProofs.PolynomialFormulas.LazardInvariantModularCounterexample
  (lazardHomogeneousInvariantBasis_of_card_ne_zero_fact)
end Modular

open LazardInvariantModule
open LazardInvariantArtinBasis
open LazardInvariantArtinModuleBasis
open LazardInvariantGradedReynolds
open LazardInvariantLeadingTermDescent

variable (K : Type*) [Field K]
variable (n : ℕ)

/-- Transport the intrinsic symmetric Artin coordinate back to the formal
polynomial ring on `e₁,…,eₙ`. -/
def intrinsicFormalCoordinates (p : MvPolynomial (Fin n) K)
    (a : ArtinIndex n) : GO.GeneralIdeal.Coeff K n :=
  (GO.coefficientEquiv K n).symm
    ((symmetricArtinBasis K n).repr p a)

/-- Reassemble the intrinsic coordinates as the literal nested normal form
`K[e][x]`. -/
def canonicalNestedNormalForm (p : MvPolynomial (Fin n) K) :
    GO.GeneralIdeal.Ambient K n :=
  GO.realizeFormalCoordinates K n (intrinsicFormalCoordinates K n p)

/-- The same canonical normal form in the literal combined ring `K[x,e]`. -/
def canonicalCombinedNormalForm (p : MvPolynomial (Fin n) K) :
    GO.Combined K n :=
  GO.flatten K n (canonicalNestedNormalForm K n p)

@[simp]
theorem coefficientEquiv_intrinsicFormalCoordinates
    (p : MvPolynomial (Fin n) K) (a : ArtinIndex n) :
    GO.coefficientEquiv K n (intrinsicFormalCoordinates K n p a) =
      (symmetricArtinBasis K n).repr p a :=
  (GO.coefficientEquiv K n).apply_symm_apply _

/-- Ground-field scalars have the expected literal formal representative. -/
@[simp]
theorem coefficientEquiv_symm_algebraMap (r : K) :
    (GO.coefficientEquiv K n).symm
        (algebraMap K (MvPolynomial.symmetricSubalgebra (Fin n) K) r) =
      MvPolynomial.C r := by
  apply (GO.coefficientEquiv K n).injective
  rw [(GO.coefficientEquiv K n).apply_symm_apply]
  simpa [MvPolynomial.algebraMap_eq] using
    ((GO.coefficientEquiv K n).commutes r).symm

theorem intrinsicFormalCoordinates_above_zero
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d)
    (a : ArtinIndex n) (ha : d < artinDegree a) :
    intrinsicFormalCoordinates K n p a = 0 := by
  apply (GO.coefficientEquiv K n).injective
  rw [coefficientEquiv_intrinsicFormalCoordinates, map_zero]
  exact h.above_zero a ha

theorem intrinsicFormalCoordinates_top_constant
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d)
    (a : ArtinIndex n) (ha : artinDegree a = d) :
    ∃ r : K, intrinsicFormalCoordinates K n p a = MvPolynomial.C r := by
  obtain ⟨r, hr⟩ := h.top_constant a ha
  refine ⟨r, ?_⟩
  rw [intrinsicFormalCoordinates, hr,
    coefficientEquiv_symm_algebraMap]

theorem intrinsicFormalCoordinates_top_nonzero
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d) :
    ∃ a : ArtinIndex n, artinDegree a = d ∧
      intrinsicFormalCoordinates K n p a ≠ 0 := by
  obtain ⟨a, ha, hne⟩ := h.top_nonzero
  refine ⟨a, ha, ?_⟩
  intro hzero
  apply hne
  have hmapped := congrArg (GO.coefficientEquiv K n) hzero
  simpa using hmapped

/-- Every outer/root support exponent of the canonical nested normal form is
an Artin staircase exponent. -/
theorem canonicalNestedNormalForm_support_witness
    {p : MvPolynomial (Fin n) K} {u : Fin n →₀ ℕ}
    (hu : u ∈ (canonicalNestedNormalForm K n p).support) :
    ∃ a : ArtinIndex n, u = artinExponent a := by
  classical
  rw [canonicalNestedNormalForm, GO.realizeFormalCoordinates] at hu
  have hsum := MvPolynomial.support_sum hu
  rcases Finset.mem_biUnion.mp hsum with ⟨a, _, ha⟩
  have hsingle := MvPolynomial.support_monomial_subset ha
  exact ⟨a, Finset.mem_singleton.mp hsingle⟩

/-- Rows above `d` vanish as literal outer coefficients of the nested normal
form. -/
theorem canonicalNestedNormalForm_coeff_above_zero
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d)
    (a : ArtinIndex n) (ha : d < artinDegree a) :
    MvPolynomial.coeff (artinExponent a)
        (canonicalNestedNormalForm K n p) = 0 := by
  rw [canonicalNestedNormalForm, GO.coeff_realizeFormalCoordinates,
    intrinsicFormalCoordinates_above_zero K n h a ha, mul_zero]

/-- Every literal outer coefficient in the top Artin row is a constant
formal polynomial; the Artin sign is absorbed into its scalar. -/
theorem canonicalNestedNormalForm_coeff_top_constant
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d)
    (a : ArtinIndex n) (ha : artinDegree a = d) :
    ∃ r : K,
      MvPolynomial.coeff (artinExponent a)
          (canonicalNestedNormalForm K n p) = MvPolynomial.C r := by
  obtain ⟨r, hr⟩ :=
    intrinsicFormalCoordinates_top_constant K n h a ha
  refine ⟨((-1 : K) ^ d) * r, ?_⟩
  rw [canonicalNestedNormalForm, GO.coeff_realizeFormalCoordinates,
    ha, hr]
  simpa using
    (map_mul (MvPolynomial.C : K →+* GO.GeneralIdeal.Coeff K n)
      ((-1 : K) ^ d) r).symm

/-- Some literal outer coefficient in the top row is nonzero. -/
theorem canonicalNestedNormalForm_coeff_top_nonzero
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d) :
    ∃ a : ArtinIndex n, artinDegree a = d ∧
      MvPolynomial.coeff (artinExponent a)
        (canonicalNestedNormalForm K n p) ≠ 0 := by
  obtain ⟨a, ha, hcoordinate⟩ :=
    intrinsicFormalCoordinates_top_nonzero K n h
  refine ⟨a, ha, ?_⟩
  rw [canonicalNestedNormalForm, GO.coeff_realizeFormalCoordinates]
  exact mul_ne_zero
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hcoordinate

/-- A combined support monomial remembers both an Artin outer exponent and
an actually supported exponent in its formal coefficient. -/
theorem canonicalCombinedNormalForm_support_witness
    {p : MvPolynomial (Fin n) K} {z : GO.Exponent n}
    (hz : z ∈ (canonicalCombinedNormalForm K n p).support) :
    ∃ a : ArtinIndex n,
      GO.rootPart n z = artinExponent a ∧
      MvPolynomial.coeff (GO.coefficientPart n z)
        (MvPolynomial.coeff (artinExponent a)
          (canonicalNestedNormalForm K n p)) ≠ 0 := by
  let u := GO.rootPart n z
  let v := GO.coefficientPart n z
  have hsplit : u.sumElim v = z :=
    Finsupp.comapDomain_sumElim_comapDomain z
  have hcoefficient :
      MvPolynomial.coeff v
          (MvPolynomial.coeff u (canonicalNestedNormalForm K n p)) =
        MvPolynomial.coeff z (canonicalCombinedNormalForm K n p) := by
    calc
      MvPolynomial.coeff v
          (MvPolynomial.coeff u (canonicalNestedNormalForm K n p)) =
          MvPolynomial.coeff v
            (MvPolynomial.coeff u
              (GO.unflatten K n (canonicalCombinedNormalForm K n p))) := by
                simp [canonicalCombinedNormalForm]
      _ = MvPolynomial.coeff (u.sumElim v)
          (canonicalCombinedNormalForm K n p) :=
            GO.coeff_coeff_unflatten K n _ u v
      _ = MvPolynomial.coeff z (canonicalCombinedNormalForm K n p) := by
            rw [hsplit]
  have hinner : MvPolynomial.coeff v
      (MvPolynomial.coeff u (canonicalNestedNormalForm K n p)) ≠ 0 := by
    rw [hcoefficient]
    exact MvPolynomial.mem_support_iff.mp hz
  have houter :
      u ∈ (canonicalNestedNormalForm K n p).support := by
    rw [MvPolynomial.mem_support_iff]
    intro hzero
    apply hinner
    rw [hzero]
    simp
  obtain ⟨a, hua⟩ :=
    canonicalNestedNormalForm_support_witness K n houter
  refine ⟨a, ?_, ?_⟩
  · simpa [u] using hua
  · simpa [v, hua] using hinner

/-! ## The literal displayed normal form, not merely its top row -/

/-- Evaluating the intrinsic formal coordinates in the symmetric Artin basis
recovers the original root polynomial.  This is the general-degree analogue
of the fixed-quintic `realize_normalCoordinates` theorem. -/
theorem realizeCoordinates_intrinsicFormalCoordinates
    (p : MvPolynomial (Fin n) K) :
    GO.realizeCoordinates K n (intrinsicFormalCoordinates K n p) = p := by
  rw [GO.realizeCoordinates]
  rw [show
    (fun a => GO.coefficientEquiv K n
      (intrinsicFormalCoordinates K n p a)) =
        (symmetricArtinBasis K n).equivFun p by
      funext a
      simp [intrinsicFormalCoordinates, Module.Basis.equivFun_apply]]
  exact (symmetricArtinBasis K n).equivFun.symm_apply_apply p

/-- The combined representative really is supported on the Artin staircase,
so it is standard for the literal displayed leading powers. -/
theorem canonicalCombinedNormalForm_isStandard
    (p : MvPolynomial (Fin n) K) :
    GO.IsStandard K n (canonicalCombinedNormalForm K n p) := by
  rw [GO.isStandard_iff_root_bounds]
  intro z hz i
  obtain ⟨a, hroot, _⟩ :=
    canonicalCombinedNormalForm_support_witness K n hz
  have hcoordinate := congrArg (fun u : Fin n →₀ ℕ => u i) hroot
  have hzi : z (Sum.inl i) = (a i).1 := by
    simpa [GO.rootPart, artinExponent_apply] using hcoordinate
  rw [hzi]
  exact (a i).isLt

/-- Elementary-symmetric specialization of the literal combined normal form
is the root polynomial from which its coordinates were obtained. -/
@[simp]
theorem combinedSpecialization_canonicalCombinedNormalForm
    (p : MvPolynomial (Fin n) K) :
    GO.combinedSpecialization K n (canonicalCombinedNormalForm K n p) = p := by
  change GO.nestedSpecialization K n
      (GO.unflatten K n (canonicalCombinedNormalForm K n p)) = p
  rw [canonicalCombinedNormalForm, GO.unflatten_flatten,
    canonicalNestedNormalForm,
    GO.nestedSpecialization_realizeFormalCoordinates,
    realizeCoordinates_intrinsicFormalCoordinates]

/-- Thus the displayed representative is the unique standard polynomial
specializing to `p`.  This closes the logical step hidden by the informal
phrase "after reduction by `J`": the theorem is not only about a convenient
coordinate expansion with the right top row. -/
theorem canonicalCombinedNormalForm_unique
    (p : MvPolynomial (Fin n) K) (s : GO.Combined K n)
    (hs : GO.IsStandard K n s)
    (hspecializes : GO.combinedSpecialization K n s = p) :
    s = canonicalCombinedNormalForm K n p := by
  apply GO.combinedSpecialization_injective_on_standard K n hs
    (canonicalCombinedNormalForm_isStandard K n p)
  exact hspecializes.trans
    (combinedSpecialization_canonicalCombinedNormalForm K n p).symm

/-- Exact literal normal-form package corresponding to the intrinsic
three-row certificate.  Standardness, specialization, and uniqueness are
derived here; the caller supplies only the intrinsic theorem's hypothesis. -/
structure LiteralDisplayedPaperLeadingNormalForm
    (p : MvPolynomial (Fin n) K) (d : ℕ) : Prop where
  standard : GO.IsStandard K n (canonicalCombinedNormalForm K n p)
  specializes :
    GO.combinedSpecialization K n (canonicalCombinedNormalForm K n p) = p
  unique : ∀ s : GO.Combined K n, GO.IsStandard K n s →
    GO.combinedSpecialization K n s = p →
      s = canonicalCombinedNormalForm K n p
  topRowConstant :
    GO.LiteralTopRowConstant K n (canonicalCombinedNormalForm K n p) d

/-- The intrinsic three-row certificate becomes the order-free literal
combined-support certificate. -/
theorem literalTopRowConstant_canonicalCombinedNormalForm
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d) :
    GO.LiteralTopRowConstant K n (canonicalCombinedNormalForm K n p) d where
  rootDegree_le z hz := by
    obtain ⟨a, hroot, hinner⟩ :=
      canonicalCombinedNormalForm_support_witness K n hz
    have hdegree : GO.rootDegree n z = artinDegree a := by
      rw [GO.rootDegree, hroot, artinExponent_degree]
    rw [hdegree]
    apply Nat.le_of_not_gt
    intro habove
    apply hinner
    rw [canonicalNestedNormalForm_coeff_above_zero K n h a habove]
    simp
  top_exists := by
    obtain ⟨a, ha, houter⟩ :=
      canonicalNestedNormalForm_coeff_top_nonzero K n h
    obtain ⟨r, hr⟩ :=
      canonicalNestedNormalForm_coeff_top_constant K n h a ha
    have hr0 : r ≠ 0 := by
      intro hzero
      apply houter
      rw [hr, hzero, map_zero]
    refine ⟨(artinExponent a).sumElim (0 : Fin n →₀ ℕ), ?_, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff,
        ← GO.coeff_coeff_unflatten K n,
        canonicalCombinedNormalForm, GO.unflatten_flatten, hr]
      simpa using hr0
    · simp [GO.rootDegree, artinExponent_degree, ha]
    · simp
  top_coefficientPart_zero z hz hzdegree := by
    obtain ⟨a, hroot, hinner⟩ :=
      canonicalCombinedNormalForm_support_witness K n hz
    have hdegree : GO.rootDegree n z = artinDegree a := by
      rw [GO.rootDegree, hroot, artinExponent_degree]
    have ha : artinDegree a = d := hdegree.symm.trans hzdegree
    obtain ⟨r, hr⟩ :=
      canonicalNestedNormalForm_coeff_top_constant K n h a ha
    by_contra hformal
    apply hinner
    rw [hr, MvPolynomial.coeff_C_of_ne_zero hformal]

/-- Intrinsic leading-term descent gives the complete literal displayed
normal-form package.  No standardness, congruence, uniqueness, or top-row
certificate is accepted as an extra argument. -/
theorem literalDisplayedPaperLeadingNormalForm_of_paperLeadingNormalForm
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d) :
    LiteralDisplayedPaperLeadingNormalForm K n p d where
  standard := canonicalCombinedNormalForm_isStandard K n p
  specializes := combinedSpecialization_canonicalCombinedNormalForm K n p
  unique := canonicalCombinedNormalForm_unique K n p
  topRowConstant := literalTopRowConstant_canonicalCombinedNormalForm K n h

/-- Exact arbitrary-degree version of Lazard's Lemma-2 leading-monomial
sentence: the `MonomialOrder.degree` of the literal combined normal form has
root degree `d` and zero formal-`e` block. -/
theorem actualLeadingExponent_canonicalCombinedNormalForm
    {m : MonomialOrder (GO.Variable n)}
    (hm : GO.PaperOrderHypotheses n m)
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d) :
    GO.rootDegree n (m.degree (canonicalCombinedNormalForm K n p)) = d ∧
      GO.coefficientPart n
        (m.degree (canonicalCombinedNormalForm K n p)) = 0 :=
  GO.actualLeadingExponent_rootDegree_eq_and_coefficientPart_eq_zero
    K n hm (literalTopRowConstant_canonicalCombinedNormalForm K n h)

/-- The same result under Lazard's full Lemma-2 block-order hypothesis,
including formal-`e` priority at equal root degree. -/
theorem actualLeadingExponent_canonicalCombinedNormalForm_paperBlockOrder
    {m : MonomialOrder (GO.Variable n)}
    (hm : GO.PaperLemmaTwoOrderHypotheses n m)
    {p : MvPolynomial (Fin n) K} {d : ℕ}
    (h : PaperLeadingNormalForm K n p d) :
    GO.rootDegree n (m.degree (canonicalCombinedNormalForm K n p)) = d ∧
      GO.coefficientPart n
        (m.degree (canonicalCombinedNormalForm K n p)) = 0 :=
  actualLeadingExponent_canonicalCombinedNormalForm K n
    hm.toPaperOrderHypotheses h

section CharacteristicZeroEndpoints

variable [CharZero K]
variable (H : Subgroup (Equiv.Perm (Fin n))) [Fintype H]

/-- No certificate is supplied by a caller: each generator of Lazard's
canonical homogeneous invariant basis has the literal actual-leading-term
property in the identity root-variable orientation. -/
theorem lazardHomogeneousInvariantBasis_actualLeadingExponent :
    let B := lazardHomogeneousInvariantBasis K n H
    ∀ (g : B.Index) (m : MonomialOrder (GO.Variable n)),
      GO.PaperOrderHypotheses n m →
      GO.rootDegree n
          (m.degree (canonicalCombinedNormalForm K n (B.basis g).1)) =
            B.degree g ∧
        GO.coefficientPart n
          (m.degree (canonicalCombinedNormalForm K n (B.basis g).1)) = 0 := by
  dsimp only
  intro g m hm
  exact actualLeadingExponent_canonicalCombinedNormalForm K n hm
    (basis_generator_has_paperLeadingNormalForm K n H
      (lazardHomogeneousInvariantBasis K n H) g)

/-- Every member of the internally constructed finite homogeneous invariant
basis has the complete literal displayed normal-form package.  Since `B.basis`
is a `Module.Basis`, generation over the symmetric coefficient ring is part
of the same object rather than a caller-supplied spanning certificate. -/
theorem lazardHomogeneousInvariantBasis_literalDisplayedPackage :
    let B := lazardHomogeneousInvariantBasis K n H
    ∀ g : B.Index,
      LiteralDisplayedPaperLeadingNormalForm K n (B.basis g).1 (B.degree g) := by
  dsimp only
  intro g
  exact literalDisplayedPaperLeadingNormalForm_of_paperLeadingNormalForm K n
    (basis_generator_has_paperLeadingNormalForm K n H
      (lazardHomogeneousInvariantBasis K n H) g)

/-- Generator-level corollary under the paper's complete Lemma-2 block-order
hypothesis, including formal-`e` priority at equal root degree. -/
theorem lazardHomogeneousInvariantBasis_actualLeadingExponent_paperBlockOrder :
    let B := lazardHomogeneousInvariantBasis K n H
    ∀ (g : B.Index) (m : MonomialOrder (GO.Variable n)),
      GO.PaperLemmaTwoOrderHypotheses n m →
      GO.rootDegree n
          (m.degree (canonicalCombinedNormalForm K n (B.basis g).1)) =
            B.degree g ∧
        GO.coefficientPart n
          (m.degree (canonicalCombinedNormalForm K n (B.basis g).1)) = 0 := by
  dsimp only
  intro g m hm
  exact actualLeadingExponent_canonicalCombinedNormalForm_paperBlockOrder
    K n hm
    (basis_generator_has_paperLeadingNormalForm K n H
      (lazardHomogeneousInvariantBasis K n H) g)

/-- Full corrected Lemma-2 endpoint for a chosen complete paper block order.
The finite module basis itself supplies generation; this theorem records, for
each of its generators, the uniform degree bound, homogeneity, unique literal
displayed normal form, and actual formal-`e`-free leading monomial. -/
theorem lazardHomogeneousInvariantBasis_literalPaperLemmaTwo_for_paperBlockOrder
    (m : MonomialOrder (GO.Variable n))
    (hm : GO.PaperLemmaTwoOrderHypotheses n m) :
    let B := lazardHomogeneousInvariantBasis K n H
    ∀ g : B.Index,
      B.degree g ≤ lazardDegreeBound n ∧
      IsHomogeneous (B.basis g).1 (B.degree g) ∧
      LiteralDisplayedPaperLeadingNormalForm K n
        (B.basis g).1 (B.degree g) ∧
      GO.rootDegree n
          (m.degree (canonicalCombinedNormalForm K n (B.basis g).1)) =
            B.degree g ∧
      GO.coefficientPart n
          (m.degree (canonicalCombinedNormalForm K n (B.basis g).1)) = 0 := by
  dsimp only
  intro g
  refine ⟨(lazardHomogeneousInvariantBasis K n H).degree_le g,
    (lazardHomogeneousInvariantBasis K n H).basis_homogeneous g,
    lazardHomogeneousInvariantBasis_literalDisplayedPackage K n H g, ?_⟩
  exact lazardHomogeneousInvariantBasis_actualLeadingExponent_paperBlockOrder
    K n H g m hm

end CharacteristicZeroEndpoints

/-- Sharp nonmodular, arbitrary-degree, literal combined-ring form of
Lazard's Lemma 2.  The sole characteristic hypothesis is that the finite
subgroup order is nonzero in the ground field.  The existentially returned
`HomogeneousInvariantBasis` is an actual `Module.Basis`, so generation is
part of the returned object; support, normal-form uniqueness, homogeneity,
the degree bound, and the actual formal-`e`-free leading monomial are all
derived internally. -/
theorem exists_lazardHomogeneousInvariantBasis_literalPaperLemmaTwo_for_paperBlockOrder_of_card_ne_zero
    (H : Subgroup (Equiv.Perm (Fin n))) [Fintype H]
    (hcard : (Fintype.card H : K) ≠ 0)
    (m : MonomialOrder (GO.Variable n))
    (hm : GO.PaperLemmaTwoOrderHypotheses n m) :
    ∃ B : HomogeneousInvariantBasis K (Fin n) H (lazardDegreeBound n),
      ∀ g : B.Index,
        B.degree g ≤ lazardDegreeBound n ∧
        IsHomogeneous (B.basis g).1 (B.degree g) ∧
        LiteralDisplayedPaperLeadingNormalForm K n
          (B.basis g).1 (B.degree g) ∧
        GO.rootDegree n
            (m.degree (canonicalCombinedNormalForm K n (B.basis g).1)) =
              B.degree g ∧
        GO.coefficientPart n
            (m.degree (canonicalCombinedNormalForm K n (B.basis g).1)) = 0 := by
  letI : Fact ((Fintype.card H : K) ≠ 0) := ⟨hcard⟩
  let B :=
    Modular.lazardHomogeneousInvariantBasis_of_card_ne_zero_fact K n H
  refine ⟨B, ?_⟩
  intro g
  have hnormal :=
    basis_generator_has_paperLeadingNormalForm K n H B g
  refine ⟨B.degree_le g, B.basis_homogeneous g,
    literalDisplayedPaperLeadingNormalForm_of_paperLeadingNormalForm K n hnormal,
    ?_⟩
  exact actualLeadingExponent_canonicalCombinedNormalForm_paperBlockOrder
    K n hm hnormal

end

end LeanProofs.PolynomialFormulas.LazardDisplayedLeadingTermDescentGeneralBridge
