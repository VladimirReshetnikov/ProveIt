import PolynomialFormulas.LazardGeneralResolventConjugacyCounterexample
import PolynomialFormulas.LazardGeneralResolventExplicit
import PolynomialFormulas.LazardGeneralResolventThetaAdapter
import PolynomialFormulas.LazardOptimalityTheoremThreeFormulaBridge
import PolynomialFormulas.LazardQuinticRootOrderingF20

/-!
# A polynomial realization of the conjugacy correction to Lazard Theorem 1

The finite witness in `LazardGeneralResolventConjugacyCounterexample` shows
that a non-base coset can have stabilizer a conjugate of the displayed
`F20`, without that stabilizer being contained in the displayed copy.  This
file realizes the same phenomenon by an actual irreducible rational
quintic, its ordered roots in its splitting field, and the actual Galois
action on those roots.

The construction is generic for an irreducible depressed rational quintic
whose scalar Frobenius--Dummit resolvent has a rational root.  That root
selects an ordering for which the Galois image lies in the standard `F20`.
Transitivity supplies a conjugate five-cycle in the original image; because
the selected image lies in `F20`, a finite `S5` calculation shows that it
contains the standard five-cycle.  Relabelling the selected roots by the
explicit three-cycle therefore makes the actual Galois image contain the
conjugated five-cycle which lies outside the displayed `F20`.

The final theorem instantiates the construction with the explicit cyclic
quintic used elsewhere in the development.  Its rational resolvent root is
proved by direct coefficient evaluation.  Thus this is not an inverse-
Galois assumption or an abstract group action presented as a polynomial.
-/

open scoped BigOperators Polynomial
open Equiv MulAction Polynomial Subgroup

namespace LeanProofs.PolynomialFormulas.LazardGeneralResolventRealizedCounterexample

open LeanProofs.PolynomialFormulas.Fin5Solvable
open LeanProofs.PolynomialFormulas.Fin5TransitiveC5
open LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable local instance cyclicIsSplittingField :
    LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.IsSplittingField ℚ
      LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.SplittingField :=
  Polynomial.IsSplittingField.splittingField _

noncomputable local instance cyclicIsGalois :
    IsGalois ℚ
      LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.SplittingField :=
  IsGalois.of_separable_splitting_field
    LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic_polynomial_irreducible.separable

noncomputable local instance standardF20Fintype :
    Fintype LazardGeneralResolventConjugacyCounterexample.G :=
  Fintype.ofEquiv
    {g : S5 // g ∈ f20Elements}
    standardF20EquivElements.symm

/-! ## The finite normalization fact used inside an actual Galois image -/

/-- Every order-five element of the standard `F20` generates its unique
order-five subgroup, the standard `C5`.  The decidable certificate is local
to the 20-element subgroup rather than quantified over all 120 elements of
`S5`. -/
theorem fiveCycle_mem_zpowers_of_orderOf_eq_five_in_standardF20 :
    ∀ x : LazardGeneralResolventConjugacyCounterexample.G,
      orderOf (x : LazardGeneralResolventConjugacyCounterexample.A) = 5 →
        fiveCycle ∈ Subgroup.zpowers (x : LazardGeneralResolventConjugacyCounterexample.A) := by
  classical
  intro x
  intro hx
  rw [((isOfFinOrder_of_finite
    (x : LazardGeneralResolventConjugacyCounterexample.A)).mem_zpowers_iff_mem_range_orderOf),
    hx]
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpow' : ∀ y : LazardGeneralResolventConjugacyCounterexample.G,
      ((y : LazardGeneralResolventConjugacyCounterexample.A) ^ 5 = 1 ∧
        (y : LazardGeneralResolventConjugacyCounterexample.A) ≠ 1) →
      fiveCycle ∈ (Finset.range 5).image
        ((y : LazardGeneralResolventConjugacyCounterexample.A) ^ ·) := by
    decide
  have hpow (y : LazardGeneralResolventConjugacyCounterexample.G)
      (hy : orderOf (y : LazardGeneralResolventConjugacyCounterexample.A) = 5) :
      fiveCycle ∈ (Finset.range 5).image
        ((y : LazardGeneralResolventConjugacyCounterexample.A) ^ ·) := by
    exact hpow' y (orderOf_eq_prime_iff.mp hy)
  exact hpow x hx

/-- If a conjugate of the standard five-cycle lies in the standard `F20`,
then it generates the standard `C5`.  Preservation of element order under
conjugation reduces the claim to the preceding 20-element certificate. -/
theorem fiveCycle_mem_zpowers_conjugate_of_mem_standardF20
    (a : LazardGeneralResolventConjugacyCounterexample.A) (ha : a * fiveCycle * a⁻¹ ∈ LazardGeneralResolventConjugacyCounterexample.G) :
    fiveCycle ∈ Subgroup.zpowers (a * fiveCycle * a⁻¹) := by
  let x : LazardGeneralResolventConjugacyCounterexample.G := ⟨a * fiveCycle * a⁻¹, ha⟩
  apply fiveCycle_mem_zpowers_of_orderOf_eq_five_in_standardF20 x
  have horder := MulEquiv.orderOf_eq (MulAut.conj a) fiveCycle
  simpa only [x, MulAut.conj_apply, orderOf_fiveCycle] using horder

/-! ## The realized counterexample package -/

/-- Data proving that the fixed-subgroup converse fails for an actual
polynomial and an actual ordering of all its roots.

`presentation` is multiplicity-sensitive: it records the exact linear
factorization of the quintic, not merely that the displayed values happen
to be roots.  `action_eq_intrinsic` identifies the explicitly conjugated
action with the permutation action reconstructed from that presentation.
-/
structure RealizedFixedSubgroupCounterexample
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial) where
  q : ℚ
  roots : Fin 5 → c.polynomial.SplittingField
  presentation :
    LazardGeneralResolventExplicit.ExactRootTuplePresentation c.polynomial roots
  action : c.polynomial.Gal →* LazardGeneralResolventConjugacyCounterexample.A
  roots_equivariant : ∀ (σ : c.polynomial.Gal) (k : Fin 5),
    σ (roots k) = roots (action σ k)
  action_eq_intrinsic :
    LazardGeneralResolventExplicit.rootTupleAction c.polynomial roots
        presentation.toRootTuplePresentation = action
  resolvent_specialization :
    (resolventPolynomial c).map
        (algebraMap ℚ c.polynomial.SplittingField) =
      FrobeniusDummitResolvent.scalarResolvent roots
  resolvent_has_base_root : (resolventPolynomial c).IsRoot q
  resolvent_separable : (resolventPolynomial c).Separable
  corrected_conjugate_containment : action.range ≤ LazardGeneralResolventConjugacyCounterexample.H
  displayed_containment_fails : ¬ action.range ≤ LazardGeneralResolventConjugacyCounterexample.G
  selected_coset_fixed : ∀ σ : c.polynomial.Gal,
    action σ • LazardGeneralResolventConjugacyCounterexample.selectedCoset = LazardGeneralResolventConjugacyCounterexample.selectedCoset

/-! ## Identification with the generic paper-facing resolvent -/

/-- The concrete sextic carried by a realized package is not merely another
polynomial with the same root behavior: it is literally the generic Lazard
`paperRootTupleResolvent` built from the rational ten-term theta polynomial,
the exact ordered root presentation, and its exact `F20` stabilizer. -/
theorem RealizedFixedSubgroupCounterexample.paperRootTupleResolvent_eq
    {c : DepressedQuintic ℚ} {hp : Irreducible c.polynomial}
    [IsGalois ℚ c.polynomial.SplittingField]
    (w : RealizedFixedSubgroupCounterexample c hp) :
    LazardGeneralResolventExplicit.paperRootTupleResolvent
        (G := standardF20) (invariant := LazardGeneralResolventThetaAdapter.thetaRat)
        (f := c.polynomial) (roots := w.roots)
        (exactStabilizer :=
          LazardGeneralResolventThetaAdapter.thetaRat_hasExactRenameStabilizer)
        (exactPresentation := w.presentation) =
      resolventPolynomial c := by
  letI : c.polynomial.IsSplittingField ℚ c.polynomial.SplittingField :=
    Polynomial.IsSplittingField.splittingField c.polynomial
  exact LazardGeneralResolventThetaAdapter.paperRootTupleResolvent_eq_of_map_eq_scalarResolvent
    c.polynomial w.roots w.presentation (resolventPolynomial c)
      w.resolvent_specialization

/-- The corrected form of Lazard's Theorem 1 is now applied literally to the
realized polynomial, rather than reproved through the separately developed
scalar criterion.  The only transport is the preceding theorem identifying
the generic paper resolvent with Lazard's explicit sextic, plus the proved
identification of the constructed action with the intrinsic ordered-root
action. -/
theorem RealizedFixedSubgroupCounterexample.literal_correctedTheoremOne
    {c : DepressedQuintic ℚ} {hp : Irreducible c.polynomial}
    [IsGalois ℚ c.polynomial.SplittingField]
    (w : RealizedFixedSubgroupCounterexample c hp) :
    (∃ q : ℚ, (resolventPolynomial c).IsRoot q) ↔
      ∃ a : LazardGeneralResolventConjugacyCounterexample.A,
        w.action.range ≤ LazardGeneralResolventCriterion.conjugateStabilizer standardF20 a := by
  letI : c.polynomial.IsSplittingField ℚ c.polynomial.SplittingField :=
    Polynomial.IsSplittingField.splittingField c.polynomial
  have heq := w.paperRootTupleResolvent_eq
  have hseparable :
      (LazardGeneralResolventExplicit.paperRootTupleResolvent
        (G := standardF20) (invariant := LazardGeneralResolventThetaAdapter.thetaRat)
        (f := c.polynomial) (roots := w.roots)
        (exactStabilizer :=
          LazardGeneralResolventThetaAdapter.thetaRat_hasExactRenameStabilizer)
        (exactPresentation := w.presentation)).Separable := by
    rw [heq]
    exact w.resolvent_separable
  rw [← heq, ← w.action_eq_intrinsic]
  exact LazardGeneralResolventExplicit.paperRootTupleResolvent_hasRoot_iff_image_le_conjugate
      (G := standardF20) (invariant := LazardGeneralResolventThetaAdapter.thetaRat)
      (f := c.polynomial) (roots := w.roots)
      (exactStabilizer :=
        LazardGeneralResolventThetaAdapter.thetaRat_hasExactRenameStabilizer)
      (exactPresentation := w.presentation) hseparable

/-! ## Generic realization from a rational scalar-resolvent root -/

/-- Every irreducible depressed rational quintic with a rational
Frobenius--Dummit resolvent root admits a deliberately relabelled, exact
root presentation realizing the failure of the fixed displayed subgroup
conclusion.

The same rational polynomial remains the specialized resolvent after the
relabeling because the six-factor scalar resolvent is invariant under all
root permutations.
-/
theorem exists_realizedFixedSubgroupCounterexample
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (q : ℚ) (hq : (resolventPolynomial c).IsRoot q) :
    Nonempty (RealizedFixedSubgroupCounterexample c hp) := by
  classical
  letI : c.polynomial.IsSplittingField ℚ c.polynomial.SplittingField :=
    Polynomial.IsSplittingField.splittingField c.polynomial
  letI : IsGalois ℚ c.polynomial.SplittingField :=
    IsGalois.of_separable_splitting_field hp.separable
  let p := c.polynomial
  let hdeg : p.natDegree = 5 := c.polynomial_natDegree
  let canonicalRoots : Fin 5 → p.SplittingField :=
    QuinticScalarGaloisBridge.rootTuple p hp hdeg
  let originalAction : p.Gal →* LazardGeneralResolventConjugacyCounterexample.A :=
    QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg

  have hqMap := Polynomial.IsRoot.map
    (f := algebraMap ℚ p.SplittingField) hq
  have hresolventMap :
      (resolventPolynomial c).map (algebraMap ℚ p.SplittingField) =
        FrobeniusDummitResolvent.scalarResolvent canonicalRoots := by
    simpa only [p, canonicalRoots, hdeg] using
      LazardQuintic.resolventPolynomial_map_eq_scalarResolvent_rootTuple
        c hp
  rw [hresolventMap] at hqMap
  obtain ⟨i, hi⟩ :=
    (FrobeniusDummitResolvent.scalarResolvent_isRoot_iff canonicalRoots
      (algebraMap ℚ p.SplittingField q)).mp hqMap

  let r : LazardGeneralResolventConjugacyCounterexample.A := FrobeniusDummitResolvent.representative i
  let t : LazardGeneralResolventConjugacyCounterexample.A := LazardGeneralResolventConjugacyCounterexample.relabelling
  let relabel : LazardGeneralResolventConjugacyCounterexample.A := r * t⁻¹
  let goodAction : p.Gal →* LazardGeneralResolventConjugacyCounterexample.A :=
    (MulAut.conj r⁻¹).toMonoidHom.comp originalAction
  let badAction : p.Gal →* LazardGeneralResolventConjugacyCounterexample.A :=
    (MulAut.conj t).toMonoidHom.comp goodAction
  let roots : Fin 5 → p.SplittingField := fun k ↦
    canonicalRoots (relabel k)

  have hrootsInjective : Function.Injective roots :=
    (QuinticScalarGaloisBridge.rootTuple_injective p hp hdeg).comp relabel.injective

  have hrootsEquivariant : ∀ (σ : p.Gal) (k : Fin 5),
      σ (roots k) = roots (badAction σ k) := by
    intro σ k
    rw [show roots k = canonicalRoots (relabel k) by rfl,
      QuinticScalarGaloisBridge.gal_maps_rootTuple]
    have hperm : originalAction σ * relabel =
        relabel * badAction σ := by
      change originalAction σ * (r * t⁻¹) =
        (r * t⁻¹) * (t * (r⁻¹ * originalAction σ * r) * t⁻¹)
      group
    change canonicalRoots ((originalAction σ * relabel) k) =
      canonicalRoots ((relabel * badAction σ) k)
    rw [hperm]

  have hproductPermuted :
      (∏ k : Fin 5, (X - C (roots k))) =
        ∏ k : Fin 5, (X - C (canonicalRoots k)) := by
    simpa only [roots] using
      (Equiv.prod_comp relabel
        (fun k : Fin 5 ↦ X - C (canonicalRoots k)))
  have hfactorization :
      p.map (algebraMap ℚ p.SplittingField) =
        ∏ k : Fin 5, (X - C (roots k)) := by
    calc
      p.map (algebraMap ℚ p.SplittingField) =
          ∏ k : Fin 5, (X - C (canonicalRoots k)) := by
        simpa only [p, canonicalRoots, hdeg] using
          QuinticScalarGaloisBridge.mapped_eq_prod_rootTuple p hp c.polynomial_monic hdeg
      _ = ∏ k : Fin 5, (X - C (roots k)) := hproductPermuted.symm

  have hcomplete : ∀ x : p.SplittingField,
      x ∈ p.rootSet p.SplittingField ↔ ∃ k : Fin 5, roots k = x := by
    intro x
    constructor
    · intro hx
      let y : p.rootSet p.SplittingField := ⟨x, hx⟩
      let j : Fin 5 := QuinticScalarGaloisBridge.rootEquiv p hp hdeg y
      refine ⟨relabel⁻¹ j, ?_⟩
      change canonicalRoots (relabel (relabel⁻¹ j)) = x
      change canonicalRoots (relabel ((relabel.symm) j)) = x
      rw [relabel.apply_symm_apply]
      change ((QuinticScalarGaloisBridge.rootEquiv p hp hdeg).symm j :
        p.SplittingField) = x
      simp only [j, y, Equiv.symm_apply_apply]
    · rintro ⟨k, rfl⟩
      change canonicalRoots (relabel k) ∈ p.rootSet p.SplittingField
      exact ((QuinticScalarGaloisBridge.rootEquiv p hp hdeg).symm (relabel k)).property

  let presentation : LazardGeneralResolventExplicit.ExactRootTuplePresentation p roots :=
    { splits := SplittingField.splits p
      nodup := hrootsInjective
      complete := hcomplete
      nonzero := hp.ne_zero
      factorization := by
        have hlead : p.leadingCoeff = 1 := by
          simpa only [p] using c.polynomial_monic.leadingCoeff
        rw [hlead, map_one, C_1, one_mul]
        exact hfactorization }

  have hgood (σ : p.Gal) : goodAction σ ∈ LazardGeneralResolventConjugacyCounterexample.G := by
    have hthetaRange : FrobeniusDummitResolvent.thetaValue canonicalRoots i ∈
        Set.range (algebraMap ℚ p.SplittingField) :=
      ⟨q, hi.symm⟩
    change (FrobeniusDummitResolvent.representative i)⁻¹ *
      (QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg) σ *
      FrobeniusDummitResolvent.representative i ∈ standardF20
    exact conjugated_rootPermutation_mem_standardF20_of_thetaValue_mem_range
      p hp hdeg i hthetaRange σ

  have hcorrected : badAction.range ≤ LazardGeneralResolventConjugacyCounterexample.H := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨goodAction σ, hgood σ, rfl⟩

  have hfiveGood : fiveCycle ∈ goodAction.range := by
    let K : Subgroup LazardGeneralResolventConjugacyCounterexample.A := QuinticScalarGaloisBridge.rootPermutationGroup p hp hdeg
    letI : MulAction.IsPretransitive K (Fin 5) :=
      QuinticScalarGaloisBridge.rootPermutationGroup_isPretransitive p hp hdeg
    obtain ⟨a, ha⟩ :=
      exists_map_conj_standardC5_le_of_pretransitive K
    have haOriginal : a * fiveCycle * a⁻¹ ∈ K := by
      apply ha
      exact ⟨fiveCycle, Subgroup.mem_zpowers fiveCycle, rfl⟩
    obtain ⟨σ, hσ⟩ := haOriginal
    let b : LazardGeneralResolventConjugacyCounterexample.A := r⁻¹ * a
    have hgoodEq : goodAction σ = b * fiveCycle * b⁻¹ := by
      change r⁻¹ * originalAction σ * r =
        (r⁻¹ * a) * fiveCycle * (r⁻¹ * a)⁻¹
      rw [hσ]
      group
    have hbG : b * fiveCycle * b⁻¹ ∈ LazardGeneralResolventConjugacyCounterexample.G := by
      rw [← hgoodEq]
      exact hgood σ
    have hpower :=
      fiveCycle_mem_zpowers_conjugate_of_mem_standardF20 b hbG
    have hbRange : b * fiveCycle * b⁻¹ ∈ goodAction.range := by
      rw [← hgoodEq]
      exact ⟨σ, rfl⟩
    exact (Subgroup.zpowers_le.mpr hbRange) hpower

  have hdisplayed : ¬ badAction.range ≤ LazardGeneralResolventConjugacyCounterexample.G := by
    intro hle
    obtain ⟨σ, hσ⟩ := hfiveGood
    apply LazardGeneralResolventConjugacyCounterexample.conjugatedFiveCycle_not_mem_G
    apply hle
    refine ⟨σ, ?_⟩
    change t * goodAction σ * t⁻¹ = t * fiveCycle * t⁻¹
    rw [hσ]

  have hresolventSpecialization :
      (resolventPolynomial c).map
          (algebraMap ℚ p.SplittingField) =
        FrobeniusDummitResolvent.scalarResolvent roots := by
    calc
      (resolventPolynomial c).map
          (algebraMap ℚ p.SplittingField) =
          FrobeniusDummitResolvent.scalarResolvent canonicalRoots := hresolventMap
      _ = FrobeniusDummitResolvent.scalarResolvent roots := by
        exact (FrobeniusDummitResolvent.scalarResolvent_permute canonicalRoots relabel).symm

  have hactionIntrinsic :
      LazardGeneralResolventExplicit.rootTupleAction p roots
          presentation.toRootTuplePresentation = badAction := by
    apply DFunLike.ext _ _
    intro σ
    apply Equiv.ext
    intro k
    apply hrootsInjective
    calc
      roots
          (LazardGeneralResolventExplicit.rootTupleAction p roots
            presentation.toRootTuplePresentation σ k) =
          σ (roots k) :=
        (LazardGeneralResolventExplicit.rootTupleAction_equivariant p roots
          presentation.toRootTuplePresentation σ k).symm
      _ = roots (badAction σ k) := hrootsEquivariant σ k

  have hfixed : ∀ σ : p.Gal,
      badAction σ • LazardGeneralResolventConjugacyCounterexample.selectedCoset = LazardGeneralResolventConjugacyCounterexample.selectedCoset := by
    intro σ
    exact LazardGeneralResolventConjugacyCounterexample.H_fixes_selectedCoset ⟨badAction σ,
      hcorrected ⟨σ, rfl⟩⟩

  exact ⟨{
    q := q
    roots := roots
    presentation := presentation
    action := badAction
    roots_equivariant := hrootsEquivariant
    action_eq_intrinsic := hactionIntrinsic
    resolvent_specialization := hresolventSpecialization
    resolvent_has_base_root := hq
    resolvent_separable :=
      LazardQuintic.resolventPolynomial_separable c hp
    corrected_conjugate_containment := hcorrected
    displayed_containment_fails := hdisplayed
    selected_coset_fixed := hfixed }⟩

/-! ## Closed cyclic-quintic instance -/

/-- A closed polynomial-level counterexample to the fixed-subgroup version
of Lazard Theorem 1.  The polynomial is the explicit cyclic quintic after
the standard depression translation, and its rational resolvent root is
`-1991/125`.

The returned package includes the exact five-factor root presentation, the
intrinsic Galois permutation action, separability of the six-factor
resolvent, its rational root, containment in the displayed conjugate `F20`,
and failure of containment in the displayed standard `F20`.
-/
theorem cyclicQuintic_realizes_fixed_displayed_subgroup_failure :
    Nonempty
      (RealizedFixedSubgroupCounterexample
        LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic
        LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic_polynomial_irreducible) := by
  letI :
      LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.IsSplittingField ℚ
        LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.SplittingField :=
    Polynomial.IsSplittingField.splittingField _
  letI : IsGalois ℚ
      LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.SplittingField :=
    IsGalois.of_separable_splitting_field
      LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic_polynomial_irreducible.separable
  exact exists_realizedFixedSubgroupCounterexample
    LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic
    LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic_polynomial_irreducible
    (-1991 / 125 : ℚ) LazardOptimalityTheoremThreeFormulaBridge.cyclicResolvent_isRoot

/-- Closed realized invocation of the generic corrected Theorem 1.  In
particular, the polynomial in the root statement is proved equal to the
generic `paperRootTupleResolvent`; it is not connected only by an informal
identification or by matching root sets. -/
theorem cyclicQuintic_invokes_literal_correctedTheoremOne :
    ∃ w : RealizedFixedSubgroupCounterexample
        LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic
        LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic_polynomial_irreducible,
      LazardGeneralResolventExplicit.paperRootTupleResolvent
          (G := standardF20) (invariant := LazardGeneralResolventThetaAdapter.thetaRat)
          (f := LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial)
          (roots := w.roots)
          (exactStabilizer :=
            LazardGeneralResolventThetaAdapter.thetaRat_hasExactRenameStabilizer)
          (exactPresentation := w.presentation) =
        resolventPolynomial LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic ∧
      ((∃ q : ℚ,
          (resolventPolynomial LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic).IsRoot q) ↔
        ∃ a : LazardGeneralResolventConjugacyCounterexample.A,
          w.action.range ≤
            LazardGeneralResolventCriterion.conjugateStabilizer standardF20 a) := by
  letI :
      LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.IsSplittingField ℚ
        LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.SplittingField :=
    Polynomial.IsSplittingField.splittingField _
  letI : IsGalois ℚ
      LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic.polynomial.SplittingField :=
    IsGalois.of_separable_splitting_field
      LazardOptimalityTheoremThreeFormulaBridge.cyclicDepressedQuintic_polynomial_irreducible.separable
  obtain ⟨w⟩ := cyclicQuintic_realizes_fixed_displayed_subgroup_failure
  exact ⟨w, w.paperRootTupleResolvent_eq,
    w.literal_correctedTheoremOne⟩

end LeanProofs.PolynomialFormulas.LazardGeneralResolventRealizedCounterexample
