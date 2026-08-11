import PolynomialFormulas.FrobeniusDummitResolvent
import PolynomialFormulas.LazardGeneralResolventExplicit

/-!
# The concrete Frobenius--Dummit sextic is the generic Lazard resolvent

This file closes the adapter between the two independently useful
formalizations of the quintic resolvent.

* `LazardGeneralResolventExplicit` constructs Lazard's resolvent from an
  exact-stabilizer multivariate polynomial and the left cosets of its
  stabilizer.
* `FrobeniusDummitResolvent` uses the six displayed representatives and the
  ten-term integral polynomial `theta` to define the scalar sextic used by
  the explicit quintic development.

We first transport `theta` from `ℤ` to `ℚ` and retain its exact `F20`
stabilizer by injectivity of `ℤ → ℚ`.  The displayed representatives are then
packaged as an equivalence `Fin 6 ≃ S₅/F20`.  On each representative, the
generic specialized orbit value is literally the existing `thetaValue`;
reindexing the product proves that the two scalar sextics are equal.  Thus
the result is sensitive to, and documents, the left-coset/left-renaming
orientation used by both Lean developments.
-/

open scoped BigOperators Polynomial
open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardGeneralResolventThetaAdapter

open LeanProofs.PolynomialFormulas.Fin5Solvable
open LeanProofs.PolynomialFormulas.Fin5TransitiveC5

set_option autoImplicit false

/-! ## The rational exact-stabilizer polynomial -/

/-- Dummit's ten-term invariant, with its integral coefficients transported
to the rational coefficient field required by the realized quintic. -/
noncomputable def thetaRat : MvPolynomial (Fin 5) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) FrobeniusDummitResolvent.theta

/-- Scalar extension from `ℤ` to `ℚ` does not enlarge the renaming
stabilizer of `theta`. -/
theorem rename_thetaRat_eq_thetaRat_iff (g : FrobeniusDummitResolvent.S5) :
    MvPolynomial.rename g thetaRat = thetaRat ↔ g ∈ standardF20 := by
  constructor
  · intro h
    apply (FrobeniusDummitResolvent.rename_theta_eq_theta_iff g).mp
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa only [thetaRat, MvPolynomial.map_rename] using h
  · intro h
    have hZ := (FrobeniusDummitResolvent.rename_theta_eq_theta_iff g).mpr h
    have hQ := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hZ
    simpa only [thetaRat, MvPolynomial.map_rename] using hQ

/-- The rational ten-term polynomial has formal renaming stabilizer exactly
the standard Frobenius subgroup `F20`. -/
theorem thetaRat_hasExactRenameStabilizer :
    LazardGeneralResolventExplicit.HasExactRenameStabilizer standardF20 thetaRat := by
  unfold LazardGeneralResolventExplicit.HasExactRenameStabilizer
  ext g
  change MvPolynomial.rename g thetaRat = thetaRat ↔ g ∈ standardF20
  exact rename_thetaRat_eq_thetaRat_iff g

/-! ## The six displayed representatives are the generic coset orbit -/

/-- The displayed representatives enumerate the same left-coset space used
by the generic Lazard construction.  No inversion is inserted here: both
Lean constructions use the formal conjugate `rename representative theta`
on the left coset represented by `representative`. -/
noncomputable def representativeCosetEquiv :
    Fin 6 ≃ LazardGeneralResolventCriterion.Cosets standardF20 :=
  Equiv.ofBijective
    (fun i : Fin 6 ↦ (FrobeniusDummitResolvent.representative i : LazardGeneralResolventCriterion.Cosets standardF20))
    ⟨representative_cosets_injective, by
      intro c
      induction c using QuotientGroup.induction_on with
      | _ g =>
          obtain ⟨i, hi⟩ := representative_cosets_exhaustive g
          exact ⟨i, hi.symm⟩⟩

noncomputable instance cosetsFintype :
    Fintype (LazardGeneralResolventCriterion.Cosets standardF20) :=
  Fintype.ofEquiv (Fin 6) representativeCosetEquiv

/-- At a displayed representative, the generic formal orbit polynomial is
the rational scalar extension of the existing integral `thetaOrbit`. -/
theorem universalOrbitValue_representative (i : Fin 6) :
    LazardGeneralResolventExplicit.universalOrbitValue standardF20 thetaRat
        thetaRat_hasExactRenameStabilizer.invariantUnder
        (representativeCosetEquiv i) =
      MvPolynomial.map (Int.castRingHom ℚ) (FrobeniusDummitResolvent.thetaOrbit i) := by
  change LazardGeneralResolventExplicit.renameAction (FrobeniusDummitResolvent.representative i) thetaRat = _
  rw [LazardGeneralResolventExplicit.renameAction, thetaRat, FrobeniusDummitResolvent.thetaOrbit,
    ← MvPolynomial.map_rename]
  congr 2

/-- Evaluation after `ℤ → ℚ → L` is evaluation through the canonical
integer map `ℤ → L`.  Consequently each generic coset value is literally
the corresponding scalar theta-value. -/
theorem specializedOrbitValue_representative
    {L : Type*} [Field L] [Algebra ℚ L]
    (roots : Fin 5 → L) (i : Fin 6) :
    LazardGeneralResolventExplicit.specializedOrbitValue standardF20 thetaRat
        thetaRat_hasExactRenameStabilizer.invariantUnder roots
        (representativeCosetEquiv i) =
      FrobeniusDummitResolvent.thetaValue roots i := by
  rw [LazardGeneralResolventExplicit.specializedOrbitValue,
    universalOrbitValue_representative]
  change
    MvPolynomial.eval₂Hom (algebraMap ℚ L) roots
        (MvPolynomial.map (Int.castRingHom ℚ) (FrobeniusDummitResolvent.thetaOrbit i)) =
      MvPolynomial.eval₂Hom (Int.castRingHom L) roots (FrobeniusDummitResolvent.thetaOrbit i)
  rw [MvPolynomial.eval₂Hom_map_hom
    (Int.castRingHom ℚ) roots (algebraMap ℚ L)
      (FrobeniusDummitResolvent.thetaOrbit i)]
  apply MvPolynomial.eval₂Hom_congr
  · exact RingHom.ext_int _ _
  · rfl
  · rfl

/-- The generic specialized orbit product for the rational `theta` is
exactly the scalar Frobenius--Dummit sextic.  The proof is the explicit
left-coset reindexing `Fin 6 ≃ S₅/F20`, followed factor by factor by
`specializedOrbitValue_representative`. -/
theorem specializedOrbitResolvent_eq_scalarResolvent
    {L : Type*} [Field L] [Algebra ℚ L]
    (roots : Fin 5 → L) :
    LazardGeneralResolventCriterion.orbitResolvent standardF20
        (LazardGeneralResolventExplicit.specializedOrbitValue standardF20 thetaRat
          thetaRat_hasExactRenameStabilizer.invariantUnder roots) =
      FrobeniusDummitResolvent.scalarResolvent roots := by
  classical
  rw [LazardGeneralResolventCriterion.orbitResolvent, FrobeniusDummitResolvent.scalarResolvent_eq_prod]
  calc
    (∏ c : LazardGeneralResolventCriterion.Cosets standardF20,
        (X - C
          (LazardGeneralResolventExplicit.specializedOrbitValue standardF20 thetaRat
            thetaRat_hasExactRenameStabilizer.invariantUnder roots c))) =
        ∏ i : Fin 6,
          (X - C
            (LazardGeneralResolventExplicit.specializedOrbitValue standardF20 thetaRat
              thetaRat_hasExactRenameStabilizer.invariantUnder roots
                (representativeCosetEquiv i))) := by
      exact (Equiv.prod_comp representativeCosetEquiv
        (fun c : LazardGeneralResolventCriterion.Cosets standardF20 ↦
          X - C
            (LazardGeneralResolventExplicit.specializedOrbitValue standardF20 thetaRat
              thetaRat_hasExactRenameStabilizer.invariantUnder roots c))).symm
    _ = ∏ i : Fin 6, (X - C (FrobeniusDummitResolvent.thetaValue roots i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [specializedOrbitValue_representative]

/-! ## Literal paper-resolvent adapter -/

/-- For every exact ordered root presentation, scalar extension of the
generic paper-facing Lazard resolvent is exactly the concrete sextic used by
the explicit quintic package. -/
theorem paperRootTupleResolvent_map_eq_scalarResolvent
    {L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (f : ℚ[X]) (roots : Fin 5 → L)
    (presentation : LazardGeneralResolventExplicit.ExactRootTuplePresentation f roots) :
    (LazardGeneralResolventExplicit.paperRootTupleResolvent
        (G := standardF20) (invariant := thetaRat) (f := f) (roots := roots)
        (exactStabilizer := thetaRat_hasExactRenameStabilizer)
        (exactPresentation := presentation)).map (algebraMap ℚ L) =
      FrobeniusDummitResolvent.scalarResolvent roots := by
  rw [LazardGeneralResolventExplicit.paperRootTupleResolvent_map]
  exact specializedOrbitResolvent_eq_scalarResolvent roots

/-- Any rational polynomial already known to specialize to the concrete
scalar sextic is therefore literally the generic paper-facing resolvent.
Injectivity of scalar extension performs the descent; equality is not added
as a certificate. -/
theorem paperRootTupleResolvent_eq_of_map_eq_scalarResolvent
    {L : Type*} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (f : ℚ[X]) (roots : Fin 5 → L)
    (presentation : LazardGeneralResolventExplicit.ExactRootTuplePresentation f roots)
    (baseResolvent : ℚ[X])
    (hbase : baseResolvent.map (algebraMap ℚ L) =
      FrobeniusDummitResolvent.scalarResolvent roots) :
    LazardGeneralResolventExplicit.paperRootTupleResolvent
        (G := standardF20) (invariant := thetaRat) (f := f) (roots := roots)
        (exactStabilizer := thetaRat_hasExactRenameStabilizer)
        (exactPresentation := presentation) =
      baseResolvent := by
  apply Polynomial.map_injective (algebraMap ℚ L) (algebraMap ℚ L).injective
  exact (paperRootTupleResolvent_map_eq_scalarResolvent
    f roots presentation).trans hbase.symm

end LeanProofs.PolynomialFormulas.LazardGeneralResolventThetaAdapter
