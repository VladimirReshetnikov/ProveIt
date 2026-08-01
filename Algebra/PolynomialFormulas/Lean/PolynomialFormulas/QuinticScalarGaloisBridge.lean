import PolynomialFormulas.Fin5TransitiveC5
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Galois groups of irreducible rational quintics as subgroups of `S₅`

This file identifies the Galois group of an irreducible rational quintic with
its faithful permutation group on an ordered copy of the five roots.  The
resulting subgroup of `S₅` is transitive, and it is solvable exactly when it is
contained in a conjugate of the standard Frobenius group `F₂₀`.

The ordered roots and the permutation representation are noncomputable proof
devices.  The eventual decision procedure uses the symmetric coefficients of
the scalar resolvent, not this choice of an ordering.
-/

open scoped Polynomial
open Equiv Polynomial

namespace LeanProofs.PolynomialFormulas.QuinticScalarGaloisBridge

open Fin5Solvable Fin5TransitiveC5

/-- It suffices to test the six explicit coset representatives when asking
whether a subgroup fixes a point of `S₅ / F₂₀`. -/
theorem exists_fixed_representative_coset_iff_le_conjugate_standardF20
    (H : Subgroup S5) :
    (∃ i : Fin 6, ∀ h : H,
      (h : S5) • (Fin5TransitiveC5.representative i : Cosets) =
        (Fin5TransitiveC5.representative i : Cosets)) ↔
      ∃ g : S5, H ≤ standardF20.map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨Fin5TransitiveC5.representative i, ?_⟩
    intro g hg
    have hmem : g ∈ MulAction.stabilizer S5
        (Fin5TransitiveC5.representative i • ((1 : S5) : Cosets)) :=
      MulAction.mem_stabilizer_iff.mpr (hi ⟨g, hg⟩)
    simpa only [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient] using hmem
  · rintro ⟨g, hg⟩
    obtain ⟨i, hi⟩ := representative_cosets_exhaustive g
    refine ⟨i, fun h ↦ ?_⟩
    have hmem : (h : S5) ∈ MulAction.stabilizer S5
        (g • ((1 : S5) : Cosets)) := by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
        MulAction.stabilizer_quotient]
      exact hg h.property
    have hfix := MulAction.mem_stabilizer_iff.mp hmem
    change (h : S5) • (g : Cosets) = (g : Cosets) at hfix
    rw [hi] at hfix
    exact hfix

/-- A choice of ordering of the five roots in the canonical splitting field. -/
noncomputable def rootEquiv (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) : p.rootSet p.SplittingField ≃ Fin 5 :=
  Fintype.equivOfCardEq
    ((card_rootSet_eq_natDegree hp.separable (SplittingField.splits p)).trans hdeg)

/-- The faithful permutation representation obtained from `rootEquiv`.  We
use the canonical action on roots in the splitting field directly; this
avoids introducing a second algebra structure on the splitting field. -/
noncomputable def rootPermutationHom (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) : p.Gal →* Equiv.Perm (Fin 5) :=
  (rootEquiv p hp hdeg).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom p.Gal (p.rootSet p.SplittingField))

/-- The quintic Galois group, realized as a subgroup of `S₅`. -/
noncomputable def rootPermutationGroup (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) : Subgroup (Equiv.Perm (Fin 5)) :=
  (rootPermutationHom p hp hdeg).range

theorem rootPermutationHom_injective (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) :
    Function.Injective (rootPermutationHom p hp hdeg) := by
  intro σ τ hστ
  apply Gal.ext
  intro x hx
  let y : p.rootSet p.SplittingField := ⟨x, hx⟩
  have hperm :
      MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) σ =
        MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) τ :=
    (rootEquiv p hp hdeg).permCongrHom.injective hστ
  have hy := Equiv.congr_fun hperm y
  exact congrArg Subtype.val hy

/-- The abstract Galois group is isomorphic to its root-permutation image. -/
noncomputable def galEquivRootPermutationGroup (p : ℚ[X])
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    p.Gal ≃* rootPermutationGroup p hp hdeg :=
  MonoidHom.ofInjective (rootPermutationHom_injective p hp hdeg)

/-- Irreducibility makes the root-permutation image transitive. -/
theorem rootPermutationGroup_isPretransitive (p : ℚ[X])
    (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    MulAction.IsPretransitive (rootPermutationGroup p hp hdeg) (Fin 5) := by
  letI : p.IsSplittingField ℚ p.SplittingField :=
    Polynomial.IsSplittingField.splittingField p
  letI : IsGalois ℚ p.SplittingField :=
    IsGalois.of_separable_splitting_field hp.separable
  constructor
  intro x y
  let e := rootEquiv p hp hdeg
  let x' : p.rootSet p.SplittingField := e.symm x
  let y' : p.rootSet p.SplittingField := e.symm y
  letI : MulAction.IsPretransitive p.Gal (p.rootSet p.SplittingField) := by
    constructor
    intro a b
    have ha := minpoly.eq_of_irreducible hp (mem_rootSet.mp a.2).2
    have hb := minpoly.eq_of_irreducible hp (mem_rootSet.mp b.2).2
    obtain ⟨g, hg⟩ :=
      (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hb.symm.trans ha)
    exact ⟨g, Subtype.ext hg⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq p.Gal x' y'
  let h : rootPermutationGroup p hp hdeg :=
    ⟨rootPermutationHom p hp hdeg g, ⟨g, rfl⟩⟩
  refine ⟨h, ?_⟩
  change rootPermutationHom p hp hdeg g x = y
  change e
    ((MulAction.toPermHom p.Gal (p.rootSet p.SplittingField) g) (e.symm x)) = y
  change e (g • x') = y
  rw [hg]
  exact e.apply_symm_apply y

/-- The chosen ordered tuple of roots. -/
noncomputable def rootTuple (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) : Fin 5 → p.SplittingField :=
  fun i ↦ rootEquiv p hp hdeg |>.symm i

/-- The Galois action on the chosen tuple is precisely
`rootPermutationHom`. -/
theorem gal_maps_rootTuple (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) (σ : p.Gal) (i : Fin 5) :
    σ (rootTuple p hp hdeg i) =
      rootTuple p hp hdeg (rootPermutationHom p hp hdeg σ i) := by
  change σ ((rootEquiv p hp hdeg).symm i : p.SplittingField) =
    ((rootEquiv p hp hdeg).symm
      ((rootEquiv p hp hdeg)
        (σ • (rootEquiv p hp hdeg).symm i)) : p.SplittingField)
  rw [(rootEquiv p hp hdeg).symm_apply_apply]
  rfl

theorem rootTuple_injective (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) : Function.Injective (rootTuple p hp hdeg) := by
  intro i j hij
  apply (rootEquiv p hp hdeg).symm.injective
  apply Subtype.ext
  exact hij

theorem rootTuple_isRoot (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) (i : Fin 5) :
    (p.map (algebraMap ℚ p.SplittingField)).IsRoot (rootTuple p hp hdeg i) := by
  rw [Polynomial.IsRoot.def, eval_map, ← aeval_def]
  exact (mem_rootSet.mp ((rootEquiv p hp hdeg).symm i).property).2

/-- The mapped monic quintic is the product of the five linear factors from
the chosen root ordering. -/
theorem mapped_eq_prod_rootTuple (p : ℚ[X]) (hp : Irreducible p)
    (hmonic : p.Monic) (hdeg : p.natDegree = 5) :
    p.map (algebraMap ℚ p.SplittingField) =
      ∏ i : Fin 5, (X - C (rootTuple p hp hdeg i)) := by
  have hm : (p.map (algebraMap ℚ p.SplittingField)).Monic := hmonic.map _
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
  · exact Polynomial.monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)
  · exact hm
  · apply Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C (rootTuple_injective p hp hdeg))
    intro i
    exact dvd_iff_isRoot.mpr (rootTuple_isRoot p hp hdeg i)
  · rw [hmonic.natDegree_map, hdeg,
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    simp

/-- The fixed-field characterization in the canonical splitting field. -/
theorem mem_range_algebraMap_iff_gal_fixed (p : ℚ[X])
    (hp : Irreducible p) (x : p.SplittingField) :
    x ∈ Set.range (algebraMap ℚ p.SplittingField) ↔
      ∀ σ : p.Gal, σ x = x := by
  letI : p.IsSplittingField ℚ p.SplittingField :=
    Polynomial.IsSplittingField.splittingField p
  letI : FiniteDimensional ℚ p.SplittingField :=
    IsSplittingField.finiteDimensional p.SplittingField p
  letI : IsGalois ℚ p.SplittingField :=
    IsGalois.of_separable_splitting_field hp.separable
  exact IsGalois.mem_range_algebraMap_iff_fixed x

/-- The sum of the chosen roots is rational.  For the no-collision argument
it is enough to observe that every Galois automorphism merely permutes the
tuple; no coefficient calculation is needed here. -/
theorem rootTuple_sum_mem_range (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) :
    (∑ i : Fin 5, rootTuple p hp hdeg i) ∈
      Set.range (algebraMap ℚ p.SplittingField) := by
  letI : p.IsSplittingField ℚ p.SplittingField :=
    Polynomial.IsSplittingField.splittingField p
  letI : FiniteDimensional ℚ p.SplittingField :=
    IsSplittingField.finiteDimensional p.SplittingField p
  letI : IsGalois ℚ p.SplittingField :=
    IsGalois.of_separable_splitting_field hp.separable
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  rw [map_sum]
  calc
    (∑ i : Fin 5, σ (rootTuple p hp hdeg i)) =
        ∑ i : Fin 5,
          rootTuple p hp hdeg (rootPermutationHom p hp hdeg σ i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact gal_maps_rootTuple p hp hdeg σ i
    _ = ∑ i : Fin 5, rootTuple p hp hdeg i :=
      Equiv.sum_comp (rootPermutationHom p hp hdeg σ) (rootTuple p hp hdeg)

theorem gal_isSolvable_iff_rootPermutationGroup_isSolvable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    IsSolvable p.Gal ↔ IsSolvable (rootPermutationGroup p hp hdeg) := by
  constructor
  · intro h
    letI : IsSolvable p.Gal := h
    exact solvable_of_surjective
      (f := (galEquivRootPermutationGroup p hp hdeg).toMonoidHom)
      (galEquivRootPermutationGroup p hp hdeg).surjective
  · intro h
    letI : IsSolvable (rootPermutationGroup p hp hdeg) := h
    exact solvable_of_surjective
      (f := (galEquivRootPermutationGroup p hp hdeg).symm.toMonoidHom)
      (galEquivRootPermutationGroup p hp hdeg).symm.surjective

theorem rootPermutationGroup_isSolvable_iff_le_conjugate_standardF20
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    IsSolvable (rootPermutationGroup p hp hdeg) ↔
      ∃ g : Equiv.Perm (Fin 5),
        rootPermutationGroup p hp hdeg ≤
          standardF20.map (MulAut.conj g).toMonoidHom := by
  letI : MulAction.IsPretransitive (rootPermutationGroup p hp hdeg) (Fin 5) :=
    rootPermutationGroup_isPretransitive p hp hdeg
  exact solvable_iff_le_conjugate_standardF20 _

/-- The finite-group criterion for an irreducible rational quintic. -/
theorem gal_isSolvable_iff_le_conjugate_standardF20
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    IsSolvable p.Gal ↔
      ∃ g : Equiv.Perm (Fin 5),
        rootPermutationGroup p hp hdeg ≤
          standardF20.map (MulAut.conj g).toMonoidHom := by
  rw [gal_isSolvable_iff_rootPermutationGroup_isSolvable,
    rootPermutationGroup_isSolvable_iff_le_conjugate_standardF20]

/-- Solvability can equivalently be read as the existence of one of the six
explicit `S₅ / F₂₀` representatives fixed by the whole Galois action. -/
theorem gal_isSolvable_iff_exists_fixed_representative_coset
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    IsSolvable p.Gal ↔
      ∃ i : Fin 6, ∀ σ : p.Gal,
        rootPermutationHom p hp hdeg σ •
            (Fin5TransitiveC5.representative i : Cosets) =
          (Fin5TransitiveC5.representative i : Cosets) := by
  rw [gal_isSolvable_iff_le_conjugate_standardF20 p hp hdeg,
    ← exists_fixed_representative_coset_iff_le_conjugate_standardF20
      (rootPermutationGroup p hp hdeg)]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, fun σ ↦ hi
      ⟨rootPermutationHom p hp hdeg σ, ⟨σ, rfl⟩⟩⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rintro ⟨g, ⟨σ, rfl⟩⟩
    exact hi σ

end LeanProofs.PolynomialFormulas.QuinticScalarGaloisBridge
