import Mathlib.FieldTheory.PolynomialGaloisGroup
import PolynomialFormulas.Fin6SolvableCriterion

/-!
# Galois groups of irreducible rational sextics as subgroups of `S₆`

An ordering of the six roots in the canonical splitting field gives a faithful
transitive permutation representation.  This is a noncomputable semantic
device; the later coefficient algorithm uses symmetric resolvents and does not
compute this ordering.
-/

open scoped Polynomial
open Equiv Polynomial

namespace LeanProofs.PolynomialFormulas.SexticScalarGaloisBridge

open LeanProofs.PolynomialFormulas.Fin6BlockSystems
open LeanProofs.PolynomialFormulas.Fin6SolvableCriterion

/-- A choice of ordering of the six roots in the canonical splitting field. -/
noncomputable def rootEquiv (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 6) : p.rootSet p.SplittingField ≃ Fin 6 :=
  Fintype.equivOfCardEq
    ((card_rootSet_eq_natDegree hp.separable (SplittingField.splits p)).trans hdeg)

/-- Faithful permutation representation on the ordered roots. -/
noncomputable def rootPermutationHom (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 6) : p.Gal →* S6 :=
  (rootEquiv p hp hdeg).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom p.Gal (p.rootSet p.SplittingField))

/-- The root-permutation image of the sextic Galois group. -/
noncomputable def rootPermutationGroup (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 6) : Subgroup S6 :=
  (rootPermutationHom p hp hdeg).range

theorem rootPermutationHom_injective (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 6) :
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

/-- The abstract Galois group is isomorphic to its permutation image. -/
noncomputable def galEquivRootPermutationGroup (p : ℚ[X])
    (hp : Irreducible p) (hdeg : p.natDegree = 6) :
    p.Gal ≃* rootPermutationGroup p hp hdeg :=
  MonoidHom.ofInjective (rootPermutationHom_injective p hp hdeg)

/-- Irreducibility makes the root-permutation image transitive. -/
theorem rootPermutationGroup_isPretransitive (p : ℚ[X])
    (hp : Irreducible p) (hdeg : p.natDegree = 6) :
    MulAction.IsPretransitive (rootPermutationGroup p hp hdeg) (Fin 6) := by
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
    (hdeg : p.natDegree = 6) : Fin 6 → p.SplittingField :=
  fun i ↦ rootEquiv p hp hdeg |>.symm i

/-- Galois automorphisms act on the tuple through `rootPermutationHom`. -/
theorem gal_maps_rootTuple (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 6) (σ : p.Gal) (i : Fin 6) :
    σ (rootTuple p hp hdeg i) =
      rootTuple p hp hdeg (rootPermutationHom p hp hdeg σ i) := by
  change σ ((rootEquiv p hp hdeg).symm i : p.SplittingField) =
    ((rootEquiv p hp hdeg).symm
      ((rootEquiv p hp hdeg)
        (σ • (rootEquiv p hp hdeg).symm i)) : p.SplittingField)
  rw [(rootEquiv p hp hdeg).symm_apply_apply]
  rfl

theorem rootTuple_injective (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 6) : Function.Injective (rootTuple p hp hdeg) := by
  intro i j hij
  apply (rootEquiv p hp hdeg).symm.injective
  apply Subtype.ext
  exact hij

theorem rootTuple_isRoot (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 6) (i : Fin 6) :
    (p.map (algebraMap ℚ p.SplittingField)).IsRoot (rootTuple p hp hdeg i) := by
  rw [Polynomial.IsRoot.def, eval_map, ← aeval_def]
  exact (mem_rootSet.mp ((rootEquiv p hp hdeg).symm i).property).2

/-- Factorization of the mapped monic sextic by the chosen roots. -/
theorem mapped_eq_prod_rootTuple (p : ℚ[X]) (hp : Irreducible p)
    (hmonic : p.Monic) (hdeg : p.natDegree = 6) :
    p.map (algebraMap ℚ p.SplittingField) =
      ∏ i : Fin 6, (X - C (rootTuple p hp hdeg i)) := by
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

/-- Fixed elements in the splitting field are exactly rational elements. -/
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

theorem gal_isSolvable_iff_rootPermutationGroup_isSolvable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6) :
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

/-- The finite group criterion for an irreducible rational sextic. -/
theorem gal_isSolvable_iff_le_pair_or_triple
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6) :
    IsSolvable p.Gal ↔
      (∃ b : PairPartition,
        rootPermutationGroup p hp hdeg ≤ pairStabilizer b) ∨
      (∃ b : TriplePartition,
        rootPermutationGroup p hp hdeg ≤ tripleStabilizer b) := by
  letI : MulAction.IsPretransitive
      (rootPermutationGroup p hp hdeg) (Fin 6) :=
    rootPermutationGroup_isPretransitive p hp hdeg
  rw [gal_isSolvable_iff_rootPermutationGroup_isSolvable]
  exact isSolvable_iff_le_pair_or_triple _

end LeanProofs.PolynomialFormulas.SexticScalarGaloisBridge
