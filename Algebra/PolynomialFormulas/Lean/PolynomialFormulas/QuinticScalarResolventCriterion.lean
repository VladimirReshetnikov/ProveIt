import PolynomialFormulas.QuinticScalarGaloisBridge
import PolynomialFormulas.FrobeniusDummitResolvent
import PolynomialFormulas.CertifiedDummitCoefficients

open scoped Polynomial
open Equiv MvPolynomial Polynomial

namespace LeanProofs.PolynomialFormulas.QuinticScalarResolventCriterion

open Fin5Solvable Fin5TransitiveC5
open QuinticScalarGaloisBridge
open FrobeniusDummitResolvent
open QuinticDummitCoefficients
open ComputableDummitCoefficients
open QuinticRadicalDecidability

example (i : Fin 6) :
    FrobeniusDummitResolvent.representative i =
      Fin5TransitiveC5.representative i := by rfl

theorem rename_thetaOrbit_eq_self_iff_mem_conjugate
    (g : Fin5Solvable.S5) (i : Fin 6) :
    rename g (thetaOrbit i) = thetaOrbit i ↔
      g ∈ standardF20.map
        (MulAut.conj (FrobeniusDummitResolvent.representative i)).toMonoidHom := by
  rw [Subgroup.mem_map_equiv, ← rename_theta_eq_theta_iff]
  constructor
  · intro h
    change rename
      ((FrobeniusDummitResolvent.representative i)⁻¹ * g *
        FrobeniusDummitResolvent.representative i) theta = theta
    have h' := congrArg
      (rename ((FrobeniusDummitResolvent.representative i)⁻¹ :
        Fin5Solvable.S5)) h
    have h'' :
        rename (fun x ↦
          (FrobeniusDummitResolvent.representative i)⁻¹
            (g (FrobeniusDummitResolvent.representative i x))) theta =
          rename (fun x : Fin 5 ↦ x) theta := by
      simpa [thetaOrbit, MvPolynomial.rename_rename, Function.comp_def] using h'
    have hid : rename (fun x : Fin 5 ↦ x) theta = theta := by
      change rename id theta = theta
      exact MvPolynomial.rename_id_apply theta
    convert h''.trans hid using 1
    apply congrArg (fun k : Fin 5 → Fin 5 ↦ rename k theta)
    funext x
    rfl
  · intro h
    change rename
      ((FrobeniusDummitResolvent.representative i)⁻¹ * g *
        FrobeniusDummitResolvent.representative i) theta = theta at h
    have h' := congrArg
      (rename (FrobeniusDummitResolvent.representative i)) h
    simpa [thetaOrbit, MvPolynomial.rename_rename, Function.comp_def,
      Function.id_def, MvPolynomial.rename_id_apply,
      MulAut.conj_apply] using h'

theorem rename_thetaOrbit_eq_self_iff_fixed_coset
    (g : Fin5Solvable.S5) (i : Fin 6) :
    rename g (thetaOrbit i) = thetaOrbit i ↔
      g • (Fin5TransitiveC5.representative i : Cosets) =
        (Fin5TransitiveC5.representative i : Cosets) := by
  rw [rename_thetaOrbit_eq_self_iff_mem_conjugate]
  change g ∈ standardF20.map
      (MulAut.conj (Fin5TransitiveC5.representative i)).toMonoidHom ↔ _
  have hstab : MulAction.stabilizer Fin5Solvable.S5
      (Fin5TransitiveC5.representative i : Cosets) =
        standardF20.map
          (MulAut.conj (Fin5TransitiveC5.representative i)).toMonoidHom := by
    change MulAction.stabilizer Fin5Solvable.S5
      (Fin5TransitiveC5.representative i •
        ((1 : Fin5Solvable.S5) : Cosets)) = _
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient]
  rw [← hstab, MulAction.mem_stabilizer_iff]

theorem map_thetaValue_eq_eval₂_rename {K L : Type*}
    [CommRing K] [CommRing L] (f : K →+* L)
    (r : Fin 5 → K) (s : Fin 5 → L) (g : Fin5Solvable.S5)
    (h : ∀ i, f (r i) = s (g i)) (i : Fin 6) :
    f (thetaValue r i) =
      MvPolynomial.eval₂ (Int.castRingHom L) s
        (rename g (thetaOrbit i)) := by
  rw [thetaValue, MvPolynomial.hom_eval₂]
  rw [MvPolynomial.eval₂_rename]
  have hcast : f.comp (Int.castRingHom K) = Int.castRingHom L := by
    ext z
    simp
  rw [hcast]
  apply MvPolynomial.eval₂_congr
  intro j _ _ _
  simpa only [Function.comp_apply] using h j

theorem gal_map_thetaValue (p : ℚ[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 5) (σ : p.Gal) (i : Fin 6) :
    σ (thetaValue (rootTuple p hp hdeg) i) =
      MvPolynomial.eval₂ (Int.castRingHom p.SplittingField)
        (rootTuple p hp hdeg)
        (rename (rootPermutationHom p hp hdeg σ) (thetaOrbit i)) := by
  exact map_thetaValue_eq_eval₂_rename σ.toRingHom
    (rootTuple p hp hdeg) (rootTuple p hp hdeg)
    (rootPermutationHom p hp hdeg σ)
    (gal_maps_rootTuple p hp hdeg σ) i

/-- Chapman's no-collision theorem applies after conjugating the regular
five-cycle contained in the transitive root-permutation group. -/
theorem thetaValue_rootTuple_injective
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    Function.Injective (thetaValue (rootTuple p hp hdeg)) := by
  let H := rootPermutationGroup p hp hdeg
  letI : MulAction.IsPretransitive H (Fin 5) :=
    rootPermutationGroup_isPretransitive p hp hdeg
  obtain ⟨g, hg⟩ := exists_map_conj_standardC5_le_of_pretransitive H
  have hcycle : g * fiveCycle * g⁻¹ ∈ H := by
    apply hg
    exact ⟨fiveCycle, Subgroup.mem_zpowers fiveCycle,
      MulAut.conj_apply g fiveCycle⟩
  obtain ⟨σ, hσ⟩ := hcycle
  let r := rootTuple p hp hdeg
  let r' : Fin 5 → p.SplittingField := fun i ↦ r (g i)
  have hr' : Function.Injective r' :=
    (rootTuple_injective p hp hdeg).comp g.injective
  have hroot' : (p.map (algebraMap ℚ p.SplittingField)).IsRoot (r' 1) :=
    rootTuple_isRoot p hp hdeg (g 1)
  have hsum' : r' 0 + r' 1 + r' 2 + r' 3 + r' 4 ∈
      Set.range (algebraMap ℚ p.SplittingField) := by
    have hsum : (∑ i : Fin 5, r' i) ∈
        Set.range (algebraMap ℚ p.SplittingField) := by
      rw [show (∑ i : Fin 5, r' i) = ∑ i : Fin 5, r i by
        exact Equiv.sum_comp g r]
      exact rootTuple_sum_mem_range p hp hdeg
    simpa [Fin.sum_univ_succ, r', add_assoc] using hsum
  have hσ' : ∀ k, σ.toRingHom (r' k) = r' (fiveCycle k) := by
    intro k
    rw [show σ.toRingHom (r' k) = σ (r' k) by rfl,
      gal_maps_rootTuple p hp hdeg σ (g k)]
    change r ((rootPermutationHom p hp hdeg σ) (g k)) = _
    rw [hσ]
    simp
    rfl
  have hinj' : Function.Injective (thetaValue r') :=
    thetaValue_injective_of_fiveCycle_action p hp hdeg r' hr' hroot'
      hsum' σ.toRingHom hσ'
  have hsep' : (scalarResolvent r').Separable := by
    rw [scalarResolvent_eq_prod, Polynomial.separable_prod_X_sub_C_iff]
    exact hinj'
  have hsep : (scalarResolvent r).Separable := by
    rw [← scalarResolvent_permute r g]
    exact hsep'
  rw [scalarResolvent_eq_prod,
    Polynomial.separable_prod_X_sub_C_iff] at hsep
  exact hsep

/-- The specialized six-factor Frobenius--Dummit resolvent is separable for
every irreducible rational quintic.  The collision-free orbit is derived by
the preceding Chapman argument, not supplied by the caller. -/
theorem scalarResolvent_rootTuple_separable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    (scalarResolvent (rootTuple p hp hdeg)).Separable := by
  rw [scalarResolvent_eq_prod,
    Polynomial.separable_prod_X_sub_C_iff]
  exact thetaValue_rootTuple_injective p hp hdeg

theorem gal_fixes_thetaValue_iff_fixed_coset
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5)
    (htheta : Function.Injective
      (thetaValue (rootTuple p hp hdeg))) (i : Fin 6) :
    (∀ σ : p.Gal,
        σ (thetaValue (rootTuple p hp hdeg) i) =
          thetaValue (rootTuple p hp hdeg) i) ↔
      ∀ σ : p.Gal,
        rootPermutationHom p hp hdeg σ •
            (Fin5TransitiveC5.representative i : Cosets) =
          (Fin5TransitiveC5.representative i : Cosets) := by
  constructor
  · intro hfix σ
    obtain ⟨j, hj⟩ := rename_thetaOrbit_exists
      (rootPermutationHom p hp hdeg σ) i
    have hmap := gal_map_thetaValue p hp hdeg σ i
    rw [hj] at hmap
    have hmap' :
        σ (thetaValue (rootTuple p hp hdeg) i) =
          thetaValue (rootTuple p hp hdeg) j := by
      simpa only [thetaValue] using hmap
    have hji : j = i := htheta (hmap'.symm.trans (hfix σ))
    subst j
    exact (rename_thetaOrbit_eq_self_iff_fixed_coset _ _).mp hj
  · intro hfix σ
    have horbit := (rename_thetaOrbit_eq_self_iff_fixed_coset _ _).mpr (hfix σ)
    have hmap := gal_map_thetaValue p hp hdeg σ i
    rw [horbit] at hmap
    simpa only [thetaValue] using hmap

theorem gal_isSolvable_iff_exists_fixed_thetaValue_of_injective
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5)
    (htheta : Function.Injective
      (thetaValue (rootTuple p hp hdeg))) :
    IsSolvable p.Gal ↔
      ∃ i : Fin 6, ∀ σ : p.Gal,
        σ (thetaValue (rootTuple p hp hdeg) i) =
          thetaValue (rootTuple p hp hdeg) i := by
  constructor
  · intro hsolv
    obtain ⟨i, hi⟩ :=
      (gal_isSolvable_iff_exists_fixed_representative_coset p hp hdeg).mp hsolv
    exact ⟨i, (gal_fixes_thetaValue_iff_fixed_coset p hp hdeg htheta i).mpr hi⟩
  · rintro ⟨i, hi⟩
    apply (gal_isSolvable_iff_exists_fixed_representative_coset p hp hdeg).mpr
    exact ⟨i, (gal_fixes_thetaValue_iff_fixed_coset p hp hdeg htheta i).mp hi⟩

theorem exists_thetaValue_mem_range_iff_gal_isSolvable_of_injective
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5)
    (htheta : Function.Injective
      (thetaValue (rootTuple p hp hdeg))) :
    (∃ i : Fin 6, thetaValue (rootTuple p hp hdeg) i ∈
      Set.range (algebraMap ℚ p.SplittingField)) ↔ IsSolvable p.Gal := by
  rw [gal_isSolvable_iff_exists_fixed_thetaValue_of_injective p hp hdeg htheta]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_range_algebraMap_iff_gal_fixed p hp _).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_range_algebraMap_iff_gal_fixed p hp _).mpr hi⟩

theorem scalarResolvent_has_rational_root_iff_gal_isSolvable_of_injective
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5)
    (htheta : Function.Injective
      (thetaValue (rootTuple p hp hdeg))) :
    (∃ q : ℚ, (scalarResolvent (rootTuple p hp hdeg)).IsRoot
      (algebraMap ℚ p.SplittingField q)) ↔ IsSolvable p.Gal := by
  rw [← exists_thetaValue_mem_range_iff_gal_isSolvable_of_injective
    p hp hdeg htheta]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨i, hi⟩ :=
      (scalarResolvent_isRoot_iff (rootTuple p hp hdeg) _).mp hq
    exact ⟨i, q, hi.symm⟩
  · rintro ⟨i, q, hq⟩
    refine ⟨q, (scalarResolvent_isRoot_iff (rootTuple p hp hdeg) _).mpr ?_⟩
    exact ⟨i, hq.symm⟩

theorem gal_isSolvable_iff_exists_fixed_thetaValue
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    IsSolvable p.Gal ↔
      ∃ i : Fin 6, ∀ σ : p.Gal,
        σ (thetaValue (rootTuple p hp hdeg) i) =
          thetaValue (rootTuple p hp hdeg) i :=
  gal_isSolvable_iff_exists_fixed_thetaValue_of_injective p hp hdeg
    (thetaValue_rootTuple_injective p hp hdeg)

theorem exists_thetaValue_mem_range_iff_gal_isSolvable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    (∃ i : Fin 6, thetaValue (rootTuple p hp hdeg) i ∈
      Set.range (algebraMap ℚ p.SplittingField)) ↔ IsSolvable p.Gal :=
  exists_thetaValue_mem_range_iff_gal_isSolvable_of_injective p hp hdeg
    (thetaValue_rootTuple_injective p hp hdeg)

theorem scalarResolvent_has_rational_root_iff_gal_isSolvable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    (∃ q : ℚ, (scalarResolvent (rootTuple p hp hdeg)).IsRoot
      (algebraMap ℚ p.SplittingField q)) ↔ IsSolvable p.Gal :=
  scalarResolvent_has_rational_root_iff_gal_isSolvable_of_injective
    p hp hdeg (thetaValue_rootTuple_injective p hp hdeg)

/-- The executable integral Dummit sextic has a rational root exactly when
the irreducible monic quintic has solvable Galois group. -/
theorem explicitDummitCoefficients_hasRationalRoot_iff_gal_isSolvable
    (f : MonicQuintic)
    (hp : Irreducible (monicQuinticRatPolynomial f)) :
    (explicitDummitCoefficients f).HasRationalRoot ↔
      IsSolvable (monicQuinticRatPolynomial f).Gal := by
  let p := monicQuinticRatPolynomial f
  let L := p.SplittingField
  let A := explicitDummitCoefficients f
  let r := rootTuple p hp (monicQuinticRatPolynomial_natDegree f)
  have hmap : A.polynomial.map (Int.castRingHom L) = scalarResolvent r := by
    dsimp only [A]
    rw [explicitDummitCoefficients_eq_dummitCoefficients]
    exact dummitPolynomial_map_eq_scalarResolvent_rootTuple f hp
  have hpolyMap :
      (A.polynomial.map (Int.castRingHom ℚ)).map (algebraMap ℚ L) =
        A.polynomial.map (Int.castRingHom L) := by
    rw [Polynomial.map_map]
    congr 1
  rw [← scalarResolvent_has_rational_root_iff_gal_isSolvable
    p hp (monicQuinticRatPolynomial_natDegree f)]
  constructor
  · rintro ⟨q, hq⟩
    have hq' : (A.polynomial.map (Int.castRingHom ℚ)).IsRoot q := by
      simpa [A, Polynomial.IsRoot, Polynomial.eval_map,
        Polynomial.aeval_def, RingHom.eq_intCast' (algebraMap ℤ ℚ)] using hq
    have hqL := Polynomial.IsRoot.map (f := algebraMap ℚ L) hq'
    rw [hpolyMap, hmap] at hqL
    exact ⟨q, hqL⟩
  · rintro ⟨q, hq⟩
    rw [← hmap, ← hpolyMap] at hq
    have hq' := hq.of_map (algebraMap ℚ L).injective
    refine ⟨q, ?_⟩
    simpa [A, Polynomial.IsRoot, Polynomial.eval_map,
      Polynomial.aeval_def, RingHom.eq_intCast' (algebraMap ℤ ℚ)] using hq'

/-- The finite rational-root search on the concrete Dummit sextic is the
executable solvability test for an irreducible monic quintic. -/
theorem explicitDummitRationalRootSearch_iff_gal_isSolvable
    (f : MonicQuintic)
    (hp : Irreducible (monicQuinticRatPolynomial f)) :
    (explicitDummitCoefficients f).rationalRootSearch = true ↔
      IsSolvable (monicQuinticRatPolynomial f).Gal := by
  rw [(explicitDummitCoefficients f).rationalRootSearch_iff_hasRationalRoot
      (by simp),
    explicitDummitCoefficients_hasRationalRoot_iff_gal_isSolvable f hp]

end LeanProofs.PolynomialFormulas.QuinticScalarResolventCriterion
