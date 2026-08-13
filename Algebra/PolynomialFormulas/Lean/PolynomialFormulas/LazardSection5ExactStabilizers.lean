import PolynomialFormulas.Fin5DihedralCore
import PolynomialFormulas.LazardGeneralResolventExplicit
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Lazard's degree-two and degree-three stabilizer witnesses in five variables

This file formalizes the concrete degree claims used in Section 5:

* the quadratic edge sum `∑ i, X_i X_{i+1}` has exact stabilizer `D₅`;
* the oriented cubic sum `∑ i, X_i² X_{i+1}` has exact stabilizer `C₅`;
* a homogeneous `C₅`-invariant of degree at most two is automatically
  reflection-, hence `D₅`-, invariant;
* a homogeneous `D₅`-invariant of degree at most one is fixed by all of
  `S₅`, so it cannot have exact stabilizer `D₅`.

The two finite orbit facts are ordinary `decide` certificates.  Their use for
arbitrary coefficient rings is proved coefficient-by-coefficient; the
polynomial conclusions are not obtained by evaluating coefficients.

This module is source-only until the focused finite computations and the public
import graph have been kernel-checked.
-/

open scoped BigOperators
open Equiv MvPolynomial

namespace LeanProofs.PolynomialFormulas.LazardSection5ExactStabilizers

/- Lean 4.32 has no namespace-assignment aliases.  Keep the short names local
and re-export only this file's dependency surface. -/
namespace Classification
export LeanProofs.PolynomialFormulas.Fin5DihedralCore
  (S5 fiveCycle fiveCycle_mem_standardD5 mem_standardD5_iff natCard_S5
    natCard_standardD5 reflection reflection_mem_standardD5 standardC5
    standardD5 standardD5_eq_closure)
end Classification

namespace FDR
export LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent
  (Exponent actExponent c5Elements finsupp_actExponent mem_c5Elements_iff
    permuteSupport polynomialOfSupport polynomialOfSupport_injective
    rename_polynomialOfSupport)
end FDR

namespace Exact
export LeanProofs.PolynomialFormulas.LazardGeneralResolventExplicit
  (HasExactRenameStabilizer InvariantUnder mem_renameStabilizer renameAction
    renameAction_mul renameAction_one renameStabilizer)
end Exact

abbrev S5 := Classification.S5
abbrev Exponent := FDR.Exponent
abbrev fiveCycle : S5 := Classification.fiveCycle
abbrev reflection : S5 := Classification.reflection
abbrev standardC5 : Subgroup S5 := Classification.standardC5
abbrev standardD5 : Subgroup S5 := Classification.standardD5

/-! ## The two displayed polynomials -/

/-- Exponent vector of the undirected edge monomial `X_i X_{i+1}`. -/
def edgeExponent (i : Fin 5) : Exponent := fun j ↦
  if j = i ∨ j = fiveCycle i then 1 else 0

theorem edgeExponent_injective : Function.Injective edgeExponent := by
  decide

def edgeSupport : Finset Exponent :=
  Finset.univ.image edgeExponent

/-- Lazard's quadratic edge sum `∑ i, X_i X_{i+1}`, represented by its
five distinct coefficient-one monomials. -/
noncomputable def quadraticEdgeSum : MvPolynomial (Fin 5) ℤ :=
  FDR.polynomialOfSupport edgeSupport

/-- Exponent vector of the oriented monomial `X_i² X_{i+1}`. -/
def orientedCubicExponent (i : Fin 5) : Exponent := fun j ↦
  if j = i then 2 else if j = fiveCycle i then 1 else 0

theorem orientedCubicExponent_injective :
    Function.Injective orientedCubicExponent := by
  decide

def orientedCubicSupport : Finset Exponent :=
  Finset.univ.image orientedCubicExponent

/-- Lazard's oriented cubic sum `∑ i, X_i² X_{i+1}`, represented by its
five distinct coefficient-one monomials. -/
noncomputable def orientedCubicSum : MvPolynomial (Fin 5) ℤ :=
  FDR.polynomialOfSupport orientedCubicSupport

set_option maxRecDepth 100000 in
theorem edgeSupport_stabilizer_certificate :
    ∀ g : S5,
      FDR.permuteSupport g edgeSupport = edgeSupport ↔ g ∈ standardD5 := by
  simp only [Classification.mem_standardD5_iff]
  decide

set_option maxRecDepth 100000 in
theorem orientedCubicSupport_stabilizer_certificate :
    ∀ g : S5,
      FDR.permuteSupport g orientedCubicSupport = orientedCubicSupport ↔
        g ∈ FDR.c5Elements := by
  decide

theorem rename_quadraticEdgeSum_eq_iff (g : S5) :
    MvPolynomial.rename g quadraticEdgeSum = quadraticEdgeSum ↔
      g ∈ standardD5 := by
  rw [quadraticEdgeSum, FDR.rename_polynomialOfSupport]
  constructor
  · intro h
    exact (edgeSupport_stabilizer_certificate g).mp
      (FDR.polynomialOfSupport_injective h)
  · intro h
    exact congrArg FDR.polynomialOfSupport
      ((edgeSupport_stabilizer_certificate g).mpr h)

theorem rename_orientedCubicSum_eq_iff (g : S5) :
    MvPolynomial.rename g orientedCubicSum = orientedCubicSum ↔
      g ∈ standardC5 := by
  rw [orientedCubicSum, FDR.rename_polynomialOfSupport]
  constructor
  · intro h
    apply (FDR.mem_c5Elements_iff g).mp
    exact (orientedCubicSupport_stabilizer_certificate g).mp
      (FDR.polynomialOfSupport_injective h)
  · intro h
    apply congrArg FDR.polynomialOfSupport
    apply (orientedCubicSupport_stabilizer_certificate g).mpr
    exact (FDR.mem_c5Elements_iff g).mpr h

/-- The quadratic edge sum has exact renaming stabilizer `D₅`. -/
theorem quadraticEdgeSum_hasExactRenameStabilizer :
    Exact.HasExactRenameStabilizer standardD5 quadraticEdgeSum := by
  unfold Exact.HasExactRenameStabilizer
  ext g
  change MvPolynomial.rename g quadraticEdgeSum = quadraticEdgeSum ↔
    g ∈ standardD5
  exact rename_quadraticEdgeSum_eq_iff g

/-- The oriented cubic sum has exact renaming stabilizer `C₅`. -/
theorem orientedCubicSum_hasExactRenameStabilizer :
    Exact.HasExactRenameStabilizer standardC5 orientedCubicSum := by
  unfold Exact.HasExactRenameStabilizer
  ext g
  change MvPolynomial.rename g orientedCubicSum = orientedCubicSum ↔
    g ∈ standardC5
  exact rename_orientedCubicSum_eq_iff g

/-! The paper works over the rational function field.  The integral
coefficient-one formulas above are convenient for the finite support
calculation; the following definitions and lemmas transport the same literal
formulas to `ℚ`, using injectivity of `ℤ → ℚ` to retain the *exact*
stabilizers. -/

/-- The rational quadratic edge sum. -/
noncomputable def quadraticEdgeSumRat : MvPolynomial (Fin 5) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) quadraticEdgeSum

/-- The rational oriented cubic sum. -/
noncomputable def orientedCubicSumRat : MvPolynomial (Fin 5) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) orientedCubicSum

theorem rename_quadraticEdgeSumRat_eq_iff (g : S5) :
    MvPolynomial.rename g quadraticEdgeSumRat = quadraticEdgeSumRat ↔
      g ∈ standardD5 := by
  constructor
  · intro h
    apply (rename_quadraticEdgeSum_eq_iff g).mp
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa only [quadraticEdgeSumRat, MvPolynomial.map_rename] using h
  · intro h
    have hZ := (rename_quadraticEdgeSum_eq_iff g).mpr h
    have hQ := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hZ
    simpa only [quadraticEdgeSumRat, MvPolynomial.map_rename] using hQ

theorem rename_orientedCubicSumRat_eq_iff (g : S5) :
    MvPolynomial.rename g orientedCubicSumRat = orientedCubicSumRat ↔
      g ∈ standardC5 := by
  constructor
  · intro h
    apply (rename_orientedCubicSum_eq_iff g).mp
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa only [orientedCubicSumRat, MvPolynomial.map_rename] using h
  · intro h
    have hZ := (rename_orientedCubicSum_eq_iff g).mpr h
    have hQ := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hZ
    simpa only [orientedCubicSumRat, MvPolynomial.map_rename] using hQ

/-- Over `ℚ`, the quadratic edge sum has exact renaming stabilizer `D₅`. -/
theorem quadraticEdgeSumRat_hasExactRenameStabilizer :
    Exact.HasExactRenameStabilizer standardD5 quadraticEdgeSumRat := by
  unfold Exact.HasExactRenameStabilizer
  ext g
  change MvPolynomial.rename g quadraticEdgeSumRat = quadraticEdgeSumRat ↔
    g ∈ standardD5
  exact rename_quadraticEdgeSumRat_eq_iff g

/-- Over `ℚ`, the oriented cubic sum has exact renaming stabilizer `C₅`. -/
theorem orientedCubicSumRat_hasExactRenameStabilizer :
    Exact.HasExactRenameStabilizer standardC5 orientedCubicSumRat := by
  unfold Exact.HasExactRenameStabilizer
  ext g
  change MvPolynomial.rename g orientedCubicSumRat = orientedCubicSumRat ↔
    g ∈ standardC5
  exact rename_orientedCubicSumRat_eq_iff g

theorem edgeExponent_sum (i : Fin 5) :
    ∑ j : Fin 5, edgeExponent i j = 2 := by
  fin_cases i <;> decide

theorem orientedCubicExponent_sum (i : Fin 5) :
    ∑ j : Fin 5, orientedCubicExponent i j = 3 := by
  fin_cases i <;> decide

theorem quadraticEdgeSum_isHomogeneous :
    quadraticEdgeSum.IsHomogeneous 2 := by
  classical
  rw [quadraticEdgeSum, FDR.polynomialOfSupport]
  apply MvPolynomial.IsHomogeneous.sum edgeSupport
  intro d hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum]
  simpa using edgeExponent_sum i

theorem orientedCubicSum_isHomogeneous :
    orientedCubicSum.IsHomogeneous 3 := by
  classical
  rw [orientedCubicSum, FDR.polynomialOfSupport]
  apply MvPolynomial.IsHomogeneous.sum orientedCubicSupport
  intro d hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum]
  simpa using orientedCubicExponent_sum i

theorem quadraticEdgeSumRat_isHomogeneous :
    quadraticEdgeSumRat.IsHomogeneous 2 := by
  simpa only [quadraticEdgeSumRat] using
    quadraticEdgeSum_isHomogeneous.map (Int.castRingHom ℚ)

theorem orientedCubicSumRat_isHomogeneous :
    orientedCubicSumRat.IsHomogeneous 3 := by
  simpa only [orientedCubicSumRat] using
    orientedCubicSum_isHomogeneous.map (Int.castRingHom ℚ)

/-! ## Finite monomial-orbit lemmas -/

/-- Every exponent occurring in degree at most two has every coordinate below
three, so it can be represented by this finite type. -/
abbrev SmallExponent := Fin 5 → Fin 3

def actSmallExponent (g : S5) (d : SmallExponent) : SmallExponent :=
  fun i ↦ d (g.symm i)

set_option maxRecDepth 100000 in
theorem reflection_degree_le_two_orbit_certificate :
    ∀ d : SmallExponent, (∑ i : Fin 5, (d i : ℕ)) ≤ 2 →
      ∃ k : Fin 5,
        actSmallExponent reflection d =
          actSmallExponent (fiveCycle ^ (k : ℕ)) d := by
  decide

set_option maxRecDepth 100000 in
theorem permutation_degree_le_one_orbit_certificate :
    ∀ (g : S5) (d : SmallExponent), (∑ i : Fin 5, (d i : ℕ)) ≤ 1 →
      ∃ k : Fin 5,
        actSmallExponent g d =
          actSmallExponent (fiveCycle ^ (k : ℕ)) d := by
  decide

def exponentToSmall (d : Fin 5 →₀ ℕ) (bound : d.degree ≤ 2) :
    SmallExponent := fun i ↦ ⟨d i, by
  have hsum : ∑ j : Fin 5, d j ≤ 2 := by
    simpa only [Finsupp.degree_eq_sum] using bound
  have hi : d i ≤ ∑ j : Fin 5, d j :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (d j)) (Finset.mem_univ i)
  omega⟩

@[simp] lemma exponentToSmall_val (d : Fin 5 →₀ ℕ) (bound : d.degree ≤ 2)
    (i : Fin 5) : (exponentToSmall d bound i : ℕ) = d i :=
  rfl

lemma mapDomain_eq_of_small_action_eq (d : Fin 5 →₀ ℕ)
    (bound : d.degree ≤ 2) (g h : S5)
    (haction : actSmallExponent g (exponentToSmall d bound) =
      actSmallExponent h (exponentToSmall d bound)) :
    d.mapDomain g = d.mapDomain h := by
  have hfun : FDR.actExponent g (fun i ↦ d i) =
      FDR.actExponent h (fun i ↦ d i) := by
    funext i
    exact congrArg Fin.val (congrFun haction i)
  have hd : Finsupp.equivFunOnFinite.symm (fun i ↦ d i) = d := by
    ext i
    simp
  calc
    d.mapDomain g =
        (Finsupp.equivFunOnFinite.symm (fun i ↦ d i)).mapDomain g := by
          rw [hd]
    _ = Finsupp.equivFunOnFinite.symm
          (FDR.actExponent g (fun i ↦ d i)) :=
        FDR.finsupp_actExponent g (fun i ↦ d i)
    _ = Finsupp.equivFunOnFinite.symm
          (FDR.actExponent h (fun i ↦ d i)) := congrArg _ hfun
    _ = (Finsupp.equivFunOnFinite.symm (fun i ↦ d i)).mapDomain h :=
        (FDR.finsupp_actExponent h (fun i ↦ d i)).symm
    _ = d.mapDomain h := by rw [hd]

theorem reflection_matches_rotation_of_degree_le_two
    (d : Fin 5 →₀ ℕ) (bound : d.degree ≤ 2) :
    ∃ k : ℕ, d.mapDomain reflection = d.mapDomain (fiveCycle ^ k) := by
  have hsum : ∑ i : Fin 5, (exponentToSmall d bound i : ℕ) ≤ 2 := by
    simpa only [exponentToSmall_val, Finsupp.degree_eq_sum] using bound
  obtain ⟨k, hk⟩ := reflection_degree_le_two_orbit_certificate
    (exponentToSmall d bound) hsum
  exact ⟨k, mapDomain_eq_of_small_action_eq d bound reflection
    (fiveCycle ^ (k : ℕ)) hk⟩

theorem permutation_matches_rotation_of_degree_le_one
    (g : S5) (d : Fin 5 →₀ ℕ) (bound : d.degree ≤ 1) :
    ∃ k : ℕ, d.mapDomain g = d.mapDomain (fiveCycle ^ k) := by
  have boundTwo : d.degree ≤ 2 := bound.trans (by omega)
  have hsum : ∑ i : Fin 5, (exponentToSmall d boundTwo i : ℕ) ≤ 1 := by
    simpa only [exponentToSmall_val, Finsupp.degree_eq_sum] using bound
  obtain ⟨k, hk⟩ := permutation_degree_le_one_orbit_certificate g
    (exponentToSmall d boundTwo) hsum
  exact ⟨k, mapDomain_eq_of_small_action_eq d boundTwo g
    (fiveCycle ^ (k : ℕ)) hk⟩

/-! ## Passing the finite orbit facts to arbitrary coefficients -/

theorem rename_fiveCycle_pow_eq {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 5) R)
    (hcycle : MvPolynomial.rename fiveCycle p = p) (k : ℕ) :
    MvPolynomial.rename (fiveCycle ^ k) p = p := by
  change Exact.renameAction (fiveCycle ^ k) p = p
  change Exact.renameAction fiveCycle p = p at hcycle
  induction k with
  | zero => exact Exact.renameAction_one p
  | succ k ih =>
      rw [pow_succ, Exact.renameAction_mul, hcycle, ih]

/-- Repeated coefficient-orbit argument used in both lower bounds. -/
theorem rename_eq_of_rotation_orbits {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 5) R) (n : ℕ) (g : S5)
    (homogeneous : p.IsHomogeneous n)
    (hcycle : MvPolynomial.rename fiveCycle p = p)
    (orbits : ∀ d : Fin 5 →₀ ℕ, d.degree = n →
      ∃ k : ℕ, d.mapDomain g = d.mapDomain (fiveCycle ^ k)) :
    MvPolynomial.rename g p = p := by
  classical
  apply MvPolynomial.ext
  intro e
  let d : Fin 5 →₀ ℕ := e.mapDomain g.symm
  have hdg : d.mapDomain g = e := by
    change (e.mapDomain g.symm).mapDomain g = e
    rw [← Finsupp.mapDomain_comp]
    have hcomp :
        (g : Fin 5 → Fin 5) ∘ (g.symm : Fin 5 → Fin 5) = id := by
      funext x
      exact g.apply_symm_apply x
    rw [hcomp, Finsupp.mapDomain_id]
  rw [← hdg, MvPolynomial.coeff_rename_mapDomain g g.injective]
  by_cases hdegree : d.degree = n
  · obtain ⟨k, hk⟩ := orbits d hdegree
    have hpow := rename_fiveCycle_pow_eq p hcycle k
    have hcoeff := congrArg
      (MvPolynomial.coeff (d.mapDomain (fiveCycle ^ k))) hpow
    rw [MvPolynomial.coeff_rename_mapDomain
      (fiveCycle ^ k) (fiveCycle ^ k).injective] at hcoeff
    rw [hk]
    exact hcoeff
  · have hdegree' : (d.mapDomain g).degree ≠ n := by
      simpa using hdegree
    rw [homogeneous.coeff_eq_zero hdegree,
      homogeneous.coeff_eq_zero hdegree']

/-- The same coefficient-orbit argument for an arbitrary polynomial of
bounded total degree.  Splitting into homogeneous components is essential:
the minimum-degree assertion in the paper is about the degree of an
invariant, not only about invariants which happened already to be
homogeneous. -/
theorem rename_eq_of_rotation_orbits_totalDegree_le
    {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 5) R) (n : ℕ) (g : S5)
    (degree_le : p.totalDegree ≤ n)
    (hcycle : MvPolynomial.rename fiveCycle p = p)
    (orbits : ∀ d : Fin 5 →₀ ℕ, d.degree ≤ n →
      ∃ k : ℕ, d.mapDomain g = d.mapDomain (fiveCycle ^ k)) :
    MvPolynomial.rename g p = p := by
  classical
  calc
    MvPolynomial.rename g p =
        MvPolynomial.rename g
          (∑ d ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.homogeneousComponent d p) := by
      rw [MvPolynomial.sum_homogeneousComponent]
    _ = ∑ d ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.rename g
            (MvPolynomial.homogeneousComponent d p) := by
      simp
    _ = ∑ d ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.homogeneousComponent d p := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdle : d ≤ n := by
        have hdlt : d < p.totalDegree + 1 := Finset.mem_range.mp hd
        have : d ≤ p.totalDegree := by omega
        exact this.trans degree_le
      have hcycleComponent :
          MvPolynomial.rename fiveCycle
              (MvPolynomial.homogeneousComponent d p) =
            MvPolynomial.homogeneousComponent d p := by
        rw [MvPolynomial.rename_homogeneousComponent, hcycle]
      exact rename_eq_of_rotation_orbits
        (MvPolynomial.homogeneousComponent d p) d g
        (MvPolynomial.homogeneousComponent_isHomogeneous d p)
        hcycleComponent (fun e he ↦ orbits e (he.le.trans hdle))
    _ = p := MvPolynomial.sum_homogeneousComponent p

/-- Degree at most two cannot distinguish the two orientations of a 5-cycle. -/
theorem reflection_invariant_of_C5_invariant_degree_le_two
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R) (n : ℕ)
    (homogeneous : p.IsHomogeneous n) (degree_le : n ≤ 2)
    (hcycle : MvPolynomial.rename fiveCycle p = p) :
    MvPolynomial.rename reflection p = p := by
  apply rename_eq_of_rotation_orbits p n reflection homogeneous hcycle
  intro d hd
  apply reflection_matches_rotation_of_degree_le_two d
  omega

/-- Paper-facing lower bound: every homogeneous `C₅`-invariant of degree at
most two is already invariant under all of `D₅`. -/
theorem D5_invariant_of_C5_invariant_degree_le_two
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R) (n : ℕ)
    (homogeneous : p.IsHomogeneous n) (degree_le : n ≤ 2)
    (hcycle : MvPolynomial.rename fiveCycle p = p) :
    Exact.InvariantUnder standardD5 p := by
  have hreflection := reflection_invariant_of_C5_invariant_degree_le_two
    p n homogeneous degree_le hcycle
  have hfive : fiveCycle ∈ Exact.renameStabilizer p := by
    exact hcycle
  have href : reflection ∈ Exact.renameStabilizer p := by
    exact hreflection
  have hD : standardD5 ≤ Exact.renameStabilizer p := by
    change Classification.standardD5 ≤ Exact.renameStabilizer p
    rw [Classification.standardD5_eq_closure, Subgroup.closure_le]
    simpa only [Set.insert_subset_iff, Set.singleton_subset_iff]
      using ⟨hfive, href⟩
  intro g hg
  exact (Exact.mem_renameStabilizer p g).mp (hD hg)

/-- Arbitrary-polynomial form of the `C5` lower bound: total degree at most
two already forces reflection invariance and hence invariance under all of
`D5`. -/
theorem D5_invariant_of_C5_invariant_totalDegree_le_two
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R)
    (degree_le : p.totalDegree ≤ 2)
    (hC : Exact.InvariantUnder standardC5 p) :
    Exact.InvariantUnder standardD5 p := by
  have hcycle : MvPolynomial.rename fiveCycle p = p :=
    hC fiveCycle (by
      apply (FDR.mem_c5Elements_iff fiveCycle).mp
      decide)
  have hreflection : MvPolynomial.rename reflection p = p := by
    apply rename_eq_of_rotation_orbits_totalDegree_le p 2 reflection
      degree_le hcycle
    intro d hd
    exact reflection_matches_rotation_of_degree_le_two d hd
  have hfive : fiveCycle ∈ Exact.renameStabilizer p := hcycle
  have href : reflection ∈ Exact.renameStabilizer p := hreflection
  have hD : standardD5 ≤ Exact.renameStabilizer p := by
    change Classification.standardD5 ≤ Exact.renameStabilizer p
    rw [Classification.standardD5_eq_closure, Subgroup.closure_le]
    simpa only [Set.insert_subset_iff, Set.singleton_subset_iff]
      using ⟨hfive, href⟩
  intro g hg
  exact (Exact.mem_renameStabilizer p g).mp (hD hg)

theorem fiveCycle_mem_standardC5 : fiveCycle ∈ standardC5 := by
  apply (FDR.mem_c5Elements_iff fiveCycle).mp
  decide

theorem reflection_not_mem_standardC5 : reflection ∉ standardC5 := by
  intro hreflection
  have hreflectionFinset : reflection ∈ FDR.c5Elements :=
    (FDR.mem_c5Elements_iff reflection).mpr hreflection
  have hreflectionNotFinset : reflection ∉ FDR.c5Elements := by decide
  exact hreflectionNotFinset hreflectionFinset

/-- Consequently, no homogeneous polynomial of degree at most two can have
exact stabilizer `C₅`.  Together with the rational oriented cubic witness,
this is the exact minimal-degree claim for `C₅`. -/
theorem no_exact_C5_stabilizer_in_degree_le_two
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R) (n : ℕ)
    (homogeneous : p.IsHomogeneous n) (degree_le : n ≤ 2)
    (hC : Exact.InvariantUnder standardC5 p) :
    ¬ Exact.HasExactRenameStabilizer standardC5 p := by
  intro hexact
  have hcycle : MvPolynomial.rename fiveCycle p = p :=
    hC fiveCycle fiveCycle_mem_standardC5
  have hreflection := reflection_invariant_of_C5_invariant_degree_le_two
    p n homogeneous degree_le hcycle
  have hreflectionStabilizer : reflection ∈ Exact.renameStabilizer p :=
    (Exact.mem_renameStabilizer p reflection).mpr hreflection
  have hreflectionC5 : reflection ∈ standardC5 := by
    rw [← hexact]
    exact hreflectionStabilizer
  exact reflection_not_mem_standardC5 hreflectionC5

/-- No arbitrary polynomial of total degree at most two has exact renaming
stabilizer `C5`.  Together with the rational oriented-cubic witness this is
the literal minimum-degree-three statement. -/
theorem no_exact_C5_stabilizer_totalDegree_le_two
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R)
    (degree_le : p.totalDegree ≤ 2)
    (hC : Exact.InvariantUnder standardC5 p) :
    ¬ Exact.HasExactRenameStabilizer standardC5 p := by
  intro hexact
  have hD := D5_invariant_of_C5_invariant_totalDegree_le_two
    p degree_le hC
  have hreflection : reflection ∈ Exact.renameStabilizer p := by
    exact hD reflection Classification.reflection_mem_standardD5
  have hreflectionC5 : reflection ∈ standardC5 := by
    rw [← hexact]
    exact hreflection
  exact reflection_not_mem_standardC5 hreflectionC5

/-- Every permutation has the same action as some rotation on monomials of
degree at most one. -/
theorem S5_invariant_of_C5_invariant_degree_le_one
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R) (n : ℕ)
    (homogeneous : p.IsHomogeneous n) (degree_le : n ≤ 1)
    (hcycle : MvPolynomial.rename fiveCycle p = p) :
    ∀ g : S5, MvPolynomial.rename g p = p := by
  intro g
  apply rename_eq_of_rotation_orbits p n g homogeneous hcycle
  intro d hd
  apply permutation_matches_rotation_of_degree_le_one g d
  omega

/-- Arbitrary-polynomial form of the linear lower bound: a cyclic-invariant
polynomial of total degree at most one is fully symmetric. -/
theorem S5_invariant_of_C5_invariant_totalDegree_le_one
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R)
    (degree_le : p.totalDegree ≤ 1)
    (hcycle : MvPolynomial.rename fiveCycle p = p) :
    ∀ g : S5, MvPolynomial.rename g p = p := by
  intro g
  apply rename_eq_of_rotation_orbits_totalDegree_le p 1 g degree_le hcycle
  intro d hd
  exact permutation_matches_rotation_of_degree_le_one g d hd

theorem standardD5_ne_top : standardD5 ≠ (⊤ : Subgroup S5) := by
  intro h
  have hcard := congrArg (fun H : Subgroup S5 ↦ Nat.card H) h
  rw [Classification.natCard_standardD5] at hcard
  have htop : Nat.card (⊤ : Subgroup S5) = 120 := by
    simpa using Classification.natCard_S5
  rw [htop] at hcard
  omega

/-- Degree at most one cannot have exact stabilizer `D₅`: transitivity makes
every such `D₅`-invariant fully symmetric. -/
theorem no_exact_D5_stabilizer_in_degree_le_one
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R) (n : ℕ)
    (homogeneous : p.IsHomogeneous n) (degree_le : n ≤ 1)
    (hD : Exact.InvariantUnder standardD5 p) :
    ¬ Exact.HasExactRenameStabilizer standardD5 p := by
  intro hexact
  have hcycle : MvPolynomial.rename fiveCycle p = p := by
    exact hD fiveCycle Classification.fiveCycle_mem_standardD5
  have hall := S5_invariant_of_C5_invariant_degree_le_one
    p n homogeneous degree_le hcycle
  have htop : Exact.renameStabilizer p = (⊤ : Subgroup S5) := by
    ext g
    change MvPolynomial.rename g p = p ↔ True
    simp only [hall g, true_iff]
  apply standardD5_ne_top
  exact hexact.symm.trans htop

/-- No arbitrary polynomial of total degree at most one has exact renaming
stabilizer `D5`.  Together with the rational quadratic witness this is the
literal minimum-degree-two statement. -/
theorem no_exact_D5_stabilizer_totalDegree_le_one
    {R : Type*} [CommRing R] (p : MvPolynomial (Fin 5) R)
    (degree_le : p.totalDegree ≤ 1)
    (hD : Exact.InvariantUnder standardD5 p) :
    ¬ Exact.HasExactRenameStabilizer standardD5 p := by
  intro hexact
  have hcycle : MvPolynomial.rename fiveCycle p = p :=
    hD fiveCycle Classification.fiveCycle_mem_standardD5
  have hall := S5_invariant_of_C5_invariant_totalDegree_le_one
    p degree_le hcycle
  have htop : Exact.renameStabilizer p = (⊤ : Subgroup S5) := by
    ext g
    change MvPolynomial.rename g p = p ↔ True
    simp only [hall g, true_iff]
  apply standardD5_ne_top
  exact hexact.symm.trans htop

end LeanProofs.PolynomialFormulas.LazardSection5ExactStabilizers
