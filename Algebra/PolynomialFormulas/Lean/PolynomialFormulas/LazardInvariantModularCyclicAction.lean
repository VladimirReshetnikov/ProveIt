import PolynomialFormulas.LazardInvariantModularProductBridgeCore
import PolynomialFormulas.LazardInvariantModule
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.Tactic

/-!
# The concrete cyclic action and orbit-sum fixedness

This dependency-first shard contains the characteristic-free action,
rotation, and orbit-relation arguments used by the modular counterexample.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants

open scoped BigOperators
open Finset MvPolynomial
open LazardInvariantModule
open LazardInvariantModularCounterexample
open LazardInvariantModularOrbitCoordinates
open LazardInvariantModularProductBridge

set_option autoImplicit false

noncomputable section

def cycleSixGeneratorPermutation : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def cyclicSix : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.zpowers cycleSixGeneratorPermutation

def cyclicSixGenerator : cyclicSix :=
  ⟨cycleSixGeneratorPermutation, Subgroup.mem_zpowers _⟩

theorem cyclicSixGenerator_zpowers_top (g : cyclicSix) :
    g ∈ Subgroup.zpowers cyclicSixGenerator := by
  rcases g.2 with ⟨z, hz⟩
  refine ⟨z, Subtype.ext ?_⟩
  simpa [cyclicSixGenerator] using hz

def cycleSixRenameLinear :
    MvPolynomial (Fin 6) F3 →ₗ[F3] MvPolynomial (Fin 6) F3 :=
  (MvPolynomial.renameEquiv F3 cycleSixGeneratorPermutation).toLinearMap

@[simp]
theorem cycleSixRenameLinear_apply (p : MvPolynomial (Fin 6) F3) :
    cycleSixRenameLinear p =
      MvPolynomial.rename cycleSixGeneratorPermutation p :=
  rfl

theorem finsupp_mapDomain_cycleSixGenerator (a : Exponent) :
    (Finsupp.equivFunOnFinite.symm a).mapDomain
        cycleSixGeneratorPermutation =
      Finsupp.equivFunOnFinite.symm (rotateExponent a 1) := by
  ext i
  rw [Finsupp.mapDomain_equiv_apply]
  change a (cycleSixGeneratorPermutation.symm i) =
    a ⟨(i.1 + 1) % 6, Nat.mod_lt _ (by decide)⟩
  congr 1
  fin_cases i <;> rfl

theorem mem_cyclicSix_invariantSubalgebra_iff
    (p : MvPolynomial (Fin 6) F3) :
    p ∈ invariantSubalgebra F3 (Fin 6) cyclicSix ↔
      MvPolynomial.rename cycleSixGeneratorPermutation p = p := by
  change p ∈
      (subgroupRepresentation F3 (Fin 6) cyclicSix).invariants ↔ _
  simpa [cyclicSixGenerator] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers
      (subgroupRepresentation F3 (Fin 6) cyclicSix)
      cyclicSixGenerator cyclicSixGenerator_zpowers_top p

theorem rotateExponent_zero (a : Exponent) :
    rotateExponent a 0 = a := by
  funext i
  apply congrArg a
  apply Fin.ext
  simp [rotateExponent]

theorem rotateExponent_succ (a : Exponent) (k : ℕ) :
    rotateExponent (rotateExponent a k) 1 =
      rotateExponent a (k + 1) := by
  funext i
  apply congrArg a
  apply Fin.ext
  simp only [rotateExponent]
  omega

theorem coeff_rotateExponent_eq_of_fixed
    (p : MvPolynomial (Fin 6) F3)
    (hfixed : cycleSixRenameLinear p = p)
    (a : Exponent) (k : ℕ) :
    p.coeff (Finsupp.equivFunOnFinite.symm (rotateExponent a k)) =
      p.coeff (Finsupp.equivFunOnFinite.symm a) := by
  induction k with
  | zero => simp [rotateExponent_zero]
  | succ k ih =>
      rw [← rotateExponent_succ]
      calc
        p.coeff (Finsupp.equivFunOnFinite.symm
            (rotateExponent (rotateExponent a k) 1)) =
            p.coeff ((Finsupp.equivFunOnFinite.symm
              (rotateExponent a k)).mapDomain
                cycleSixGeneratorPermutation) := by
              rw [finsupp_mapDomain_cycleSixGenerator]
        _ = (MvPolynomial.rename cycleSixGeneratorPermutation p).coeff
              ((Finsupp.equivFunOnFinite.symm
                (rotateExponent a k)).mapDomain
                  cycleSixGeneratorPermutation) := by
              rw [show MvPolynomial.rename cycleSixGeneratorPermutation p = p by
                simpa using hfixed]
        _ = p.coeff (Finsupp.equivFunOnFinite.symm
              (rotateExponent a k)) :=
              MvPolynomial.coeff_rename_mapDomain _
                cycleSixGeneratorPermutation.injective _ _
        _ = p.coeff (Finsupp.equivFunOnFinite.symm a) := ih

theorem coeff_eq_of_mem_cyclicOrbitSupport
    (p : MvPolynomial (Fin 6) F3)
    (hfixed : cycleSixRenameLinear p = p)
    (a b : Exponent) (hb : b ∈ cyclicOrbitSupport a) :
    p.coeff (Finsupp.equivFunOnFinite.symm b) =
      p.coeff (Finsupp.equivFunOnFinite.symm a) := by
  simp only [cyclicOrbitSupport, List.mem_toFinset, cyclicOrbit,
    List.mem_eraseDups, List.mem_map] at hb
  rcases hb with ⟨k, hk, rfl⟩
  exact coeff_rotateExponent_eq_of_fixed p hfixed a k

theorem self_mem_cyclicOrbitSupport (a : Exponent) :
    a ∈ cyclicOrbitSupport a := by
  simp only [cyclicOrbitSupport, List.mem_toFinset, cyclicOrbit,
    List.mem_eraseDups, List.mem_map]
  exact ⟨0, List.mem_range.mpr (by omega), rotateExponent_zero a⟩

theorem rotateExponent_mem_cyclicOrbitSupport (a : Exponent) (k : ℕ)
    (hk : k < 6) :
    rotateExponent a k ∈ cyclicOrbitSupport a := by
  simp only [cyclicOrbitSupport, List.mem_toFinset, cyclicOrbit,
    List.mem_eraseDups, List.mem_map]
  exact ⟨k, List.mem_range.mpr hk, rfl⟩

theorem mem_cyclicOrbitSupport_symm {a b : Exponent}
    (hb : b ∈ cyclicOrbitSupport a) :
    a ∈ cyclicOrbitSupport b := by
  simp only [cyclicOrbitSupport, List.mem_toFinset, cyclicOrbit,
    List.mem_eraseDups, List.mem_map] at hb ⊢
  rcases hb with ⟨k, hk, rfl⟩
  refine ⟨(6 - k) % 6,
    List.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
  funext i
  apply congrArg a
  apply Fin.ext
  simp only [rotateExponent]
  have hk' : k < 6 := List.mem_range.mp hk
  omega

theorem mem_cyclicOrbitSupport_trans {a b c : Exponent}
    (hb : b ∈ cyclicOrbitSupport a)
    (hc : c ∈ cyclicOrbitSupport b) :
    c ∈ cyclicOrbitSupport a := by
  simp only [cyclicOrbitSupport, List.mem_toFinset, cyclicOrbit,
    List.mem_eraseDups, List.mem_map] at hb hc ⊢
  rcases hb with ⟨k, hk, rfl⟩
  rcases hc with ⟨l, hl, rfl⟩
  refine ⟨(k + l) % 6,
    List.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
  funext i
  apply congrArg a
  apply Fin.ext
  simp only [rotateExponent]
  omega

theorem mem_cyclicOrbitSupport_iff_of_mem {a b c : Exponent}
    (hb : b ∈ cyclicOrbitSupport c) :
    b ∈ cyclicOrbitSupport a ↔ c ∈ cyclicOrbitSupport a := by
  constructor
  · intro hba
    exact mem_cyclicOrbitSupport_trans hba
      (mem_cyclicOrbitSupport_symm hb)
  · intro hca
    exact mem_cyclicOrbitSupport_trans hca hb

theorem canonicalExponent_mem_cyclicOrbitSupport (a : Exponent) :
    canonicalExponent a ∈ cyclicOrbitSupport a := by
  change (cyclicOrbit a).foldl exponentMin a ∈ cyclicOrbitSupport a
  apply List.foldlRecOn
  · exact self_mem_cyclicOrbitSupport a
  · intro b hb c hc
    rw [exponentMin]
    split
    · simpa [cyclicOrbitSupport] using hc
    · exact hb

theorem canonicalExponent_mem_orbitRepresentatives (d : ℕ) (a : Exponent)
    (ha : a ∈ (degreeExponents d).toFinset) :
    canonicalExponent a ∈ (orbitRepresentatives d).toFinset := by
  have ha' : a ∈ degreeExponents d := by
    simpa using ha
  simp only [orbitRepresentatives, List.mem_toFinset,
    List.mem_eraseDups, List.mem_map]
  exact ⟨a, ha', rfl⟩

theorem equivFunOnFinite_comapDomain_cycleSixGenerator
    (m : Fin 6 →₀ ℕ) :
    Finsupp.equivFunOnFinite
        (Finsupp.comapDomain cycleSixGeneratorPermutation m
          cycleSixGeneratorPermutation.injective.injOn) =
      rotateExponent (Finsupp.equivFunOnFinite m) 5 := by
  funext i
  fin_cases i <;> rfl

theorem cyclicOrbitPolynomial_fixed_general (a : Exponent) :
    cycleSixRenameLinear (cyclicOrbitPolynomial a) =
      cyclicOrbitPolynomial a := by
  apply MvPolynomial.ext
  intro m
  let d : Fin 6 →₀ ℕ :=
    Finsupp.comapDomain cycleSixGeneratorPermutation m
      cycleSixGeneratorPermutation.injective.injOn
  have hd : d.mapDomain cycleSixGeneratorPermutation = m := by
    exact Finsupp.mapDomain_comapDomain
      cycleSixGeneratorPermutation
      cycleSixGeneratorPermutation.injective
      m (fun i _ =>
        ⟨cycleSixGeneratorPermutation.symm i, by simp⟩)
  let u : Exponent := Finsupp.equivFunOnFinite m
  have hdu : Finsupp.equivFunOnFinite d = rotateExponent u 5 := by
    exact equivFunOnFinite_comapDomain_cycleSixGenerator m
  have hrotation : rotateExponent u 5 ∈ cyclicOrbitSupport u :=
    rotateExponent_mem_cyclicOrbitSupport u 5 (by omega)
  have horbit :
      Finsupp.equivFunOnFinite d ∈ cyclicOrbitSupport a ↔
        u ∈ cyclicOrbitSupport a := by
    rw [hdu]
    exact mem_cyclicOrbitSupport_iff_of_mem hrotation
  change
    (MvPolynomial.rename cycleSixGeneratorPermutation
      (cyclicOrbitPolynomial a)).coeff m =
        (cyclicOrbitPolynomial a).coeff m
  calc
    (MvPolynomial.rename cycleSixGeneratorPermutation
        (cyclicOrbitPolynomial a)).coeff m =
        (MvPolynomial.rename cycleSixGeneratorPermutation
          (cyclicOrbitPolynomial a)).coeff
            (d.mapDomain cycleSixGeneratorPermutation) := by rw [hd]
    _ = (cyclicOrbitPolynomial a).coeff d :=
      MvPolynomial.coeff_rename_mapDomain
        cycleSixGeneratorPermutation
        cycleSixGeneratorPermutation.injective _ _
    _ = if Finsupp.equivFunOnFinite d ∈ cyclicOrbitSupport a
          then 1 else 0 := by
      simpa using coeff_cyclicOrbitPolynomial a
        (Finsupp.equivFunOnFinite d)
    _ = if u ∈ cyclicOrbitSupport a then 1 else 0 := by
      simp only [horbit]
    _ = (cyclicOrbitPolynomial a).coeff m := by
      symm
      simpa [u] using coeff_cyclicOrbitPolynomial a u

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants
