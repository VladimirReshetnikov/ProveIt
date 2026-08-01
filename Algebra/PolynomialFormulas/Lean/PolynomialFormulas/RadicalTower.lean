import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Cyclic Galois layers lie in the radical closure

This module supplies the positive Kummer-theoretic direction that is absent
from `Mathlib.FieldTheory.AbelRuffini`: a finite cyclic Galois extension inside
`ℂ` is contained in `solvableByRad ℚ ℂ` whenever its base field is.

The first theorem handles the usual Kummer hypothesis that the base contains
the required primitive roots of unity.  The second removes that hypothesis by
adjoining a sufficiently large root of unity.  That adjunction is itself a
radical adjunction, and base change embeds the resulting cyclic Galois group
in the original one.
-/

open Polynomial IntermediateField

namespace LeanProofs.PolynomialFormulas

/-- Kummer step for a cyclic Galois layer whose base contains the necessary
primitive roots of unity. -/
theorem cyclic_extension_le_solvableByRad
    {K L : IntermediateField ℚ ℂ} (hKL : K ≤ L)
    (hK : K ≤ solvableByRad ℚ ℂ)
    [FiniteDimensional K (IntermediateField.extendScalars hKL)]
    [IsGalois K (IntermediateField.extendScalars hKL)]
    [IsCyclic Gal((IntermediateField.extendScalars hKL)/K)]
    (hroots :
      (primitiveRoots
        (Module.finrank K (IntermediateField.extendScalars hKL)) K).Nonempty) :
    L ≤ solvableByRad ℚ ℂ := by
  let E : IntermediateField K ℂ := IntermediateField.extendScalars hKL
  obtain ⟨α, hαpow, hαtop⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic K E hroots
  obtain ⟨a, ha⟩ := hαpow
  have hαpow' : (α : ℂ) ^ Module.finrank K E ∈ solvableByRad ℚ ℂ := by
    change ((α ^ Module.finrank K E : E) : ℂ) ∈ solvableByRad ℚ ℂ
    rw [← ha]
    exact hK a.property
  have hα : (α : ℂ) ∈ solvableByRad ℚ ℂ :=
    solvableByRad.rad_mem (Module.finrank_pos.ne') hαpow'
  intro x hx
  let y : E := ⟨x, hx⟩
  have hy : y ∈ adjoin K ({α} : Set E) := by
    rw [hαtop]
    exact trivial
  exact IntermediateField.adjoin_induction K (E := E) (s := ({α} : Set E))
    (p := fun z _ => (z : ℂ) ∈ solvableByRad ℚ ℂ)
    (by
      rintro z rfl
      exact hα)
    (fun z => hK z.property)
    (fun _ _ _ _ hz hw => add_mem hz hw)
    (fun _ _ hz => inv_mem hz)
    (fun _ _ _ _ hz hw => mul_mem hz hw)
    hy

set_option maxHeartbeats 800000 in
/-- A finite cyclic Galois extension inside `ℂ` is contained in the radical
closure as soon as its base field is. Primitive roots of unity are first
adjoined inside the radical closure, so no roots-of-unity hypothesis is
needed on the original base field. -/
theorem cyclic_galois_extension_le_solvableByRad
    {K L : IntermediateField ℚ ℂ} (hKL : K ≤ L)
    (hK : K ≤ solvableByRad ℚ ℂ)
    [FiniteDimensional K (IntermediateField.extendScalars hKL)]
    [IsGalois K (IntermediateField.extendScalars hKL)]
    [IsCyclic Gal((IntermediateField.extendScalars hKL)/K)] :
    L ≤ solvableByRad ℚ ℂ := by
  let A : IntermediateField K ℂ := IntermediateField.extendScalars hKL
  let N := Module.finrank K A
  let m := N.factorial
  have hmpos : 0 < m := Nat.factorial_pos N
  letI : NeZero (m : ℂ) := ⟨by exact_mod_cast hmpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ m
  have hζrad : ζ ∈ solvableByRad ℚ ℂ := by
    apply solvableByRad.rad_mem hmpos.ne'
    rw [hζ.pow_eq_one]
    exact one_mem _
  let Z : IntermediateField K ℂ := K⟮ζ⟯
  have hZrad (z : Z) : (z : ℂ) ∈ solvableByRad ℚ ℂ := by
    exact IntermediateField.adjoin_induction K (E := ℂ) (s := ({ζ} : Set ℂ))
      (p := fun z _ => z ∈ solvableByRad ℚ ℂ)
      (by
        rintro z rfl
        exact hζrad)
      (fun z => hK z.property)
      (fun _ _ _ _ hz hw => add_mem hz hw)
      (fun _ _ hz => inv_mem hz)
      (fun _ _ _ _ hz hw => mul_mem hz hw)
      z.property
  have hζint : IsIntegral K ζ :=
    (hζ.isIntegral hmpos).tower_top
  letI : FiniteDimensional K Z :=
    IntermediateField.adjoin.finiteDimensional hζint
  let M : IntermediateField K ℂ := A ⊔ Z
  letI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_sup A Z
  let A' : IntermediateField K M := A.restrict le_sup_left
  let Z' : IntermediateField K M := Z.restrict le_sup_right
  have hsup : A' ⊔ Z' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top,
      IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict]
  letI : FiniteDimensional K A' :=
    IntermediateField.finiteDimensional_left A'
  letI : IsGalois K A' :=
    IsGalois.of_algEquiv (IntermediateField.restrict_algEquiv le_sup_left)
  letI : IsCyclic Gal(A'/K) :=
    isCyclic_of_injective
      (AlgEquiv.autCongr
        (IntermediateField.restrict_algEquiv (show A ≤ M from le_sup_left))).symm.toMonoidHom
      (AlgEquiv.autCongr
        (IntermediateField.restrict_algEquiv (show A ≤ M from le_sup_left))).symm.injective
  letI : FiniteDimensional Z' M :=
    IntermediateField.finiteDimensional_right Z'
  letI : IsGalois Z' M := IsGalois.sup_right A' Z' hsup
  let ρ : Gal(M/Z') →* Gal(A'/K) :=
    IntermediateField.restrictRestrictAlgEquivMapHom K A' Z' M
  have hρinj : Function.Injective ρ :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective A' Z' hsup
  letI : IsCyclic Gal(M/Z') := isCyclic_of_injective ρ hρinj
  let d := Module.finrank Z' M
  have hdpos : 0 < d := Module.finrank_pos
  have hdle' : d ≤ Module.finrank K A' := by
    change Module.finrank Z' M ≤ Module.finrank K A'
    rw [← IsGalois.card_aut_eq_finrank Z' M,
      ← IsGalois.card_aut_eq_finrank K A']
    exact Nat.card_le_card_of_injective ρ hρinj
  have hAA' : Module.finrank K A = Module.finrank K A' :=
    (IntermediateField.restrict_algEquiv
      (show A ≤ M from le_sup_left)).toLinearEquiv.finrank_eq
  have hdle : d ≤ N := hdle'.trans_eq hAA'.symm
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hdpos hdle
  have hηC : IsPrimitiveRoot (ζ ^ k) d :=
    hζ.pow hmpos (by
      change N.factorial = k * d
      rw [hk, Nat.mul_comm])
  let ηM : M :=
    ⟨ζ ^ k, (show Z ≤ M from le_sup_right)
      (pow_mem (IntermediateField.mem_adjoin_simple_self K ζ) k)⟩
  let η : Z' :=
    ⟨ηM, (IntermediateField.mem_restrict le_sup_right ηM).2
      (pow_mem (IntermediateField.mem_adjoin_simple_self K ζ) k)⟩
  have hη : IsPrimitiveRoot η d := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff,
      ← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hηC
  have hroots : (primitiveRoots d Z').Nonempty :=
    ⟨η, (mem_primitiveRoots hdpos).2 hη⟩
  have hZ'rad (z : Z') : ((z : M) : ℂ) ∈ solvableByRad ℚ ℂ := by
    let z' : Z :=
      ⟨((z : M) : ℂ),
        (IntermediateField.mem_restrict le_sup_right (z : M)).1 z.property⟩
    exact hZrad z'
  obtain ⟨α, hαpow, hαtop⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic Z' M hroots
  obtain ⟨a, ha⟩ := hαpow
  have hαpow' : (α : ℂ) ^ d ∈ solvableByRad ℚ ℂ := by
    change ((α ^ d : M) : ℂ) ∈ solvableByRad ℚ ℂ
    rw [← ha]
    exact hZ'rad a
  have hαrad : (α : ℂ) ∈ solvableByRad ℚ ℂ :=
    solvableByRad.rad_mem hdpos.ne' hαpow'
  have hMrad (x : M) : (x : ℂ) ∈ solvableByRad ℚ ℂ := by
    have hx : x ∈ adjoin Z' ({α} : Set M) := by
      rw [hαtop]
      exact trivial
    exact IntermediateField.adjoin_induction Z' (E := M) (s := ({α} : Set M))
      (p := fun x _ => (x : ℂ) ∈ solvableByRad ℚ ℂ)
      (by
        rintro x rfl
        exact hαrad)
      (fun z => hZ'rad z)
      (fun _ _ _ _ hx hy => add_mem hx hy)
      (fun _ _ hx => inv_mem hx)
      (fun _ _ _ _ hx hy => mul_mem hx hy)
      hx
  intro x hx
  let xM : M := ⟨x, (show A ≤ M from le_sup_left) hx⟩
  exact hMrad xM

end LeanProofs.PolynomialFormulas
