import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Lazard's general resolvent criterion on a finite coset orbit

This file isolates the honest group-action argument behind Theorem 1 of
Lazard's *Solving Quintics by Radicals*.  Let `G` be a subgroup of an ambient
permutation group `A`.  A specialized `G`-invariant has one value on every
left coset `A/G`, and the corresponding resolvent is the product of the
linear factors with those values as roots.

The two directions deliberately have different hypotheses.

* If the Galois image is contained in the stabilizer of the chosen base
  coset, its value is fixed by every Galois automorphism and hence belongs to
  the base field.  No injectivity or separability hypothesis is used.
* Conversely, a base-field root selects a coset.  Injectivity of the
  specialized coset values (equivalently, separability of this product of
  linear factors) forces that coset to be fixed, so the Galois image is
  contained in its conjugate stabilizer.

The module works with the full finite-dimensional Galois group and uses
`IsGalois.mem_range_algebraMap_iff_fixed`; fixed-field descent is therefore a
theorem, not a field-membership certificate supplied by the caller.  The
optional `baseResolvent` hypotheses at the end merely identify a concrete
polynomial over the base field with the orbit product after scalar extension.
They do not assume either conclusion of the criterion.
-/

open scoped Polynomial
open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardGeneralResolventCriterion

universe uF uL uA

/-- The left-coset type used by a resolvent for the subgroup `G ≤ A`. -/
abbrev Cosets {A : Type uA} [Group A] (G : Subgroup A) :=
  A ⧸ G

/-- The coset whose stabilizer is literally `G`. -/
def baseCoset {A : Type uA} [Group A] (G : Subgroup A) : Cosets G :=
  ((1 : A) : Cosets G)

/-- The stabilizer of the coset represented by `a`.

For the left action on `A/G`, Mathlib's convention identifies this with
`G` transported by `x ↦ a * x * a⁻¹`.
-/
def conjugateStabilizer {A : Type uA} [Group A]
    (G : Subgroup A) (a : A) : Subgroup A :=
  G.map (MulAut.conj a).toMonoidHom

section OrbitPolynomial

variable {A : Type uA} [Group A]
variable (G : Subgroup A) [Fintype (Cosets G)]
variable {R : Type uL} [CommRing R]

/-- The specialized orbit resolvent: it has one linear factor for every
coset in `A/G`.  Thus equal values are retained as repeated factors rather
than silently deduplicated. -/
noncomputable def orbitResolvent (value : Cosets G → R) : R[X] :=
  ∏ c : Cosets G, (X - C (value c))

variable {L : Type uL} [Field L]

/-- Root semantics of the specialized orbit resolvent.  This statement does
not require the coset values to be distinct. -/
theorem orbitResolvent_isRoot_iff (value : Cosets G → L) (x : L) :
    (orbitResolvent G value).IsRoot x ↔ ∃ c : Cosets G, value c = x := by
  classical
  simp only [Polynomial.IsRoot, orbitResolvent, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c, hc.symm⟩

/-- Every specialized coset value is a root of the orbit resolvent. -/
theorem orbitResolvent_isRoot_value (value : Cosets G → L) (c : Cosets G) :
    (orbitResolvent G value).IsRoot (value c) :=
  (orbitResolvent_isRoot_iff G value (value c)).2 ⟨c, rfl⟩

/-- For an orbit product of linear factors, separability is exactly
injectivity of the specialized coset values. -/
theorem orbitResolvent_separable_iff (value : Cosets G → L) :
    (orbitResolvent G value).Separable ↔ Function.Injective value := by
  classical
  rw [orbitResolvent, Polynomial.separable_prod_X_sub_C_iff]

end OrbitPolynomial

section GaloisCriterion

variable {F : Type uF} {L : Type uL} {A : Type uA}
variable [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]
variable [Group A]
variable (G : Subgroup A) [Fintype (Cosets G)]

/- An action homomorphism from the full Galois group into the ambient group
acting on the cosets. -/
variable (rootAction : (L ≃ₐ[F] L) →* A)

/- Specialized invariant values, equivariant for the Galois action and the
coset action induced by `rootAction`. -/
variable (value : Cosets G → L)
variable (value_equivariant :
  ∀ (σ : L ≃ₐ[F] L) (c : Cosets G),
    σ (value c) = value (rootAction σ • c))

include value_equivariant

omit [Fintype (Cosets G)] in
/-- A coset fixed by the whole Galois image has a value in the base field.
This is the fixed-field theorem for a finite-dimensional Galois extension,
not an extra rationality certificate. -/
theorem value_mem_range_algebraMap_of_fixedCoset
    (c : Cosets G)
    (hfixed : ∀ σ : L ≃ₐ[F] L, rootAction σ • c = c) :
    value c ∈ Set.range (algebraMap F L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  rw [value_equivariant σ c, hfixed σ]

/-- A fixed coset yields an actual base-field root of the specialized orbit
resolvent.  No separability or injectivity is assumed. -/
theorem orbitResolvent_has_baseField_root_of_fixedCoset
    (c : Cosets G)
    (hfixed : ∀ σ : L ≃ₐ[F] L, rootAction σ • c = c) :
    ∃ q : F, (orbitResolvent G value).IsRoot (algebraMap F L q) := by
  obtain ⟨q, hq⟩ := value_mem_range_algebraMap_of_fixedCoset
    G rootAction value value_equivariant c hfixed
  refine ⟨q, ?_⟩
  rw [hq]
  exact orbitResolvent_isRoot_value G value c

omit [FiniteDimensional F L] [IsGalois F L] [Fintype (Cosets G)]
  value_equivariant in
/-- Containment of the Galois image in `G` fixes the chosen base coset
`1G`.  This is the group-theoretic hypothesis in the forward half of
Lazard's theorem. -/
theorem baseCoset_fixed_of_range_le
    (hle : rootAction.range ≤ G) (σ : L ≃ₐ[F] L) :
    rootAction σ • baseCoset G = baseCoset G := by
  apply MulAction.mem_stabilizer_iff.mp
  rw [show baseCoset G = ((1 : A) : Cosets G) by rfl,
    MulAction.stabilizer_quotient]
  exact hle ⟨σ, rfl⟩

/-- **Forward half of Lazard Theorem 1, at the chosen base coset.**

If the Galois image is contained in `G`, the specialized orbit resolvent has
a root coming from `F`.  In particular, this direction does not use
separability of the specialized resolvent.
-/
theorem orbitResolvent_has_baseField_root_of_le_baseStabilizer
    (hle : rootAction.range ≤ G) :
    ∃ q : F, (orbitResolvent G value).IsRoot (algebraMap F L q) := by
  apply orbitResolvent_has_baseField_root_of_fixedCoset
    G rootAction value value_equivariant (baseCoset G)
  exact fun σ ↦ baseCoset_fixed_of_range_le G rootAction hle σ

omit [FiniteDimensional F L] [IsGalois F L] [Fintype (Cosets G)]
  value_equivariant in
/-- Containment in the conjugate stabilizer represented by `a` fixes the
corresponding coset `aG`. -/
theorem representedCoset_fixed_of_range_le_conjugateStabilizer
    (a : A) (hle : rootAction.range ≤ conjugateStabilizer G a)
    (σ : L ≃ₐ[F] L) :
    rootAction σ • (a • baseCoset G) = a • baseCoset G := by
  have hbase : MulAction.stabilizer A (baseCoset G) = G := by
    simpa only [baseCoset] using MulAction.stabilizer_quotient G
  have hmem :
      rootAction σ ∈ MulAction.stabilizer A (a • baseCoset G) := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, hbase]
    exact hle (show rootAction σ ∈ rootAction.range from ⟨σ, rfl⟩)
  exact MulAction.mem_stabilizer_iff.mp hmem

/-- Conjugate containment gives a base-field resolvent root as well; the
root is the value at the represented coset.  Again, no separability is used.
-/
theorem orbitResolvent_has_baseField_root_of_le_conjugateStabilizer
    (a : A) (hle : rootAction.range ≤ conjugateStabilizer G a) :
    ∃ q : F, (orbitResolvent G value).IsRoot (algebraMap F L q) := by
  apply orbitResolvent_has_baseField_root_of_fixedCoset
    G rootAction value value_equivariant (a • baseCoset G)
  exact fun σ ↦ representedCoset_fixed_of_range_le_conjugateStabilizer
    G rootAction a hle σ

omit [FiniteDimensional F L] [IsGalois F L] in
/-- With distinct specialized values, an arbitrary base-field root of the
orbit resolvent selects a coset fixed by the entire Galois image. -/
theorem exists_fixedCoset_of_baseField_root_of_injective
    (hinjective : Function.Injective value)
    (q : F)
    (hq : (orbitResolvent G value).IsRoot (algebraMap F L q)) :
    ∃ c : Cosets G, ∀ σ : L ≃ₐ[F] L, rootAction σ • c = c := by
  obtain ⟨c, hc⟩ := (orbitResolvent_isRoot_iff G value _).1 hq
  refine ⟨c, fun σ ↦ hinjective ?_⟩
  calc
    value (rootAction σ • c) = σ (value c) :=
      (value_equivariant σ c).symm
    _ = σ (algebraMap F L q) := congrArg (σ : L → L) hc
    _ = algebraMap F L q := by simp
    _ = value c := hc.symm

omit [FiniteDimensional F L] [IsGalois F L] [Fintype (Cosets G)]
  value_equivariant in
/-- A coset fixed by the Galois image identifies a conjugate of `G` that
contains that image. -/
theorem exists_le_conjugateStabilizer_of_fixedCoset
    (c : Cosets G)
    (hfixed : ∀ σ : L ≃ₐ[F] L, rootAction σ • c = c) :
    ∃ a : A, rootAction.range ≤ conjugateStabilizer G a := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨a, ?_⟩
  rintro g ⟨σ, rfl⟩
  have hfixed' :
      rootAction σ • (a • ((1 : A) : Cosets G)) =
        a • ((1 : A) : Cosets G) := by
    simpa using hfixed σ
  have hmem := MulAction.mem_stabilizer_iff.mpr hfixed'
  simpa only [conjugateStabilizer,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_quotient] using hmem

omit [FiniteDimensional F L] [IsGalois F L] in
/-- **Converse half of Lazard Theorem 1, injective form.**

If the specialized orbit values are distinct, every root of the orbit
resolvent that lies in the base field forces the Galois image into a conjugate
of `G`.
-/
theorem exists_le_conjugateStabilizer_of_baseField_root_of_injective
    (hinjective : Function.Injective value)
    (q : F)
    (hq : (orbitResolvent G value).IsRoot (algebraMap F L q)) :
    ∃ a : A, rootAction.range ≤ conjugateStabilizer G a := by
  obtain ⟨c, hfixed⟩ := exists_fixedCoset_of_baseField_root_of_injective
    G rootAction value value_equivariant hinjective q hq
  exact exists_le_conjugateStabilizer_of_fixedCoset
    G rootAction c hfixed

omit [FiniteDimensional F L] [IsGalois F L] in
/-- **Converse half of Lazard Theorem 1, separable form.**

For this explicit product of linear factors, separability supplies precisely
the injectivity needed by the preceding theorem.
-/
theorem exists_le_conjugateStabilizer_of_baseField_root_of_separable
    (hseparable : (orbitResolvent G value).Separable)
    (q : F)
    (hq : (orbitResolvent G value).IsRoot (algebraMap F L q)) :
    ∃ a : A, rootAction.range ≤ conjugateStabilizer G a := by
  exact exists_le_conjugateStabilizer_of_baseField_root_of_injective
    G rootAction value value_equivariant
      ((orbitResolvent_separable_iff G value).1 hseparable) q hq

/-- The abstract criterion as an equivalence once the specialized orbit is
injective.  The reverse implication invokes the no-separability forward
theorem, not the injectivity hypothesis. -/
theorem orbitResolvent_has_baseField_root_iff_exists_le_conjugateStabilizer
    (hinjective : Function.Injective value) :
    (∃ q : F,
      (orbitResolvent G value).IsRoot (algebraMap F L q)) ↔
      ∃ a : A, rootAction.range ≤ conjugateStabilizer G a := by
  constructor
  · rintro ⟨q, hq⟩
    exact exists_le_conjugateStabilizer_of_baseField_root_of_injective
      G rootAction value value_equivariant hinjective q hq
  · rintro ⟨a, hle⟩
    exact orbitResolvent_has_baseField_root_of_le_conjugateStabilizer
      G rootAction value value_equivariant a hle

section ConcreteBasePolynomial

variable (baseResolvent : F[X])
variable (baseResolvent_map :
  baseResolvent.map (algebraMap F L) = orbitResolvent G value)

include baseResolvent_map

omit [FiniteDimensional F L] [IsGalois F L] value_equivariant in
/-- Transfer a root of the orbit product back to a concrete resolvent over
the base field whose scalar extension is that product. -/
theorem baseResolvent_isRoot_of_orbitResolvent_isRoot
    (q : F)
    (hq : (orbitResolvent G value).IsRoot (algebraMap F L q)) :
    baseResolvent.IsRoot q := by
  have hq' :
      (baseResolvent.map (algebraMap F L)).IsRoot
        (algebraMap F L q) := by
    rwa [baseResolvent_map]
  exact hq'.of_map (algebraMap F L).injective

/-- Polynomial-root version of the forward theorem for a concrete resolvent
defined over `F`.  Separability is intentionally absent. -/
theorem baseResolvent_hasRoot_of_le_baseStabilizer
    (hle : rootAction.range ≤ G) :
    ∃ q : F, baseResolvent.IsRoot q := by
  obtain ⟨q, hq⟩ := orbitResolvent_has_baseField_root_of_le_baseStabilizer
    G rootAction value value_equivariant hle
  exact ⟨q, baseResolvent_isRoot_of_orbitResolvent_isRoot
    G value baseResolvent baseResolvent_map q hq⟩

omit [FiniteDimensional F L] [IsGalois F L] in
/-- Polynomial-root version of the injective converse for a concrete
base-field resolvent. -/
theorem exists_le_conjugateStabilizer_of_baseResolvent_root_of_injective
    (hinjective : Function.Injective value)
    (q : F) (hq : baseResolvent.IsRoot q) :
    ∃ a : A, rootAction.range ≤ conjugateStabilizer G a := by
  have hqL := Polynomial.IsRoot.map (f := algebraMap F L) hq
  rw [baseResolvent_map] at hqL
  exact exists_le_conjugateStabilizer_of_baseField_root_of_injective
    G rootAction value value_equivariant hinjective q hqL

omit [FiniteDimensional F L] [IsGalois F L] in
/-- Polynomial-root version of the separable converse for a concrete
base-field resolvent. -/
theorem exists_le_conjugateStabilizer_of_baseResolvent_root_of_separable
    (hseparable : (orbitResolvent G value).Separable)
    (q : F) (hq : baseResolvent.IsRoot q) :
    ∃ a : A, rootAction.range ≤ conjugateStabilizer G a := by
  exact exists_le_conjugateStabilizer_of_baseResolvent_root_of_injective
    G rootAction value value_equivariant baseResolvent baseResolvent_map
      ((orbitResolvent_separable_iff G value).1 hseparable) q hq

omit [FiniteDimensional F L] [IsGalois F L] value_equivariant in
/-- Separability of the concrete base-field resolvent transfers to its
explicit orbit factorization after scalar extension.  This is the form of
the hypothesis used in Lazard's statement. -/
theorem orbitResolvent_separable_of_baseResolvent_separable
    (hseparable : baseResolvent.Separable) :
    (orbitResolvent G value).Separable := by
  have hmap :
      (baseResolvent.map (algebraMap F L)).Separable :=
    hseparable.map (f := algebraMap F L)
  rwa [baseResolvent_map] at hmap

omit [FiniteDimensional F L] [IsGalois F L] in
/-- Concrete-base-polynomial converse with separability stated directly for
the resolvent over `F`, as in Lazard's Theorem 1. -/
theorem exists_le_conjugateStabilizer_of_baseResolvent_root_of_baseSeparable
    (hseparable : baseResolvent.Separable)
    (q : F) (hq : baseResolvent.IsRoot q) :
    ∃ a : A, rootAction.range ≤ conjugateStabilizer G a := by
  exact exists_le_conjugateStabilizer_of_baseResolvent_root_of_separable
    G rootAction value value_equivariant baseResolvent baseResolvent_map
      (orbitResolvent_separable_of_baseResolvent_separable
        G value baseResolvent baseResolvent_map hseparable) q hq

/-- The concrete resolvent criterion with Lazard's separability premise on
the base-field polynomial.  For an arbitrary ordering of the roots, the
honest converse conclusion is containment in some conjugate of `G`. -/
theorem baseResolvent_hasRoot_iff_exists_le_conjugateStabilizer
    (hseparable : baseResolvent.Separable) :
    (∃ q : F, baseResolvent.IsRoot q) ↔
      ∃ a : A, rootAction.range ≤ conjugateStabilizer G a := by
  constructor
  · rintro ⟨q, hq⟩
    exact
      exists_le_conjugateStabilizer_of_baseResolvent_root_of_baseSeparable
        G rootAction value value_equivariant baseResolvent
          baseResolvent_map hseparable q hq
  · rintro ⟨a, hle⟩
    obtain ⟨q, hq⟩ :=
      orbitResolvent_has_baseField_root_of_le_conjugateStabilizer
        G rootAction value value_equivariant a hle
    exact ⟨q, baseResolvent_isRoot_of_orbitResolvent_isRoot
      G value baseResolvent baseResolvent_map q hq⟩

end ConcreteBasePolynomial

end GaloisCriterion

end LeanProofs.PolynomialFormulas.LazardGeneralResolventCriterion
