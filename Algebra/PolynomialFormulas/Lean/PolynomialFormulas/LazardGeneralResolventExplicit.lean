import PolynomialFormulas.LazardGeneralResolventCriterion
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# The explicit invariant-polynomial adapter for Lazard's general resolvent

`LazardGeneralResolventCriterion` isolates the group-theoretic argument in
Lazard's Theorem 1.  Its most general interface accepts an equivariant map on
cosets and a factorization of a polynomial over the coefficient field.  This
file constructs both pieces from closely related explicit data:

* an actual multivariate polynomial `invariant` over the base field;
* its invariance under the subgroup `G`;
* an ordered root tuple on which the Galois group acts through `rootAction`.

The value on `aG` is, by definition, the evaluation at the ordered roots of
the polynomial obtained by renaming the variables by `a`.  Subgroup
invariance proves that this is well defined on cosets.  Evaluation of a
base-coefficient polynomial commutes with every Galois automorphism, so orbit
equivariance is a theorem.  The universal product specializes definitionally
to the product over those values.  Finally that product is Galois fixed, and
the fixed-field theorem descends every coefficient to the base field.  Thus
the concrete base resolvent and its specialized factorization are constructed
here, rather than supplied as certificates.

Separability occurs only in the converse, exactly where distinct specialized
orbit values are needed.

There is one deliberate distinction from the terminology of the paper.  A
merely `G`-invariant polynomial may have formal stabilizer larger than `G`.
The predicate `HasExactRenameStabilizer` below records the stronger
group-theoretic exact-stabilizer condition, and under that condition the
universal values are proved injective on `A/G`.  This is the stabilizer part
of the paper's notion of a resolvent invariant, not yet the full
minimal-polynomial assertion.  The orbit-product criterion remains valid
under the weaker `InvariantUnder` hypothesis.  Identifying the resulting
orbit product with a minimal polynomial over the invariant rational-function
field still requires the fraction-field action/fixed-field bridge described
in the crosswalk.
-/

open scoped Polynomial
open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardGeneralResolventExplicit

universe uF uL uA uI

section FormalInvariantOrbit

variable {F : Type uF} [CommRing F]
variable {A : Type uA} [Group A]
variable {ι : Type uI} [MulAction A ι]

/-- The honest left action on a polynomial in labelled variables.  The
orientation agrees with left multiplication on `A/G`. -/
noncomputable def renameAction (a : A) (p : MvPolynomial ι F) : MvPolynomial ι F :=
  MvPolynomial.rename (fun i => a • i) p

@[simp] theorem renameAction_one (p : MvPolynomial ι F) :
    renameAction (1 : A) p = p := by
  unfold renameAction
  simp only [one_smul]
  change MvPolynomial.rename id p = p
  exact MvPolynomial.rename_id_apply p

theorem renameAction_mul (a b : A) (p : MvPolynomial ι F) :
    renameAction (a * b) p = renameAction a (renameAction b p) := by
  simp [renameAction, MvPolynomial.rename_rename, Function.comp_def, mul_smul]

/-- Polynomial invariance under the subgroup occurring in the resolvent. -/
def InvariantUnder (G : Subgroup A) (p : MvPolynomial ι F) : Prop :=
  ∀ g : A, g ∈ G → renameAction g p = p

/-- The subgroup of elements which fix a polynomial under variable renaming.
This is the formal stabilizer relevant to Lazard's definition of a resolvent
invariant. -/
def renameStabilizer (p : MvPolynomial ι F) : Subgroup A where
  carrier := {a | renameAction a p = p}
  one_mem' := renameAction_one p
  mul_mem' := by
    intro a b ha hb
    change renameAction (a * b) p = p
    rw [renameAction_mul, hb, ha]
  inv_mem' := by
    intro a ha
    calc
      renameAction a⁻¹ p = renameAction a⁻¹ (renameAction a p) := by rw [ha]
      _ = renameAction (a⁻¹ * a) p := (renameAction_mul a⁻¹ a p).symm
      _ = p := by simp

@[simp] theorem mem_renameStabilizer (p : MvPolynomial ι F) (a : A) :
    a ∈ renameStabilizer p ↔ renameAction a p = p :=
  Iff.rfl

/-- The exact renaming-stabilizer condition expected of Lazard's resolvent
invariant.  This is deliberately named as a stabilizer condition: by itself
it does not yet identify the orbit product with a minimal polynomial over the
invariant rational-function field. -/
def HasExactRenameStabilizer (G : Subgroup A)
    (p : MvPolynomial ι F) : Prop :=
  renameStabilizer p = G

namespace HasExactRenameStabilizer

/-- Exact stabilizer implies the weaker invariance used by the general orbit
criterion. -/
theorem invariantUnder {G : Subgroup A} {p : MvPolynomial ι F}
    (h : HasExactRenameStabilizer G p) : InvariantUnder G p := by
  intro g hg
  apply (mem_renameStabilizer p g).mp
  rw [h]
  exact hg

/-- Pointwise form of the exact renaming-stabilizer condition. -/
theorem rename_eq_iff_mem {G : Subgroup A} {p : MvPolynomial ι F}
    (h : HasExactRenameStabilizer G p) (a : A) :
    renameAction a p = p ↔ a ∈ G := by
  rw [← mem_renameStabilizer, h]

end HasExactRenameStabilizer

/-- The formal conjugate indexed by a coset.  The quotient lift is justified
from the definition of subgroup invariance, not by a supplied orbit map. -/
noncomputable def universalOrbitValue
    (G : Subgroup A) (p : MvPolynomial ι F) (hp : InvariantUnder G p)
    (c : LazardGeneralResolventCriterion.Cosets G) : MvPolynomial ι F :=
  Quotient.liftOn' c (fun a => renameAction a p) (by
    intro a b hab
    have habG : a⁻¹ * b ∈ G := QuotientGroup.leftRel_apply.mp hab
    calc
      renameAction a p = renameAction a (renameAction (a⁻¹ * b) p) := by
        rw [hp (a⁻¹ * b) habG]
      _ = renameAction (a * (a⁻¹ * b)) p :=
        (renameAction_mul a (a⁻¹ * b) p).symm
      _ = renameAction b p := by simp)

@[simp] theorem universalOrbitValue_mk
    (G : Subgroup A) (p : MvPolynomial ι F) (hp : InvariantUnder G p)
    (a : A) :
    universalOrbitValue G p hp (a : LazardGeneralResolventCriterion.Cosets G) =
      renameAction a p :=
  rfl

/-- Left multiplication of cosets is exactly variable renaming of the formal
orbit value. -/
theorem universalOrbitValue_smul
    (G : Subgroup A) (p : MvPolynomial ι F) (hp : InvariantUnder G p)
    (a : A) (c : LazardGeneralResolventCriterion.Cosets G) :
    universalOrbitValue G p hp (a • c) =
      renameAction a (universalOrbitValue G p hp c) := by
  induction c using QuotientGroup.induction_on with
  | _ b =>
      exact renameAction_mul a b p

/-- Under Lazard's exact-stabilizer hypothesis, distinct left cosets give
distinct formal conjugates.  This is a statement about the universal
polynomials; a later specialization may still make two values collide. -/
theorem universalOrbitValue_injective
    (G : Subgroup A) (p : MvPolynomial ι F)
    (hp : HasExactRenameStabilizer G p) :
    Function.Injective (universalOrbitValue G p hp.invariantUnder) := by
  intro c d
  induction c using QuotientGroup.induction_on with
  | _ a =>
      induction d using QuotientGroup.induction_on with
      | _ b =>
          intro hab
          have hab' : renameAction a p = renameAction b p := by
            simpa only [universalOrbitValue_mk] using hab
          have hfix : renameAction (a⁻¹ * b) p = p := by
            calc
              renameAction (a⁻¹ * b) p =
                  renameAction a⁻¹ (renameAction b p) :=
                renameAction_mul a⁻¹ b p
              _ = renameAction a⁻¹ (renameAction a p) := by rw [← hab']
              _ = renameAction (a⁻¹ * a) p :=
                (renameAction_mul a⁻¹ a p).symm
              _ = p := by simp
          exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr
            ((hp.rename_eq_iff_mem (a⁻¹ * b)).mp hfix))

/-- The universal orbit polynomial attached to the explicit invariant.

When the invariant has stabilizer exactly `G` this is the usual full orbit
polynomial.  No minimal-polynomial or fixed-field-generation claim is made by
this definition alone. -/
noncomputable def universalInvariantResolvent
    (G : Subgroup A) [Fintype (LazardGeneralResolventCriterion.Cosets G)]
    (p : MvPolynomial ι F) (hp : InvariantUnder G p) :
    Polynomial (MvPolynomial ι F) :=
  LazardGeneralResolventCriterion.orbitResolvent G (universalOrbitValue G p hp)

end FormalInvariantOrbit

section Specialization

variable {F : Type uF} {L : Type uL} {A : Type uA} {ι : Type uI}
variable [Field F] [Field L] [Algebra F L]
variable [Group A] [MulAction A ι]
variable (G : Subgroup A) [Fintype (LazardGeneralResolventCriterion.Cosets G)]
variable (p : MvPolynomial ι F) (hp : InvariantUnder G p)
variable (roots : ι → L)

/-- Evaluation of the formal coset conjugate at the ordered roots. -/
noncomputable def specializedOrbitValue (c : LazardGeneralResolventCriterion.Cosets G) : L :=
  MvPolynomial.eval₂Hom (algebraMap F L) roots
    (universalOrbitValue G p hp c)

/-- The universal resolvent specializes to the product over the explicitly
evaluated coset conjugates.  This is the factorization hypothesis of the
abstract criterion, now proved directly from the definitions. -/
theorem universalInvariantResolvent_specializes :
    (universalInvariantResolvent G p hp).map
        (MvPolynomial.eval₂Hom (algebraMap F L) roots) =
      LazardGeneralResolventCriterion.orbitResolvent G (specializedOrbitValue G p hp roots) := by
  classical
  simp [universalInvariantResolvent, LazardGeneralResolventCriterion.orbitResolvent,
    specializedOrbitValue, Polynomial.map_prod]

end Specialization

section GaloisSpecialization

variable {F : Type uF} {L : Type uL} {A : Type uA} {ι : Type uI}
variable [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]
variable [Group A] [MulAction A ι]
variable (G : Subgroup A) [Fintype (LazardGeneralResolventCriterion.Cosets G)]
variable (p : MvPolynomial ι F) (hp : InvariantUnder G p)
variable (roots : ι → L)
variable (rootAction : (L ≃ₐ[F] L) →* A)
variable (roots_equivariant :
  ∀ (σ : L ≃ₐ[F] L) (i : ι),
    σ (roots i) = roots (rootAction σ • i))

include roots_equivariant

omit [FiniteDimensional F L] [IsGalois F L] roots_equivariant in
/-- Evaluation of a polynomial with base-field coefficients commutes with a
Galois automorphism. -/
theorem map_specialization
    (σ : L ≃ₐ[F] L) (q : MvPolynomial ι F) :
    σ (MvPolynomial.eval₂Hom (algebraMap F L) roots q) =
      MvPolynomial.eval₂Hom (algebraMap F L)
        (fun i => σ (roots i)) q := by
  change σ.toRingEquiv.toRingHom
      (MvPolynomial.eval₂Hom (algebraMap F L) roots q) = _
  rw [MvPolynomial.map_eval₂Hom
    (algebraMap F L) roots σ.toRingEquiv.toRingHom q]
  apply MvPolynomial.eval₂Hom_congr
  · ext x
    exact σ.commutes x
  · rfl
  · rfl

omit [FiniteDimensional F L] [IsGalois F L]
  [Fintype (LazardGeneralResolventCriterion.Cosets G)] in
/-- Equivariance of the specialized orbit values follows from polynomial
evaluation and the action on the ordered roots. -/
theorem specializedOrbitValue_equivariant
    (σ : L ≃ₐ[F] L) (c : LazardGeneralResolventCriterion.Cosets G) :
    σ (specializedOrbitValue G p hp roots c) =
      specializedOrbitValue G p hp roots (rootAction σ • c) := by
  induction c using QuotientGroup.induction_on with
  | _ a =>
      rw [specializedOrbitValue, universalOrbitValue_mk,
        map_specialization roots σ]
      rw [show rootAction σ • ((a : A) : LazardGeneralResolventCriterion.Cosets G) =
          ((rootAction σ * a : A) : LazardGeneralResolventCriterion.Cosets G) by rfl,
        specializedOrbitValue, universalOrbitValue_mk]
      rw [renameAction, renameAction, MvPolynomial.eval₂Hom_rename,
        MvPolynomial.eval₂Hom_rename]
      apply MvPolynomial.eval₂Hom_congr
      · rfl
      · funext i
        simp only [Function.comp_apply, mul_smul]
        exact roots_equivariant σ (a • i)
      · rfl

omit [FiniteDimensional F L] [IsGalois F L] in
/-- The specialized orbit product is fixed coefficientwise by the whole
Galois group. -/
theorem specializedOrbitResolvent_map_galois
    (σ : L ≃ₐ[F] L) :
    (LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G p hp roots)).map σ.toRingHom =
      LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G p hp roots) := by
  classical
  have hequiv (c : LazardGeneralResolventCriterion.Cosets G) :
      σ.toRingEquiv.toRingHom (specializedOrbitValue G p hp roots c) =
        specializedOrbitValue G p hp roots (rootAction σ • c) := by
    exact specializedOrbitValue_equivariant
      G p hp roots rootAction roots_equivariant σ c
  simp only [LazardGeneralResolventCriterion.orbitResolvent, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    hequiv]
  exact (Equiv.prod_comp (MulAction.toPerm (rootAction σ))
    (fun c : LazardGeneralResolventCriterion.Cosets G =>
      Polynomial.X - Polynomial.C (specializedOrbitValue G p hp roots c)))

/-- Every coefficient of the explicit specialized orbit product descends to
the base field. -/
theorem specializedOrbitResolvent_coeff_mem_range (n : ℕ) :
    (LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G p hp roots)).coeff n ∈
      Set.range (algebraMap F L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  change σ.toRingEquiv.toRingHom
      ((LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G p hp roots)).coeff n) = _
  have h := congrArg (fun q : Polynomial L => q.coeff n)
    (specializedOrbitResolvent_map_galois G p hp roots rootAction
      roots_equivariant σ)
  simpa only [Polynomial.coeff_map] using h

/-- The specialized product lifts to a polynomial over the base field. -/
theorem specializedOrbitResolvent_mem_lifts :
    LazardGeneralResolventCriterion.orbitResolvent G (specializedOrbitValue G p hp roots) ∈
      Polynomial.lifts (algebraMap F L) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  exact specializedOrbitResolvent_coeff_mem_range
    G p hp roots rootAction roots_equivariant

/-- A canonical (classically selected) base-field resolvent.  Its existence,
including every coefficient, is derived from the explicit orbit product. -/
noncomputable def baseInvariantResolvent : Polynomial F :=
  Classical.choose ((Polynomial.mem_lifts
      (f := algebraMap F L)
      (LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G p hp roots))).1
    (specializedOrbitResolvent_mem_lifts
      G p hp roots rootAction roots_equivariant))

/-- The constructed base resolvent specializes to the explicit orbit
product.  This discharges the second supplied hypothesis of the abstract
criterion. -/
theorem baseInvariantResolvent_map :
    (baseInvariantResolvent G p hp roots rootAction roots_equivariant).map
        (algebraMap F L) =
      LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G p hp roots) :=
  Classical.choose_spec ((Polynomial.mem_lifts
      (f := algebraMap F L)
      (LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G p hp roots))).1
    (specializedOrbitResolvent_mem_lifts
      G p hp roots rootAction roots_equivariant))

/-- The forward half of Lazard's Theorem 1 for an explicit invariant
polynomial.  Neither equivariance, factorization, nor separability is an
input. -/
theorem baseInvariantResolvent_hasRoot_of_le_baseStabilizer
    (hle : rootAction.range ≤ G) :
    ∃ q : F,
      (baseInvariantResolvent G p hp roots rootAction roots_equivariant).IsRoot q := by
  exact LazardGeneralResolventCriterion.baseResolvent_hasRoot_of_le_baseStabilizer
    G rootAction (specializedOrbitValue G p hp roots)
    (specializedOrbitValue_equivariant
      G p hp roots rootAction roots_equivariant)
    (baseInvariantResolvent G p hp roots rootAction roots_equivariant)
    (baseInvariantResolvent_map
      G p hp roots rootAction roots_equivariant) hle

/-- The complete explicit invariant-resolvent criterion.  Separability is
retained only for Lazard's converse, where it rules out collisions among
specialized conjugates. -/
theorem baseInvariantResolvent_hasRoot_iff_image_le_conjugate
    (hseparable :
      (LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G p hp roots)).Separable) :
    (∃ q : F,
      (baseInvariantResolvent G p hp roots rootAction roots_equivariant).IsRoot q) ↔
      ∃ a : A, rootAction.range ≤ LazardGeneralResolventCriterion.conjugateStabilizer G a := by
  constructor
  · rintro ⟨q, hq⟩
    exact LazardGeneralResolventCriterion.exists_le_conjugateStabilizer_of_baseResolvent_root_of_separable
      G rootAction (specializedOrbitValue G p hp roots)
      (specializedOrbitValue_equivariant
        G p hp roots rootAction roots_equivariant)
      (baseInvariantResolvent G p hp roots rootAction roots_equivariant)
      (baseInvariantResolvent_map
        G p hp roots rootAction roots_equivariant)
      hseparable q hq
  · rintro ⟨a, hle⟩
    obtain ⟨q, hq⟩ := LazardGeneralResolventCriterion.orbitResolvent_has_baseField_root_of_le_conjugateStabilizer
      G rootAction (specializedOrbitValue G p hp roots)
      (specializedOrbitValue_equivariant
        G p hp roots rootAction roots_equivariant) a hle
    exact ⟨q, LazardGeneralResolventCriterion.baseResolvent_isRoot_of_orbitResolvent_isRoot
      G (specializedOrbitValue G p hp roots)
      (baseInvariantResolvent G p hp roots rootAction roots_equivariant)
      (baseInvariantResolvent_map
        G p hp roots rootAction roots_equivariant) q hq⟩

end GaloisSpecialization

section OrderedRootPresentation

variable {F : Type uF} {L : Type uL} {ι : Type uI}
variable [Field F] [Field L] [Algebra F L]
variable [FiniteDimensional F L] [IsGalois F L]
variable [Fintype ι]

/-- A support-level presentation of the labelled roots used by the orbit
action.  `nodup` says that the labels are distinct, while `complete` says
that every distinct root in `L` occurs under a label.  The separate `splits`
field says that the polynomial splits in `L`.

This deliberately does **not** record root multiplicities: for example, a
singleton tuple can present the root support of `(X - C a) ^ 2`.  Use
`ExactRootTuplePresentation` below when claiming the literal factorization
implicit in Lazard's ordered `d` roots. -/
structure RootTuplePresentation (f : F[X]) (roots : ι → L) : Prop where
  splits : (f.map (algebraMap F L)).Splits
  nodup : Function.Injective roots
  complete : ∀ x : L, x ∈ f.rootSet L ↔ ∃ i : ι, roots i = x

/-- A literal, multiplicity-sensitive ordered-root presentation.  The
nonzero polynomial is its leading coefficient times exactly one linear
factor for every label.  Together with `nodup`, this is the Lean analogue of
the associate factorization used by the Coq adapter and of the `d` labelled
roots in Lazard's paper. -/
structure ExactRootTuplePresentation (f : F[X]) (roots : ι → L) : Prop
    extends RootTuplePresentation f roots where
  nonzero : f ≠ 0
  factorization :
    f.map (algebraMap F L) =
      C ((algebraMap F L) f.leadingCoeff) *
        ∏ i : ι, (X - C (roots i))

/-- The ordered root tuple is canonically equivalent to the root set of its
presented polynomial. -/
noncomputable def rootTupleEquiv (f : F[X]) (roots : ι → L)
    (h : RootTuplePresentation f roots) : ι ≃ f.rootSet L :=
  Equiv.ofBijective
    (fun i => ⟨roots i, (h.complete (roots i)).2 ⟨i, rfl⟩⟩)
    ⟨(by
        intro i j hij
        apply h.nodup
        exact congrArg Subtype.val hij),
      (by
        rintro ⟨x, hx⟩
        obtain ⟨i, hi⟩ := (h.complete x).1 hx
        exact ⟨i, Subtype.ext hi⟩)⟩

/-- The permutation representation on the ordered labels, obtained by
transporting the intrinsic Galois action on the polynomial's root set along
`rootTupleEquiv`.  No root-permutation map is supplied by the caller. -/
noncomputable def rootTupleAction (f : F[X]) (roots : ι → L)
    (h : RootTuplePresentation f roots) :
    (L ≃ₐ[F] L) →* Equiv.Perm ι :=
  (rootTupleEquiv f roots h).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (L ≃ₐ[F] L) (f.rootSet L))

omit [FiniteDimensional F L] [IsGalois F L] [Fintype ι] in
@[simp] theorem rootTupleAction_apply (f : F[X]) (roots : ι → L)
    (h : RootTuplePresentation f roots) (σ : L ≃ₐ[F] L) (i : ι) :
    rootTupleAction f roots h σ i =
      (rootTupleEquiv f roots h).symm
        (σ • rootTupleEquiv f roots h i) :=
  rfl

omit [FiniteDimensional F L] [IsGalois F L] [Fintype ι] in
/-- The root-equivariance premise of the explicit invariant adapter follows
from the support-level root presentation. -/
theorem rootTupleAction_equivariant (f : F[X]) (roots : ι → L)
    (h : RootTuplePresentation f roots) (σ : L ≃ₐ[F] L) (i : ι) :
    σ (roots i) = roots (rootTupleAction f roots h σ i) := by
  rw [rootTupleAction_apply]
  let e := rootTupleEquiv f roots h
  have he := congrArg Subtype.val (e.apply_symm_apply (σ • e i))
  change roots (e.symm (σ • e i)) = σ (roots i) at he
  exact he.symm

variable (G : Subgroup (Equiv.Perm ι))
variable [Fintype (LazardGeneralResolventCriterion.Cosets G)]
variable (invariant : MvPolynomial ι F)
variable (invariant_under : InvariantUnder G invariant)
variable (f : F[X]) (roots : ι → L)
variable (presentation : RootTuplePresentation f roots)

/-- The base-field resolvent constructed from a polynomial and a complete
enumeration of its distinct roots. -/
noncomputable def rootTupleBaseInvariantResolvent : F[X] :=
  baseInvariantResolvent G invariant invariant_under roots
    (rootTupleAction f roots presentation)
    (rootTupleAction_equivariant f roots presentation)

omit [Fintype ι] in
theorem rootTupleBaseInvariantResolvent_map :
    (rootTupleBaseInvariantResolvent G invariant invariant_under
      f roots presentation).map (algebraMap F L) =
      LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G invariant invariant_under roots) :=
  baseInvariantResolvent_map G invariant invariant_under roots
    (rootTupleAction f roots presentation)
    (rootTupleAction_equivariant f roots presentation)

omit [Fintype ι] in
/-- The forward implication in support-level root-tuple form.  In particular,
the permutation representation and its evaluation equivariance no longer
occur as hypotheses. -/
theorem rootTupleBaseInvariantResolvent_hasRoot_of_le_baseStabilizer
    (hle : (rootTupleAction f roots presentation).range ≤ G) :
    ∃ q : F,
      (rootTupleBaseInvariantResolvent G invariant invariant_under
        f roots presentation).IsRoot q :=
  baseInvariantResolvent_hasRoot_of_le_baseStabilizer
    G invariant invariant_under roots
      (rootTupleAction f roots presentation)
      (rootTupleAction_equivariant f roots presentation) hle

omit [Fintype ι] in
/-- The support-level ordered-root form of the orbit criterion.
Separability remains only in the converse.  For the literal
multiplicity-sensitive paper interface, use the exact wrappers below. -/
theorem rootTupleBaseInvariantResolvent_hasRoot_iff_image_le_conjugate
    (hseparable :
      (LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G invariant invariant_under roots)).Separable) :
    (∃ q : F,
      (rootTupleBaseInvariantResolvent G invariant invariant_under
        f roots presentation).IsRoot q) ↔
      ∃ a : Equiv.Perm ι,
        (rootTupleAction f roots presentation).range ≤
          LazardGeneralResolventCriterion.conjugateStabilizer G a :=
  baseInvariantResolvent_hasRoot_iff_image_le_conjugate
    G invariant invariant_under roots
      (rootTupleAction f roots presentation)
      (rootTupleAction_equivariant f roots presentation) hseparable

section ExactOrderedRootPresentation

variable (exactPresentation : ExactRootTuplePresentation f roots)

/-- Scalar-extension identity for a multiplicity-sensitive ordered-root
presentation. -/
theorem exactRootTupleBaseInvariantResolvent_map :
    (rootTupleBaseInvariantResolvent G invariant invariant_under
      f roots exactPresentation.toRootTuplePresentation).map
        (algebraMap F L) =
      LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G invariant invariant_under roots) :=
  rootTupleBaseInvariantResolvent_map G invariant invariant_under
    f roots exactPresentation.toRootTuplePresentation

/-- Lazard's forward implication with the literal root factorization made
explicit.  As before, this direction needs no resolvent separability. -/
theorem exactRootTupleBaseInvariantResolvent_hasRoot_of_le_baseStabilizer
    (hle :
      (rootTupleAction f roots
        exactPresentation.toRootTuplePresentation).range ≤ G) :
    ∃ q : F,
      (rootTupleBaseInvariantResolvent G invariant invariant_under
        f roots exactPresentation.toRootTuplePresentation).IsRoot q :=
  rootTupleBaseInvariantResolvent_hasRoot_of_le_baseStabilizer
    G invariant invariant_under f roots
      exactPresentation.toRootTuplePresentation hle

/-- Multiplicity-sensitive ordered-root wrapper for Lazard's Theorem 1,
with separability stated for the constructed resolvent over the base field.
The arbitrary root labelling makes conjugate containment the correct
converse conclusion. -/
theorem exactRootTupleBaseInvariantResolvent_hasRoot_iff_image_le_conjugate
    (hseparable :
      (rootTupleBaseInvariantResolvent G invariant invariant_under
        f roots exactPresentation.toRootTuplePresentation).Separable) :
    (∃ q : F,
      (rootTupleBaseInvariantResolvent G invariant invariant_under
        f roots exactPresentation.toRootTuplePresentation).IsRoot q) ↔
      ∃ a : Equiv.Perm ι,
        (rootTupleAction f roots
          exactPresentation.toRootTuplePresentation).range ≤
            LazardGeneralResolventCriterion.conjugateStabilizer G a :=
  LazardGeneralResolventCriterion.baseResolvent_hasRoot_iff_exists_le_conjugateStabilizer
    G
    (rootTupleAction f roots exactPresentation.toRootTuplePresentation)
    (specializedOrbitValue G invariant invariant_under roots)
    (specializedOrbitValue_equivariant
      G invariant invariant_under roots
        (rootTupleAction f roots exactPresentation.toRootTuplePresentation)
        (rootTupleAction_equivariant
          f roots exactPresentation.toRootTuplePresentation))
    (rootTupleBaseInvariantResolvent G invariant invariant_under
      f roots exactPresentation.toRootTuplePresentation)
    (rootTupleBaseInvariantResolvent_map G invariant invariant_under
      f roots exactPresentation.toRootTuplePresentation)
    hseparable

end ExactOrderedRootPresentation

section PaperExactStabilizerWrappers

variable (exactStabilizer : HasExactRenameStabilizer G invariant)
variable (exactPresentation : ExactRootTuplePresentation f roots)

/-- Paper-facing group-theoretic resolvent wrapper: the ordered roots carry
their exact multiplicity-sensitive factorization, and the displayed
polynomial has formal stabilizer exactly `G`.

This definition does not yet claim that the universal orbit product is the
minimal polynomial over the invariant rational-function field. -/
noncomputable def paperRootTupleResolvent : F[X] :=
  rootTupleBaseInvariantResolvent G invariant
    exactStabilizer.invariantUnder f roots
      exactPresentation.toRootTuplePresentation

omit [Fintype ι]
  [Fintype (LazardGeneralResolventCriterion.Cosets G)] in
/-- The formal conjugates of an exact-stabilizer polynomial are indexed
without repetition by `A/G`. -/
theorem paperUniversalOrbitValue_injective :
    Function.Injective
      (universalOrbitValue G invariant exactStabilizer.invariantUnder) :=
  universalOrbitValue_injective G invariant exactStabilizer

/-- Scalar extension of the paper-facing resolvent is the explicit product
over its specialized coset values. -/
theorem paperRootTupleResolvent_map :
    (paperRootTupleResolvent (G := G) (invariant := invariant)
      (f := f) (roots := roots) (exactStabilizer := exactStabilizer)
      (exactPresentation := exactPresentation)).map (algebraMap F L) =
      LazardGeneralResolventCriterion.orbitResolvent G
        (specializedOrbitValue G invariant
          exactStabilizer.invariantUnder roots) :=
  rootTupleBaseInvariantResolvent_map G invariant
    exactStabilizer.invariantUnder f roots
      exactPresentation.toRootTuplePresentation

/-- Forward implication of Lazard's Theorem 1 with exact root presentation
and exact renaming stabilizer exposed, and with no separability assumption. -/
theorem paperRootTupleResolvent_hasRoot_of_le_baseStabilizer
    (hle :
      (rootTupleAction f roots
        exactPresentation.toRootTuplePresentation).range ≤ G) :
    ∃ q : F,
      (paperRootTupleResolvent (G := G) (invariant := invariant)
        (f := f) (roots := roots) (exactStabilizer := exactStabilizer)
        (exactPresentation := exactPresentation)).IsRoot q := by
  simpa only [paperRootTupleResolvent] using
    exactRootTupleBaseInvariantResolvent_hasRoot_of_le_baseStabilizer
      G invariant exactStabilizer.invariantUnder f roots
        exactPresentation hle

/-- Group-theoretic paper-facing orbit criterion.  Exact formal stabilizer
makes the universal coset values distinct, while separability is still stated
after specialization because evaluation can create new collisions.  The
separate universal minimal-polynomial identification remains outside this
wrapper. -/
theorem paperRootTupleResolvent_hasRoot_iff_image_le_conjugate
    (hseparable :
      (paperRootTupleResolvent (G := G) (invariant := invariant)
        (f := f) (roots := roots) (exactStabilizer := exactStabilizer)
        (exactPresentation := exactPresentation)).Separable) :
    (∃ q : F,
      (paperRootTupleResolvent (G := G) (invariant := invariant)
        (f := f) (roots := roots) (exactStabilizer := exactStabilizer)
        (exactPresentation := exactPresentation)).IsRoot q) ↔
      ∃ a : Equiv.Perm ι,
        (rootTupleAction f roots
          exactPresentation.toRootTuplePresentation).range ≤
            LazardGeneralResolventCriterion.conjugateStabilizer G a := by
  simpa only [paperRootTupleResolvent] using
    exactRootTupleBaseInvariantResolvent_hasRoot_iff_image_le_conjugate
      G invariant exactStabilizer.invariantUnder f roots
        exactPresentation hseparable

end PaperExactStabilizerWrappers

end OrderedRootPresentation

end LeanProofs.PolynomialFormulas.LazardGeneralResolventExplicit
