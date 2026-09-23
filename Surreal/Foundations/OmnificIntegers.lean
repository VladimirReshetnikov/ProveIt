import Surreal.Foundations.SmallNormalFormFieldEquiv
import Surreal.HahnSeries.NonpositiveSupport
import Surreal.Algebra.CoefficientPullback

/-!
# Actual omnific integers and constant-term retractions

The real and omnific ring clauses of `odg:prop:ring`, with the exact
normal-form support condition of `odg:def:rings` and `found:eq:omnific`.
The rings are subrings of the constructed sign field, using its proved
normal-form equivalence. Supports remain small in the lower universe;
no replacement of all surreals by a fixed small Hahn workspace is made.
-/

universe u
namespace Surreal.Foundations.SignSequence

open SmallNormalForm

noncomputable section

/-- The canonical normal form regarded as a Hahn series with decreasing growth exponents. -/
def normalFormHahnHom : SignSequence.{u} →+* _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℝ where
  toFun x := ofLex (normalForm x).val
  map_zero' := by rw [normalForm_zero]; rfl
  map_one' := by rw [normalForm_one]; rfl
  map_add' x y := by rw [normalForm_add]; rfl
  map_mul' x y := by rw [normalForm_mul]; rfl

/-- The actual surreal subring whose Conway growth exponents are all nonnegative. -/
def nonnegativeSupportSubring : Subring SignSequence.{u} :=
  (Surreal.HahnSeries.nonpositiveSupportSubring (_root_.Surreal.{u}ᵒᵈ) ℝ).comap normalFormHahnHom

/-- The subring condition is exactly the absence of negative growth exponents. -/
theorem mem_nonnegativeSupportSubring_iff (x : SignSequence.{u}) :
    x ∈ nonnegativeSupportSubring ↔ ∀ a, a < 0 → coeff (normalForm x) a = 0 := by
  constructor
  · intro hx a ha
    apply hx (OrderDual.toDual (toSurreal a))
    change toSurreal a < 0
    simpa only [toSurreal_zero] using (toSurreal_lt_iff a 0).mpr ha
  · intro hx b hb
    obtain ⟨a, ha⟩ := toSurreal_surjective (OrderDual.ofDual b)
    have ha0 : a < 0 := (toSurreal_lt_iff a 0).mp (by
      rw [ha, toSurreal_zero]
      exact hb)
    have he := hx a ha0
    change _root_.SurrealHahnSeries.coeff (normalForm x) (toSurreal a) = 0 at he
    rw [ha] at he
    exact he

/-- Real constants belong to the nonnegative-support subring. -/
theorem ofReal_mem_nonnegativeSupportSubring (r : ℝ) :
    ofReal r ∈ nonnegativeSupportSubring.{u} := by
  rw [mem_nonnegativeSupportSubring_iff]
  intro a ha
  simp only [normalForm_ofReal, coeff_single, if_neg (ne_of_lt ha)]

/-- Constant coefficient, restricted to the actual nonnegative-support subring. -/
def constantCoeff : nonnegativeSupportSubring.{u} →+* ℝ :=
  Surreal.HahnSeries.nonpositiveConstantCoeff.comp
    (normalFormHahnHom.comp nonnegativeSupportSubring.subtype |>.codRestrict _
      (fun x => x.property))

@[simp] theorem constantCoeff_eq (x : nonnegativeSupportSubring.{u}) :
    constantCoeff x = coeff (normalForm x.val) 0 := by
  change _ = _root_.SurrealHahnSeries.coeff (normalForm x.val) (toSurreal 0)
  rw [toSurreal_zero]
  rfl

/-- Inclusion of real constants is a section of the constant-term map. -/
def realConstants : ℝ →+* nonnegativeSupportSubring.{u} :=
  ofReal.toRingHom.codRestrict _ ofReal_mem_nonnegativeSupportSubring

@[simp] theorem constantCoeff_realConstants (r : ℝ) : constantCoeff (realConstants.{u} r) = r := by
  rw [constantCoeff_eq]
  change coeff (normalForm (ofReal r : SignSequence.{u})) 0 = r
  simp

/-- The actual nonnegative-support ring retracts onto the ordinary reals. -/
theorem constantCoeff_surjective : Function.Surjective (constantCoeff.{u}) :=
  fun r => ⟨realConstants r, constantCoeff_realConstants r⟩

/-- Purely infinite actual surreals, as an ideal of the nonnegative-support ring. -/
def purelyInfiniteIdeal : Ideal nonnegativeSupportSubring.{u} := RingHom.ker constantCoeff

/-- The ideal condition is exactly strictly positive Conway growth support. -/
theorem mem_purelyInfiniteIdeal_iff (x : nonnegativeSupportSubring.{u}) :
    x ∈ purelyInfiniteIdeal ↔ ∀ a ∈ support (normalForm x.val), 0 < a := by
  change constantCoeff x = 0 ↔ _
  rw [constantCoeff_eq]
  constructor
  · intro hx a ha
    have ha0 : ¬ a < 0 := fun h => ha ((mem_nonnegativeSupportSubring_iff x.val).mp x.property a h)
    exact lt_of_le_of_ne (le_of_not_gt ha0) (fun h => ha (h.symm ▸ hx))
  · intro hx
    by_contra h
    exact (lt_irrefl (0 : SignSequence.{u})) (hx 0 h)

/-- The omnific subring: arbitrary real positive-growth coefficients and an integer constant term. -/
def omnificSubring : Subring nonnegativeSupportSubring.{u} :=
  CoefficientPullback.subring constantCoeff (Int.castRingHom ℝ)

/-- The actual omnific integers, with the ring and order inherited from surreal numbers. -/
abbrev OmnificInteger : Type (u + 1) := omnificSubring.{u}

/-- The canonical embedding of omnific integers into the actual surreal field. -/
def omnificToSurreal : OmnificInteger.{u} →+* SignSequence.{u} :=
  nonnegativeSupportSubring.subtype.comp omnificSubring.subtype

/-- Every omnific integer is determined by its value as an actual surreal. -/
theorem omnificToSurreal_injective : Function.Injective (omnificToSurreal.{u}) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

/-- Extract the integer constant coefficient of an actual omnific integer. -/
def omnificConstantCoeff : OmnificInteger.{u} →+* ℤ :=
  CoefficientPullback.retraction constantCoeff (Int.castRingHom ℝ) Int.cast_injective

/-- Casting the integer coefficient to the reals recovers the actual normal-form coefficient. -/
@[simp] theorem cast_omnificConstantCoeff (x : OmnificInteger.{u}) :
    (omnificConstantCoeff x : ℝ) = coeff (normalForm (omnificToSurreal x)) 0 := by
  exact (CoefficientPullback.embedding_retraction constantCoeff (Int.castRingHom ℝ)
    Int.cast_injective x).trans (constantCoeff_eq x.val)

/-- The ordinary integers embed as constant omnific integers. -/
def omnificIntCast : ℤ →+* OmnificInteger.{u} :=
  CoefficientPullback.sectionMap constantCoeff (Int.castRingHom ℝ) realConstants
    constantCoeff_realConstants

@[simp] theorem omnificConstantCoeff_intCast (n : ℤ) :
    omnificConstantCoeff (omnificIntCast.{u} n) = n :=
  CoefficientPullback.retraction_sectionMap constantCoeff (Int.castRingHom ℝ)
    Int.cast_injective realConstants constantCoeff_realConstants n

/-- The omnific constant-term homomorphism is onto the ordinary integers. -/
theorem omnificConstantCoeff_surjective : Function.Surjective (omnificConstantCoeff.{u}) :=
  fun n => ⟨omnificIntCast n, omnificConstantCoeff_intCast n⟩

/-- Purely infinite elements form an ideal of the omnific ring as well. -/
def omnificPurelyInfiniteIdeal : Ideal OmnificInteger.{u} := RingHom.ker omnificConstantCoeff

/-- The omnific ideal has exactly strictly positive growth support. -/
theorem mem_omnificPurelyInfiniteIdeal_iff (x : OmnificInteger.{u}) :
    x ∈ omnificPurelyInfiniteIdeal ↔ ∀ a ∈ support (normalForm (omnificToSurreal x)), 0 < a := by
  rw [show x ∈ omnificPurelyInfiniteIdeal ↔ constantCoeff x.val = 0 from
    CoefficientPullback.mem_ker_iff constantCoeff (Int.castRingHom ℝ) Int.cast_injective x]
  exact mem_purelyInfiniteIdeal_iff x.val

/-- Modding out the purely infinite omnific ideal recovers exactly the ordinary integers. -/
def omnificQuotientEquiv : OmnificInteger.{u} ⧸ omnificPurelyInfiniteIdeal ≃+* ℤ :=
  omnificConstantCoeff.quotientKerEquivOfSurjective omnificConstantCoeff_surjective



/-- Every purely infinite element of the real ring is also an omnific integer. -/
theorem purelyInfinite_mem_omnificSubring (x : nonnegativeSupportSubring.{u})
    (hx : x ∈ purelyInfiniteIdeal) : x ∈ omnificSubring := by
  change ∃ n : ℤ, (n : ℝ) = constantCoeff x
  exact ⟨0, by simpa only [Int.cast_zero] using hx.symm⟩

/-- Every element of the real ring is its real constant plus a purely infinite remainder. -/
theorem real_constant_decomposition (x : nonnegativeSupportSubring.{u}) :
    ∃ y ∈ purelyInfiniteIdeal, x = realConstants (constantCoeff x) + y := by
  refine ⟨x - realConstants (constantCoeff x), ?_, by abel⟩
  change constantCoeff (x - realConstants (constantCoeff x)) = 0
  rw [map_sub, constantCoeff_realConstants, sub_self]

/-- Every omnific integer is its integer constant plus a purely infinite remainder. -/
theorem omnific_constant_decomposition (x : OmnificInteger.{u}) :
    ∃ y ∈ omnificPurelyInfiniteIdeal, x = omnificIntCast (omnificConstantCoeff x) + y := by
  refine ⟨x - omnificIntCast (omnificConstantCoeff x), ?_, by abel⟩
  change omnificConstantCoeff (x - omnificIntCast (omnificConstantCoeff x)) = 0
  rw [map_sub, omnificConstantCoeff_intCast, sub_self]

/-- Membership in the omnific subring imposes only an integer constant coefficient. -/
theorem mem_omnificSubring_iff (x : nonnegativeSupportSubring.{u}) :
    x ∈ omnificSubring ↔ ∃ n : ℤ, (n : ℝ) = coeff (normalForm x.val) 0 := by
  change (∃ n : ℤ, (n : ℝ) = constantCoeff x) ↔ _
  rw [constantCoeff_eq]

/-- The image in the actual field is precisely the normal-form definition of omnific integers. -/
theorem exists_omnific_iff (x : SignSequence.{u}) :
    (∃ z : OmnificInteger.{u}, omnificToSurreal z = x) ↔
      (∀ a, a < 0 → coeff (normalForm x) a = 0) ∧
      ∃ n : ℤ, (n : ℝ) = coeff (normalForm x) 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(mem_nonnegativeSupportSubring_iff z.val.val).mp z.val.property,
      (mem_omnificSubring_iff z.val).mp z.property⟩
  · rintro ⟨hx, hn⟩
    let y : nonnegativeSupportSubring.{u} := ⟨x, (mem_nonnegativeSupportSubring_iff x).mpr hx⟩
    exact ⟨⟨y, (mem_omnificSubring_iff y).mpr hn⟩, rfl⟩

/-- The omnific inclusion preserves the inherited strict order. -/
theorem omnificToSurreal_strictMono : StrictMono (omnificToSurreal.{u}) := fun _ _ h => h

@[simp] theorem omnificToSurreal_intCast (n : ℤ) :
    omnificToSurreal (omnificIntCast.{u} n) = n := by
  change ofReal (n : ℝ) = (n : SignSequence.{u})
  exact map_intCast ofReal n

/-- Quotienting the real nonnegative-support ring by purely infinite terms recovers the reals. -/
def nonnegativeSupportQuotientEquiv : nonnegativeSupportSubring.{u} ⧸ purelyInfiniteIdeal ≃+* ℝ :=
  constantCoeff.quotientKerEquivOfSurjective constantCoeff_surjective

/-- The real coefficient action on the nonnegative-support ring. -/
abbrev nonnegativeSupportRealAlgebra : Algebra ℝ nonnegativeSupportSubring.{u} :=
  realConstants.toAlgebra

attribute [local instance] nonnegativeSupportRealAlgebra

/-- Real scalar multiplication is the multiplication inherited from the actual surreal field. -/
theorem nonnegativeSupport_smul_val (r : ℝ) (x : nonnegativeSupportSubring.{u}) :
    (r • x).val = ofReal r * x.val := rfl

/-- The purely infinite ideal is also a vector subspace over the ordinary reals. -/
def purelyInfiniteSubmodule : Submodule ℝ nonnegativeSupportSubring.{u} :=
  purelyInfiniteIdeal.restrictScalars ℝ

/-- The vector subspace has exactly the required positive-growth support. -/
theorem mem_purelyInfiniteSubmodule_iff (x : nonnegativeSupportSubring.{u}) :
    x ∈ purelyInfiniteSubmodule ↔ ∀ a ∈ support (normalForm x.val), 0 < a :=
  mem_purelyInfiniteIdeal_iff x

end
end Surreal.Foundations.SignSequence
