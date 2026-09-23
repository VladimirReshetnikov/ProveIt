import Surreal.Foundations.OmnificIntegers
import Surreal.Surcomplex.ComplexEmbedding

/-!
# The actual complex nonnegative-growth-support ring

The complex ring and retraction clauses of `odg:prop:ring`. The ring is
literally the subring of actual surcomplex numbers with both coordinates
in the real nonnegative-support ring. Its constant-term kernel is the
complex purely infinite ideal.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The actual subring `B_R[i]` of surcomplex numbers. -/
def nonnegativeSupportSubring : Subring Surcomplex.{u} where
  carrier := {z | z.re ∈ SignSequence.nonnegativeSupportSubring ∧
    z.im ∈ SignSequence.nonnegativeSupportSubring}
  zero_mem' := ⟨Subring.zero_mem _, Subring.zero_mem _⟩
  one_mem' := ⟨Subring.one_mem _, Subring.zero_mem _⟩
  add_mem' := fun hz hw => ⟨Subring.add_mem _ hz.1 hw.1, Subring.add_mem _ hz.2 hw.2⟩
  neg_mem' := fun hz => ⟨Subring.neg_mem _ hz.1, Subring.neg_mem _ hz.2⟩
  mul_mem' := by
    intro z w hz hw
    constructor
    · rw [mul_re]
      exact Subring.sub_mem _ (Subring.mul_mem _ hz.1 hw.1) (Subring.mul_mem _ hz.2 hw.2)
    · rw [mul_im]
      exact Subring.add_mem _ (Subring.mul_mem _ hz.1 hw.2) (Subring.mul_mem _ hz.2 hw.1)

/-- The real coordinate, retaining membership in the actual support-restricted real ring. -/
def nonnegativeRe (z : nonnegativeSupportSubring.{u}) : SignSequence.nonnegativeSupportSubring :=
  ⟨z.val.re, z.property.1⟩

/-- The imaginary coordinate, retaining membership in the same real ring. -/
def nonnegativeIm (z : nonnegativeSupportSubring.{u}) : SignSequence.nonnegativeSupportSubring :=
  ⟨z.val.im, z.property.2⟩

/-- Constant-term extraction is an ordinary-complex-valued ring homomorphism. -/
def constantCoeff : nonnegativeSupportSubring.{u} →+* ℂ where
  toFun z := ⟨SignSequence.constantCoeff (nonnegativeRe z),
    SignSequence.constantCoeff (nonnegativeIm z)⟩
  map_zero' := by apply Complex.ext <;> exact map_zero SignSequence.constantCoeff
  map_one' := by
    apply Complex.ext
    · exact map_one SignSequence.constantCoeff
    · exact map_zero SignSequence.constantCoeff
  map_add' z w := by
    apply Complex.ext
    · exact map_add SignSequence.constantCoeff (nonnegativeRe z) (nonnegativeRe w)
    · exact map_add SignSequence.constantCoeff (nonnegativeIm z) (nonnegativeIm w)
  map_mul' z w := by
    have hre : nonnegativeRe (z * w) =
        nonnegativeRe z * nonnegativeRe w - nonnegativeIm z * nonnegativeIm w :=
      Subtype.ext (mul_re z.val w.val)
    have him : nonnegativeIm (z * w) =
        nonnegativeRe z * nonnegativeIm w + nonnegativeIm z * nonnegativeRe w :=
      Subtype.ext (mul_im z.val w.val)
    apply Complex.ext
    · change SignSequence.constantCoeff (nonnegativeRe (z * w)) = _
      rw [hre, map_sub, map_mul, map_mul]
      rfl
    · change SignSequence.constantCoeff (nonnegativeIm (z * w)) = _
      rw [him, map_add, map_mul, map_mul]
      rfl

/-- Ordinary complex numbers embed as constant elements of the support-restricted ring. -/
def complexConstants : ℂ →+* nonnegativeSupportSubring.{u} :=
  ofComplex.codRestrict _ (fun z =>
    ⟨SignSequence.ofReal_mem_nonnegativeSupportSubring z.re,
      SignSequence.ofReal_mem_nonnegativeSupportSubring z.im⟩)

@[simp] theorem constantCoeff_complexConstants (z : ℂ) :
    constantCoeff (complexConstants.{u} z) = z := by
  apply Complex.ext
  · exact SignSequence.constantCoeff_realConstants z.re
  · exact SignSequence.constantCoeff_realConstants z.im

/-- The complex constant-term retraction is surjective. -/
theorem constantCoeff_surjective : Function.Surjective (constantCoeff.{u}) :=
  fun z => ⟨complexConstants z, constantCoeff_complexConstants z⟩

/-- The complex purely infinite ideal is the kernel of the constant-term map. -/
def purelyInfiniteIdeal : Ideal nonnegativeSupportSubring.{u} := RingHom.ker constantCoeff

/-- Both real coordinates of the complex ideal are purely infinite. -/
theorem mem_purelyInfiniteIdeal_iff (z : nonnegativeSupportSubring.{u}) :
    z ∈ purelyInfiniteIdeal ↔
      nonnegativeRe z ∈ SignSequence.purelyInfiniteIdeal ∧
      nonnegativeIm z ∈ SignSequence.purelyInfiniteIdeal := by
  change (⟨_, _⟩ : ℂ) = 0 ↔ _
  rw [Complex.ext_iff]
  rfl


/-- Every element splits into its ordinary complex constant and a purely infinite remainder. -/
theorem constant_decomposition (z : nonnegativeSupportSubring.{u}) :
    ∃ w ∈ purelyInfiniteIdeal, z = complexConstants (constantCoeff z) + w := by
  refine ⟨z - complexConstants (constantCoeff z), ?_, by abel⟩
  change constantCoeff (z - complexConstants (constantCoeff z)) = 0
  rw [map_sub, constantCoeff_complexConstants, sub_self]

/-- The complex quotient by purely infinite terms is the ordinary complex field. -/
def nonnegativeSupportQuotientEquiv : nonnegativeSupportSubring.{u} ⧸ purelyInfiniteIdeal ≃+* ℂ :=
  constantCoeff.quotientKerEquivOfSurjective constantCoeff_surjective

end
end Surreal.Surcomplex
