import Surreal.Surcomplex.SmallHahnRealization
import Surreal.Surcomplex.GaussianOmnificAutomorphisms
import Surreal.HahnSeries.CharacterTwist

/-!
# Character twists of actual surcomplex numbers

The support and Gaussian-ring preservation assertions of `odg:def:lem:twist`,
for every multiplicative character of the native growth exponent group.
-/

universe u
namespace Surreal.Surcomplex
noncomputable section

private theorem small_twist_image (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) (z : Surcomplex.{u}) :
    Small.{u} (HahnSeries.characterTwist χ (rawNormalForm z)).support := by
  change Small.{u} (HahnSeries.twist χ (rawNormalForm z)).support
  rw [HahnSeries.support_twist]
  infer_instance

private def characterMap (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) (z : Surcomplex.{u}) : Surcomplex.{u} :=
  ofSmallHahn (HahnSeries.characterTwist χ (rawNormalForm z)) (small_twist_image χ z)

private theorem rawNormalForm_characterMap (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) (z : Surcomplex.{u}) :
    rawNormalForm (characterMap χ z) = HahnSeries.characterTwist χ (rawNormalForm z) :=
  rawNormalForm_ofSmallHahn _ _

private theorem characterMap_inverse (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) (z : Surcomplex.{u}) :
    characterMap χ⁻¹ (characterMap χ z) = z := by
  apply rawNormalForm_injective
  rw [rawNormalForm_characterMap, rawNormalForm_characterMap]
  exact HahnSeries.twist_inverse χ (rawNormalForm z)

/-- Character twisting evaluated in the actual surcomplex field. -/
def characterAutomorphism (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) : Surcomplex.{u} ≃+* Surcomplex.{u} where
  toFun := characterMap χ
  invFun := characterMap χ⁻¹
  left_inv := characterMap_inverse χ
  right_inv z := by simpa only [inv_inv] using characterMap_inverse χ⁻¹ z
  map_add' z w := by
    apply rawNormalForm_injective
    rw [rawNormalForm_characterMap, rawNormalForm_add, map_add, rawNormalForm_add,
      rawNormalForm_characterMap, rawNormalForm_characterMap]
  map_mul' z w := by
    apply rawNormalForm_injective
    rw [rawNormalForm_characterMap, rawNormalForm_mul, map_mul, rawNormalForm_mul,
      rawNormalForm_characterMap, rawNormalForm_characterMap]

@[simp] theorem rawNormalForm_characterAutomorphism (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (z : Surcomplex.{u}) : rawNormalForm (characterAutomorphism χ z) =
      HahnSeries.characterTwist χ (rawNormalForm z) := rawNormalForm_characterMap χ z

@[simp] theorem coeff_characterAutomorphism (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (z : Surcomplex.{u}) (a : _root_.Surreal.{u}ᵒᵈ) :
    (rawNormalForm (characterAutomorphism χ z)).coeff a = (rawNormalForm z).coeff a * χ a := by
  rw [rawNormalForm_characterAutomorphism]
  rfl

theorem support_characterAutomorphism (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) (z : Surcomplex.{u}) :
    (rawNormalForm (characterAutomorphism χ z)).support = (rawNormalForm z).support := by
  rw [rawNormalForm_characterAutomorphism]
  exact HahnSeries.support_twist χ (rawNormalForm z)

@[simp] theorem characterAutomorphism_inverse (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) (z : Surcomplex.{u}) :
    characterAutomorphism χ⁻¹ (characterAutomorphism χ z) = z := characterMap_inverse χ z

/-- Every character twist fixes every ordinary complex number. -/
@[simp] theorem characterAutomorphism_ofComplex (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) (c : ℂ) :
    characterAutomorphism χ (ofComplex c) = ofComplex c := by
  apply rawNormalForm_injective
  rw [rawNormalForm_characterAutomorphism, rawNormalForm_ofComplex]
  exact HahnSeries.characterTwist_C χ c

/-- Each real Conway monomial acquires the character value at its growth exponent. -/
theorem characterAutomorphism_real_omegaPower (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (a : Foundations.SignSequence.{u}) :
    characterAutomorphism χ (ofReal (Foundations.SignSequence.omegaPower a)) =
      ofComplex (χ (OrderDual.toDual (Foundations.SignSequence.toSurreal a))) *
        ofReal (Foundations.SignSequence.omegaPower a) := by
  apply rawNormalForm_injective
  rw [rawNormalForm_characterAutomorphism, rawNormalForm_mul, rawNormalForm_ofComplex,
    rawNormalForm_real_omegaPower, HahnSeries.characterTwist_single]
  change _ = _root_.HahnSeries.single 0 _ * _root_.HahnSeries.single _ 1
  simp only [_root_.HahnSeries.single_mul_single, zero_add, one_mul, mul_one]

/-- Character twists preserve the full support ring. -/
theorem characterAutomorphism_mem_supportRing (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ)
    {z : Surcomplex.{u}} (hz : z ∈ nonnegativeSupportSubring) :
    characterAutomorphism χ z ∈ nonnegativeSupportSubring := by
  rw [mem_supportRing_iff_rawNormalForm] at hz ⊢
  intro a ha
  rw [coeff_characterAutomorphism, hz a ha, zero_mul]

/-- The zero coefficient is unchanged by a character twist. -/
theorem constantCoeff_characterAutomorphism (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (z : nonnegativeSupportSubring.{u}) :
    constantCoeff ⟨characterAutomorphism χ z.val, characterAutomorphism_mem_supportRing χ z.property⟩ =
      constantCoeff z := by
  rw [← supportHahnEmbedding_constantCoeff, ← supportHahnEmbedding_constantCoeff z]
  change (rawNormalForm (characterAutomorphism χ z.val)).coeff 0 = (rawNormalForm z.val).coeff 0
  rw [coeff_characterAutomorphism, AddChar.map_zero_eq_one, mul_one]

private def gaussianCharacterMap (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (z : GaussianOmnificInteger.{u}) : GaussianOmnificInteger.{u} :=
  ⟨⟨characterAutomorphism χ z.val.val, characterAutomorphism_mem_supportRing χ z.val.property⟩, by
    change ∃ b : GaussianInt, GaussianInt.toComplex b = constantCoeff _
    rw [constantCoeff_characterAutomorphism]
    exact z.property⟩

/-- Every character twist restricts to a Gaussian omnific automorphism. -/
def gaussianCharacterAutomorphism (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) :
    GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u} where
  toFun := gaussianCharacterMap χ
  invFun := gaussianCharacterMap χ⁻¹
  left_inv z := by
    apply gaussianOmnificToSurcomplex_injective
    exact characterAutomorphism_inverse χ (gaussianOmnificToSurcomplex z)
  right_inv z := by
    apply gaussianOmnificToSurcomplex_injective
    change characterAutomorphism χ (characterAutomorphism χ⁻¹ (gaussianOmnificToSurcomplex z)) = _
    simpa only [inv_inv] using characterAutomorphism_inverse χ⁻¹ (gaussianOmnificToSurcomplex z)
  map_add' z w := by
    apply gaussianOmnificToSurcomplex_injective
    change characterAutomorphism χ (gaussianOmnificToSurcomplex (z + w)) =
      gaussianOmnificToSurcomplex (gaussianCharacterMap χ z + gaussianCharacterMap χ w)
    rw [map_add, map_add, map_add]; rfl
  map_mul' z w := by
    apply gaussianOmnificToSurcomplex_injective
    change characterAutomorphism χ (gaussianOmnificToSurcomplex (z * w)) =
      gaussianOmnificToSurcomplex (gaussianCharacterMap χ z * gaussianCharacterMap χ w)
    rw [map_mul, map_mul, map_mul]; rfl

@[simp] theorem gaussianOmnificToSurcomplex_characterAutomorphism
    (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ) (z : GaussianOmnificInteger.{u}) :
    gaussianOmnificToSurcomplex (gaussianCharacterAutomorphism χ z) =
      characterAutomorphism χ (gaussianOmnificToSurcomplex z) := rfl

/-- Gaussian ordinary constants are fixed pointwise, including all permissible ring parameters. -/
theorem gaussianCharacterAutomorphism_constants (χ : AddChar (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (a : GaussianInt) : gaussianCharacterAutomorphism χ (gaussianOmnificConstants a) = gaussianOmnificConstants a := by
  apply gaussianOmnificToSurcomplex_injective
  exact characterAutomorphism_ofComplex χ (GaussianInt.toComplex a)

end
end Surreal.Surcomplex
