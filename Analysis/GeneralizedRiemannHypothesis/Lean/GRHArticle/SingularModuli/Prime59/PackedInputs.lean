import GRHArticle.SingularModuli.Prime59.DivisorInputs
import GRHArticle.SingularModuli.Prime59.InputPrefixes
import GRHArticle.SingularModuli.ModularInvariantPrefixCertificate
import GRHArticle.SingularModuli.HeckePackedLeafChunks

/-!
# Packed coefficient inputs for the level-59 prefix checks

Mapping and zipping take place in the original divisor blocks. The
resulting polynomial evaluations have exactly the same coefficients.
-/

namespace GRHArticle.SingularModuli.Prime59

open IntegerPolynomialExpression DivisorBlocks DivisorPowerPrefixCertificate

def sigma3Chunks : List (List ℤ) :=
  [sigma3_00, sigma3_01, sigma3_02, sigma3_03, sigma3_04,
  sigma3_05, sigma3_06, sigma3_07, sigma3_08, sigma3_09,
  sigma3_10, sigma3_11, sigma3_12, sigma3_13, sigma3_14].map (List.map Int.ofNat)

theorem sigma3Chunks_flatten : sigma3Chunks.flatten = sigma3.map Int.ofNat := by
  simp only [sigma3Chunks, sigma3, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.map_append, List.append_assoc]

def sigma5Chunks : List (List ℤ) :=
  [sigma5_00, sigma5_01, sigma5_02, sigma5_03, sigma5_04,
  sigma5_05, sigma5_06, sigma5_07, sigma5_08, sigma5_09,
  sigma5_10, sigma5_11, sigma5_12, sigma5_13, sigma5_14].map (List.map Int.ofNat)

theorem sigma5Chunks_flatten : sigma5Chunks.flatten = sigma5.map Int.ofNat := by
  simp only [sigma5Chunks, sigma5, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.map_append, List.append_assoc]

private theorem sigma_length_00 : sigma3_00.length = sigma5_00.length := by
  rw [sigma3_00_checked, sigma5_00_checked]
  simp [coefficientsBlock]

private theorem sigma_length_01 : sigma3_01.length = sigma5_01.length := by
  rw [sigma3_01_checked, sigma5_01_checked]
  simp [coefficientsBlock]

private theorem sigma_length_02 : sigma3_02.length = sigma5_02.length := by
  rw [sigma3_02_checked, sigma5_02_checked]
  simp [coefficientsBlock]

private theorem sigma_length_03 : sigma3_03.length = sigma5_03.length := by
  rw [sigma3_03_checked, sigma5_03_checked]
  simp [coefficientsBlock]

private theorem sigma_length_04 : sigma3_04.length = sigma5_04.length := by
  rw [sigma3_04_checked, sigma5_04_checked]
  simp [coefficientsBlock]

private theorem sigma_length_05 : sigma3_05.length = sigma5_05.length := by
  rw [sigma3_05_checked, sigma5_05_checked]
  simp [coefficientsBlock]

private theorem sigma_length_06 : sigma3_06.length = sigma5_06.length := by
  rw [sigma3_06_checked, sigma5_06_checked]
  simp [coefficientsBlock]

private theorem sigma_length_07 : sigma3_07.length = sigma5_07.length := by
  rw [sigma3_07_checked, sigma5_07_checked]
  simp [coefficientsBlock]

private theorem sigma_length_08 : sigma3_08.length = sigma5_08.length := by
  rw [sigma3_08_checked, sigma5_08_checked]
  simp [coefficientsBlock]

private theorem sigma_length_09 : sigma3_09.length = sigma5_09.length := by
  rw [sigma3_09_checked, sigma5_09_checked]
  simp [coefficientsBlock]

private theorem sigma_length_10 : sigma3_10.length = sigma5_10.length := by
  rw [sigma3_10_checked, sigma5_10_checked]
  simp [coefficientsBlock]

private theorem sigma_length_11 : sigma3_11.length = sigma5_11.length := by
  rw [sigma3_11_checked, sigma5_11_checked]
  simp [coefficientsBlock]

private theorem sigma_length_12 : sigma3_12.length = sigma5_12.length := by
  rw [sigma3_12_checked, sigma5_12_checked]
  simp [coefficientsBlock]

private theorem sigma_length_13 : sigma3_13.length = sigma5_13.length := by
  rw [sigma3_13_checked, sigma5_13_checked]
  simp [coefficientsBlock]

def linearChunks : List (List ℤ) := [
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_00 sigma5_00,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_01 sigma5_01,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_02 sigma5_02,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_03 sigma5_03,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_04 sigma5_04,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_05 sigma5_05,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_06 sigma5_06,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_07 sigma5_07,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_08 sigma5_08,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_09 sigma5_09,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_10 sigma5_10,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_11 sigma5_11,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_12 sigma5_12,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_13 sigma5_13,
  ModularInvariantPrefixCertificate.linearCoefficients sigma3_14 sigma5_14]

theorem linearChunks_flatten :
    linearChunks.flatten = ModularInvariantPrefixCertificate.linearCoefficients sigma3 sigma5 := by
  unfold linearChunks sigma3 sigma5 ModularInvariantPrefixCertificate.linearCoefficients
  simp only [List.append_assoc]
  rw [List.zipWith_append sigma_length_00]
  rw [List.zipWith_append sigma_length_01]
  rw [List.zipWith_append sigma_length_02]
  rw [List.zipWith_append sigma_length_03]
  rw [List.zipWith_append sigma_length_04]
  rw [List.zipWith_append sigma_length_05]
  rw [List.zipWith_append sigma_length_06]
  rw [List.zipWith_append sigma_length_07]
  rw [List.zipWith_append sigma_length_08]
  rw [List.zipWith_append sigma_length_09]
  rw [List.zipWith_append sigma_length_10]
  rw [List.zipWith_append sigma_length_11]
  rw [List.zipWith_append sigma_length_12]
  rw [List.zipWith_append sigma_length_13]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

def packedDiscriminant (w : ℕ) : ℤ :=
  packedLeafChunks w discriminantBlocks

def packedInvariant (w : ℕ) : ℤ :=
  packedLeafChunks w invariantBlocks

theorem packedDiscriminant_eq (w : ℕ) :
    packedDiscriminant w = (coefficients discriminant).packedEval w := by
  rw [packedDiscriminant, packedLeafChunks_eq, discriminant]

theorem packedInvariant_eq (w : ℕ) :
    packedInvariant w = (coefficients invariant).packedEval w := by
  rw [packedInvariant, packedLeafChunks_eq, invariant]

end GRHArticle.SingularModuli.Prime59
