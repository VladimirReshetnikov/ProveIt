import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows00
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows01
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows02
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows03
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows04
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows05
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows06
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows07
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows08
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows09
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows10
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows11
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows12
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows13
import GRHArticle.SingularModuli.Prime59.DivisorBlocks.Rows14

/-!
# The divisor-power inputs for the level-59 diagonal
-/

namespace GRHArticle.SingularModuli.Prime59

open DivisorPowerPrefixCertificate DivisorBlocks

private def factors : List (List (ℕ × ℕ)) :=
  rows00 ++
  rows01 ++
  rows02 ++
  rows03 ++
  rows04 ++
  rows05 ++
  rows06 ++
  rows07 ++
  rows08 ++
  rows09 ++
  rows10 ++
  rows11 ++
  rows12 ++
  rows13 ++
  rows14

def sigma3 : List ℕ :=
  sigma3_00 ++
  sigma3_01 ++
  sigma3_02 ++
  sigma3_03 ++
  sigma3_04 ++
  sigma3_05 ++
  sigma3_06 ++
  sigma3_07 ++
  sigma3_08 ++
  sigma3_09 ++
  sigma3_10 ++
  sigma3_11 ++
  sigma3_12 ++
  sigma3_13 ++
  sigma3_14

def sigma5 : List ℕ :=
  sigma5_00 ++
  sigma5_01 ++
  sigma5_02 ++
  sigma5_03 ++
  sigma5_04 ++
  sigma5_05 ++
  sigma5_06 ++
  sigma5_07 ++
  sigma5_08 ++
  sigma5_09 ++
  sigma5_10 ++
  sigma5_11 ++
  sigma5_12 ++
  sigma5_13 ++
  sigma5_14

private theorem factors_checked : check factors = true := by
  simp only [check_eq_zeroBlock, factors, checkBlock_append, List.length_append,
    rows00_length, rows01_length, rows02_length, rows03_length, rows04_length,
    rows05_length, rows06_length, rows07_length, rows08_length, rows09_length,
    rows10_length, rows11_length, rows12_length, rows13_length,
    Nat.reduceAdd, rows00_checked, rows01_checked, rows02_checked, rows03_checked, rows04_checked,
    rows05_checked, rows06_checked, rows07_checked, rows08_checked, rows09_checked,
    rows10_checked, rows11_checked, rows12_checked, rows13_checked, rows14_checked, Bool.and_true]

private theorem factors_length : factors.length = 6964 := by
  simp only [factors, List.length_append, rows00_length, rows01_length, rows02_length, rows03_length, rows04_length,
    rows05_length, rows06_length, rows07_length, rows08_length, rows09_length,
    rows10_length, rows11_length, rows12_length, rows13_length, rows14_length, Nat.reduceAdd]

private theorem sigma3_eq : sigma3 = coefficients 3 factors := by
  simp only [coefficients_eq_zeroBlock, sigma3, factors, coefficientsBlock_append,
    List.length_append,
    rows00_length, rows01_length, rows02_length, rows03_length, rows04_length,
    rows05_length, rows06_length, rows07_length, rows08_length, rows09_length,
    rows10_length, rows11_length, rows12_length, rows13_length, Nat.reduceAdd,
    sigma3_00_checked, sigma3_01_checked, sigma3_02_checked, sigma3_03_checked, sigma3_04_checked,
    sigma3_05_checked, sigma3_06_checked, sigma3_07_checked, sigma3_08_checked, sigma3_09_checked,
    sigma3_10_checked, sigma3_11_checked, sigma3_12_checked, sigma3_13_checked, sigma3_14_checked]

theorem sigma3_length : sigma3.length = 6964 := by
  rw [sigma3_eq, length_coefficients, factors_length]

theorem getD_sigma3 (i : ℕ) (hi : i < 6964) : sigma3.getD i 0 = ArithmeticFunction.sigma 3 i := by
  rw [sigma3_eq]
  exact getD_coefficients 3 factors_checked i (factors_length.symm ▸ hi)

private theorem sigma5_eq : sigma5 = coefficients 5 factors := by
  simp only [coefficients_eq_zeroBlock, sigma5, factors, coefficientsBlock_append,
    List.length_append,
    rows00_length, rows01_length, rows02_length, rows03_length, rows04_length,
    rows05_length, rows06_length, rows07_length, rows08_length, rows09_length,
    rows10_length, rows11_length, rows12_length, rows13_length, Nat.reduceAdd,
    sigma5_00_checked, sigma5_01_checked, sigma5_02_checked, sigma5_03_checked, sigma5_04_checked,
    sigma5_05_checked, sigma5_06_checked, sigma5_07_checked, sigma5_08_checked, sigma5_09_checked,
    sigma5_10_checked, sigma5_11_checked, sigma5_12_checked, sigma5_13_checked, sigma5_14_checked]

theorem sigma5_length : sigma5.length = 6964 := by
  rw [sigma5_eq, length_coefficients, factors_length]

theorem getD_sigma5 (i : ℕ) (hi : i < 6964) : sigma5.getD i 0 = ArithmeticFunction.sigma 5 i := by
  rw [sigma5_eq]
  exact getD_coefficients 5 factors_checked i (factors_length.symm ▸ hi)

end GRHArticle.SingularModuli.Prime59
