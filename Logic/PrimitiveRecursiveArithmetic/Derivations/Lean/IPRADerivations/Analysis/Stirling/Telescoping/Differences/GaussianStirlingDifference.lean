import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithm
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# The logarithmic Stirling difference at a positive fraction

At x = A/B the original positive rational logarithm is sampled at
(A+B)/A. The named arithmetic calls compute
`(x + 1/2) * log(1 + 1/x) - 1`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDifference

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianPositiveRationalLogarithm (logF fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (A B : PTm n) : PTm n := fraction (two*A+B) (two*B)
def logData (A B : PTm n) : PTm n := GaussianPositiveRationalLogarithm.data (A+B) A
def minusOne : PTm n := GaussianRationalMatrixFiniteSums.minusOne
def productF : PR 2 := multiplyF constantF logF
def productData (A B : PTm n) : PTm n := multiplyData constantF logF (coefficient A B) (logData A B)
def nameF : PR 2 := addF productF constantF
def data (A B : PTm n) : PTm n := addData (productData A B) minusOne

ipra_subst coefficient
ipra_subst logData
ipra_subst productData
ipra_subst data [minusOne, GaussianRationalMatrixFiniteSums.minusOne]

theorem log_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] pointCN logF (logData A B) :=
  GaussianPositiveRationalLogarithm.name_regular (A+B) A (.andI (le_trans hA (le_add_right A B)) hA)

theorem product_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] pointCN productF (productData A B) :=
  multiply_fast constantF logF (coefficient A B) (logData A B) (constant_regular _) (log_regular A B hA)

theorem name_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (_hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  add_fast productF constantF (productData A B) minusOne (product_regular A B hA) (constant_regular _)

end LeanProofs.IPRA.Analysis.GaussianStirlingDifference
