import IPRADerivations.Analysis.Exponential.Polynomials.Recomposition.GaussianRationalPolynomialExponentialRecomposition
import IPRADerivations.Analysis.Polynomials.Products.Convolution.GaussianPolynomialLowPrefixMass
import IPRADerivations.Analysis.Polynomials.Products.Convolution.GaussianRationalPolynomialProductTruncation

/-!
# Stored product with the exponential recomposition polynomial

The retained product coefficients come from the original finite convolution.
An input coefficient mass of at most L bounds the exponential prefix by
3^L uniformly in the finite exponential cutoff. This controls the discarded
product at order m + 1 on the original shrinking disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialProductTruncation

open_ipra
open GaussianCoefficientL1 (coefficientNorm)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (evaluate qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticBounds (natCode)
open GaussianRationalSyntheticDivision (canonicalCoefficients qmul_congr qone)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentialPrefix (C N K m : PTm n) : PTm n :=
  GaussianPolynomialLowPrefix.polynomial (GaussianRationalPolynomialExponential.polynomial C N K) (K*N) m

def polynomial (P C r N m : PTm n) : PTm n :=
  GaussianRationalPolynomialProductTruncation.polynomial P (exponentialPrefix C N m m) r m m

@[simp] theorem subst_exponentialPrefix {l : ℕ} (σ : Fin n → PTm l) (C N K m : PTm n) :
    Syn.subst σ (exponentialPrefix C N K m) =
      exponentialPrefix (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ m) := by
  simp [exponentialPrefix]

@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (P C r N m : PTm n) :
    Syn.subst σ (polynomial P C r N m) =
      polynomial (Syn.subst σ P) (Syn.subst σ C) (Syn.subst σ r) (Syn.subst σ N) (Syn.subst σ m) := by
  simp [polynomial]

theorem exponential_prefix_length (C N K m : PTm n) : Γ ⊢[PRAAx] length (exponentialPrefix C N K m) ≐ succ m :=
  GaussianPolynomialLowPrefix.polynomial_length _ _ _

theorem exponential_prefix_evaluation (C N m w : PTm n) (hm : Γ ⊢[PRAAx] le m (m*N)) : Γ ⊢[PRAAx]
    evaluate (exponentialPrefix C N m m) w ≐ GaussianRationalPolynomialExponentialRecomposition.value C N m w :=
  GaussianPolynomialLowPrefix.original_evaluation _ _ _ _ hm

theorem exponential_prefix_mass (C N K m L : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hCan : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hm : Γ ⊢[PRAAx] le m (K*N)) (hL : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (natCode L)) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (exponentialPrefix C N K m)) (natCode (pw (num 3) L)) := by
  let E := GaussianRationalPolynomialExponential.polynomial C N K
  have hE : Γ ⊢[PRAAx] length E ≐ succ (K*N) :=
    GaussianRationalPolynomialExponential.polynomial_length C N K
  have inputNorm := GaussianGammaInputStaticNorm.unit_weighted_norm C N hC hCan
  have outputNorm := GaussianGammaInputStaticNorm.unit_weighted_norm E (K*N) hE
    (GaussianRationalPolynomialExponential.polynomial_canonical C N K)
  have majorant := GaussianFiniteExponentialCoefficientMajorant.polynomial_numerical_majorant C N K qone L hC
    (rationalLE_congr inputNorm.eqSymm (.eqRefl _) hL)
  exact RationalArgmin.transitive (GaussianPolynomialLowPrefixMass.low_prefix_mass E (K*N) m hE hm)
    (rationalLE_congr outputNorm (.eqRefl _) majorant)

theorem polynomial_length (P C r N m : PTm n) : Γ ⊢[PRAAx] length (polynomial P C r N m) ≐ succ m :=
  GaussianRationalPolynomialProductTruncation.polynomial_length _ _ _ _ _

theorem polynomial_canonical (P C r N m : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (polynomial P C r N m) :=
  GaussianPolynomialLowPrefixMass.low_prefix_canonical _ _ _
    (GaussianRationalPolynomialProduct.product_length P (exponentialPrefix C N m m) r m)
    (GaussianRationalPolynomialProduct.product_canonical P (exponentialPrefix C N m m) r m)

theorem coefficient (P C r N m e : PTm n) (he : Γ ⊢[PRAAx] le e m) : Γ ⊢[PRAAx]
    entry (polynomial P C r N m) (monus m e) ≐
      entry (GaussianRationalPolynomialProduct.product P (exponentialPrefix C N m m) r m) (monus (r+m) e) :=
  GaussianRationalPolynomialProductTruncation.coefficient _ _ _ _ _ _ he

theorem tail (P C r N m w H B A L : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ r) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hm : Γ ⊢[PRAAx] le m (m*N))
    (hB : Γ ⊢[PRAAx] le one B) (hHB : Γ ⊢[PRAAx] le H B) (hw : Γ ⊢[PRAAx] bounded w H B)
    (hA : Γ ⊢[PRAAx] rationalLE (coefficientNorm P) (natCode A))
    (hL : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (natCode L)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (evaluate P w) (GaussianRationalPolynomialExponentialRecomposition.value C N m w))
      (evaluate (polynomial P C r N m) w) ((A*pw (num 3) L)*pw H (succ m)) (pw B (succ m)) := by
  have bound := GaussianRationalPolynomialProductTruncation.tail_of_factor_masses P (exponentialPrefix C N m m)
    r m m w H B A (pw (num 3) L) hP (exponential_prefix_length C N m m)
    (le_add_left m r) hB hHB hw hA (exponential_prefix_mass C N m m L hC hCan hm hL)
  exact distance_congr (qmul_congr (.eqRefl _) (exponential_prefix_evaluation C N m w hm))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) bound

theorem actual_exponential_recomposition_product_truncation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let P := var 0
     let C := var 1
     let r := var 2
     let N := var 3
     let m := var 4
     let w := var 5
     let H := var 6
     let B := var 7
     let A := var 8
     let L := var 9
     ((length P ≐ succ r) ⋏ ((length C ≐ succ N) ⋏ (canonicalCoefficients C ⋏ (le m (m*N) ⋏
       (le one B ⋏ (le H B ⋏ (bounded w H B ⋏ (rationalLE (coefficientNorm P) (natCode A) ⋏
       rationalLE (coefficientNorm C) (natCode L))))))))) ⟶
       distanceBounded (qmul (evaluate P w) (GaussianRationalPolynomialExponentialRecomposition.value C N m w))
         (evaluate (polynomial P C r N m) w) ((A*pw (num 3) L)*pw H (succ m)) (pw B (succ m))) :=
  closeUniv 10 (.impI (tail _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialProductTruncation
