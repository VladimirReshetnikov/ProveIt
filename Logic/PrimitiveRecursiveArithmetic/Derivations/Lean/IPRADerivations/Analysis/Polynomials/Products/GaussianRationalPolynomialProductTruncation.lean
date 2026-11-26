import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialLowPrefix
import IPRADerivations.Analysis.Polynomials.Taylor.GaussianShrinkingPolynomialTail
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianFiniteExponentialWeightedNorm

/-!
# The stored low-degree prefix of the original Gaussian polynomial product

The stored result selects the original convolution coefficients
through the requested degree. The discarded part is bounded by the
product coefficient mass times the first omitted power of the input radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductTruncation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientL1 (coefficientNorm)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (evaluate qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialProduct (product product_length product_evaluation)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative natCode_multiply)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open RationalArgmin (rationalLE)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polynomial (P Q N M d : PTm n) : PTm n := GaussianPolynomialLowPrefix.polynomial (product P Q N M) (N+M) d

@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (P Q N M d : PTm n) :
    Syn.subst σ (polynomial P Q N M d) =
      polynomial (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ d) := by
  simp [polynomial]

theorem polynomial_length (P Q N M d : PTm n) : Γ ⊢[PRAAx] length (polynomial P Q N M d) ≐ succ d :=
  GaussianPolynomialLowPrefix.polynomial_length _ _ _

theorem coefficient (P Q N M d e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    entry (polynomial P Q N M d) (monus d e) ≐ entry (product P Q N M) (monus (N+M) e) :=
  GaussianPolynomialLowPrefix.original_reader _ _ _ _ he

theorem factor_mass (P Q N M A C : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) (hA : Γ ⊢[PRAAx] rationalLE (coefficientNorm P) (natCode A))
    (hC : Γ ⊢[PRAAx] rationalLE (coefficientNorm Q) (natCode C)) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (product P Q N M)) (natCode (A*C)) := by
  have q := GaussianCoefficientNormOrder.coefficient_numerator_nonnegative (Γ := Γ) Q
  have bound := GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ q (natCode_nonnegative A) hA hC
  exact RationalArgmin.transitive (GaussianRationalConvolutionNorm.product_norm P Q N M hP hQ)
    (RationalArgmin.rationalLE_congr (.eqRefl _) (natCode_multiply A C) bound)

theorem tail (P Q N M d w H B E : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) (hd : Γ ⊢[PRAAx] le d (N+M))
    (hB : Γ ⊢[PRAAx] le one B) (hHB : Γ ⊢[PRAAx] le H B) (hw : Γ ⊢[PRAAx] bounded w H B)
    (hMass : Γ ⊢[PRAAx] rationalLE (coefficientNorm (product P Q N M)) (fraction E one)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (evaluate P w) (evaluate Q w)) (evaluate (polynomial P Q N M d) w)
      (E*pw H (succ d)) (pw B (succ d)) := by
  let C := product P Q N M
  have finite := GaussianShrinkingPolynomialTail.finite_coefficient_tail C (N+M) d w E one H B
    (product_length P Q N M) hd (le_refl one) hB hHB hMass hw
  exact distance_congr (product_evaluation P Q N M w hP hQ)
    (GaussianPolynomialLowPrefix.original_evaluation C (N+M) d w hd).eqSymm (.eqRefl _) (one_mul _) finite

theorem tail_of_factor_masses (P Q N M d w H B A C : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) (hd : Γ ⊢[PRAAx] le d (N+M))
    (hB : Γ ⊢[PRAAx] le one B) (hHB : Γ ⊢[PRAAx] le H B) (hw : Γ ⊢[PRAAx] bounded w H B)
    (hA : Γ ⊢[PRAAx] rationalLE (coefficientNorm P) (natCode A))
    (hC : Γ ⊢[PRAAx] rationalLE (coefficientNorm Q) (natCode C)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (evaluate P w) (evaluate Q w)) (evaluate (polynomial P Q N M d) w)
      ((A*C)*pw H (succ d)) (pw B (succ d)) :=
  tail P Q N M d w H B (A*C) hP hQ hd hB hHB hw (factor_mass P Q N M A C hP hQ hA hC)

theorem actual_stored_Gaussian_product_truncation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let P := var 0
     let Q := var 1
     let N := var 2
     let M := var 3
     let d := var 4
     let w := var 5
     let H := var 6
     let B := var 7
     let A := var 8
     let C := var 9
     ((length P ≐ succ N) ⋏ ((length Q ≐ succ M) ⋏ (le d (N+M) ⋏ (le one B ⋏
       (le H B ⋏ (bounded w H B ⋏ (rationalLE (coefficientNorm P) (natCode A) ⋏
         rationalLE (coefficientNorm Q) (natCode C)))))))) ⟶
       distanceBounded (qmul (evaluate P w) (evaluate Q w)) (evaluate (polynomial P Q N M d) w)
         ((A*C)*pw H (succ d)) (pw B (succ d))) :=
  closeUniv 10 (.impI (tail_of_factor_masses _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductTruncation
