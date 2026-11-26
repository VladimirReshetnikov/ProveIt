import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGaussEulerFiniteIdentity
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationNormalization
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationQuotient

/-!
# Gauss multiplication for the original Gamma name

At every positive internal order m, and under the original rational
bounds and pole separation for mz, the shifted Gamma product divided
by Gamma(mz) agrees with m^(1−mz) times the reference Gamma product.

The reference product is the certified positive square root of the
independently named value (2π)^(m−1)/m. Its substitution gives the
normalized multiplication formula with the original Gamma and power
programs.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplication

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaGaussShiftedProduct (source)
open GaussianGaussEulerFiniteIdentity (cleared_Gauss_multiplication)
open GaussianGaussMultiplicationCofinalProducts (leftF leftData)
open GaussianGaussMultiplicationNormalization (normalize_Gauss normalizedF normalizedData)
open GaussianGaussMultiplicationQuotient
  (leftQuotientF rightQuotientF leftQuotientData rightQuotientData quotient_from_cleared)
open GaussianNameEquivalence (crossEquivalent)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (pred)
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem divided_multiplication (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] crossEquivalent leftQuotientF rightQuotientF
      (leftQuotientData z R B m d) (rightQuotientData z R B m) :=
  quotient_from_cleared z R B m a d hs (cleared_Gauss_multiplication z R B m a d hs)

def normalizedAt (z R B m d : PTm n) : PTm n := normalizedData z R B (pred m) d zero

theorem normalized_multiplication (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] crossEquivalent leftF normalizedF (leftData z R B m d) (normalizedAt z R B m d) := by
  let M := succ (pred m)
  have e : Γ ⊢[PRAAx] m ≐ M := by
    refine .orE (zero_or_succ m) ?_ Prf.hyp0
    exact lt_zero_absurd _ (le_congr (.eqRefl _) Prf.hyp0 hs.andE₁.andE₁.wk)
  have last (t : PTm n) : (![z,R,B,t,a,d] : Fin 6 → PTm n) 5 = d := rfl
  have hf : Γ ⊢[PRAAx] source z R B M a d := by
    simpa only [GaussianGammaGaussShiftedProduct.subst_source,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,last] using
      Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : Fm PTm 6)
        ![z,R,B,m,a,d] ![z,R,B,M,a,d] (fun i => by
          fin_cases i
          · exact .eqRefl _
          · exact .eqRefl _
          · exact .eqRefl _
          · exact e
          · exact .eqRefl _
          · exact .eqRefl _) (by simpa using hs)
  have hdata : Γ ⊢[PRAAx] leftData z R B M d ≐ leftData z R B m d := by
    simpa only [GaussianGaussMultiplicationCofinalProducts.subst_leftData,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (leftData (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![z,R,B,M,d]) (σ' := ![z,R,B,m,d]) (fun i => by
          fin_cases i
          · exact .eqRefl _
          · exact .eqRefl _
          · exact .eqRefl _
          · exact e.eqSymm
          · exact .eqRefl _)
  exact cross_data_congr leftF normalizedF _ _ _ _ hdata (.eqRefl _)
    (normalize_Gauss z R B (pred m) a d zero hf (cleared_Gauss_multiplication z R B M a d hf))

theorem actual_divided_Gauss_multiplication_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent leftQuotientF rightQuotientF (leftQuotientData (var 0) (var 1) (var 2) (var 3) (var 5))
        (rightQuotientData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 6 (.impI (divided_multiplication _ _ _ _ _ _ Prf.hyp0))

theorem actual_normalized_Gauss_multiplication_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent leftF normalizedF (leftData (var 0) (var 1) (var 2) (var 3) (var 5))
        (normalizedAt (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (normalized_multiplication _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplication
