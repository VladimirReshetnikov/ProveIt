import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalFiniteTaylorEvenGridComparison
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorGridUniformObservations

/-!
# Disk-uniform Taylor error on the actual opposite Barnes grids

Use the disk-uniform head and central scalar bounds for the analytic
part of each observed row. The combined normalized estimate retains
the full power of the displacement.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridUniformComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded bounded_neg)
open GaussianBarnesCanonicalFiniteTaylorEvenGridComparison (observed target errorDenominator compare_from_rows)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "rowNumerator" => GaussianBarnesCanonicalFiniteTaylorGridUniformObservations.numerator

def errorNumerator (t s p z h R B H r M e D : PTm n) : PTm n :=
  pw D e*(pw two e*(rowNumerator t s p z h R B H r M e+rowNumerator t s p z (ComplexLogarithmRemainder.neg h) R B H r M e))

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (t s p z h R B H r M e D : PTm n) :
    Syn.subst σ (errorNumerator t s p z h R B H r M e D) =
      errorNumerator (Syn.subst σ t) (Syn.subst σ s) (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ h)
        (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ r) (Syn.subst σ M) (Syn.subst σ e) (Syn.subst σ D) :=
  by simp [errorNumerator,pw,two,one]

theorem compare (t s p z h R B H r M e L D : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B)
    (he : Γ ⊢[PRAAx] previous M ≐ succ e) (hL : Γ ⊢[PRAAx] le one L) (hD : Γ ⊢[PRAAx] le one D)
    (hstep : Γ ⊢[PRAAx] lower (ofGaussian h B) L D) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B r e) (target s p z R B H r M e)
      (errorNumerator t s p z h R B H r M e D) (errorDenominator t s p R B M e L) :=
  compare_from_rows t s p z h R B H r M e L D _ _ hz.andE₁ he hL hD hstep
    (GaussianBarnesCanonicalFiniteTaylorGridUniformObservations.row_bound t s p z h R B H r M e hz hh hsmall)
    (GaussianBarnesCanonicalFiniteTaylorGridUniformObservations.row_bound t s p z (ComplexLogarithmRemainder.neg h) R B H r M e hz (bounded_neg hh) hsmall)

theorem actual_Barnes_finite_Taylor_even_grid_uniform_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (let t := var 0
     let s := var 1
     let p := var 2
     let z := var 3
     let h := var 4
     let R := var 5
     let B := var 6
     let H := var 7
     let r := var 8
     let M := var 9
     let e := var 10
     let L := var 11
     let D := var 12
     (source z R B ⋏ (bounded h H ⋏ (le ((e*stepDivisor R)*H) B ⋏ (previous M ≐ succ e ⋏
       (le one L ⋏ (le one D ⋏ lower (ofGaussian h B) L D)))))) ⟶
       distanceBounded (observed t z h R B r e) (target s p z R B H r M e)
         (errorNumerator t s p z h R B H r M e D) (errorDenominator t s p R B M e L)) :=
  closeUniv 13 (.impI (compare _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridUniformComparison
