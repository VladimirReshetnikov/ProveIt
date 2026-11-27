import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.FiniteProducts.GaussianBarnesCanonicalPolynomialShift
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductAlgebra

/-!
# Cleared shift of the actual Barnes base-power product

The rational factors in the literal head are the powers of `(1+z/k)`.
Their common inverse-integer product factors out at both arguments.
The cleared shift uses the finite polynomial identity without dividing
by a base, even when one of the translated powers vanishes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalBaseProductShift

open_ipra
open GaussianBarnesCanonicalDeflatedFactor (translatedValue inversePower power_factor)
open GaussianBarnesCanonicalFactor (powerValue)
open GaussianBarnesCanonicalPolynomialShift (polynomial plain polynomial_shift)
open GaussianBarnesWeightedProductShift (weighted)
open GaussianGammaEulerHeadLower (translated)
open GaussianRationalFiniteProduct (qprod product_congr_bounded)
open GaussianRationalHorner (qmul)
open GaussianRationalProductAlgebra (multiplyBody multiply_body_at product_multiply)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "pointData" => GaussianBarnesCanonicalPolynomialShift.data
local notation "polyBody" => weighted GaussianBarnesCanonicalPolynomialShift.rowF

def powerBody : PTm 2 := powerValue (fstT (var 1)) (sndT (var 1)) (succ (var 0))
def powerProduct (z B N : PTm n) : PTm n := qprod powerBody N (pointData z B)
def terminal (z B N : PTm n) : PTm n := power (translatedValue z B (succ N)) N

private def inverseBody : PTm 2 := inversePower (succ (var 0))
private def inverseProduct (N : PTm n) : PTm n := qprod inverseBody N zero

@[simp] theorem subst_powerProduct {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (powerProduct z B N) = powerProduct (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [powerProduct]

theorem power_at (i z B : PTm n) : Γ ⊢[PRAAx] inst2 powerBody i (pointData z B) ≐ powerValue z B (succ i) := by
  change Γ ⊢[PRAAx] inst2 powerBody i (pairT z B) ≐ powerValue z B (succ i)
  simp only [powerBody,inst2,GaussianBarnesCanonicalFactor.subst_powerValue,subst_fstT,subst_sndT,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val]
  ipra_congr (powerValue (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair z B, snd_pair z B, .eqRefl (succ i)]

private theorem inverse_at (i x : PTm n) : inst2 inverseBody i x = inversePower (succ i) := by
  simp [inst2,inverseBody]

private theorem polynomial_at (i z B : PTm n) : Γ ⊢[PRAAx]
    inst2 polyBody i (pointData z B) ≐ GaussianBarnesCanonicalDeflatedFactor.translatedPower z B (succ i) := by
  simpa [weighted,inst2,GaussianBarnesCanonicalDeflatedFactor.translatedPower,power] using
    congrAp2 powerF (.eqRefl (succ i)) (GaussianBarnesCanonicalPolynomialShift.row_at (Γ := Γ) z B i)

private theorem factorized (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    powerProduct z B N ≐ qmul (polynomial z B N) (inverseProduct N) := by
  let x := pointData z B
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual powerBody (multiplyBody polyBody inverseBody) N x x := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let Z := Syn.shift z
    let D := Syn.shift B
    let i : PTm (n+1) := var 0
    have h : Δ ⊢[PRAAx] le one D := by simpa [Fm.shift,Syn.shift,one,Δ,D] using hB.shift.wk
    have e := (power_at (Γ := Δ) i Z D).eqTrans (power_factor Z D (succ i) h (zero_lt_succ i))
    rw [multiply_body_at,inverse_at]
    simpa only [Syn.shift,GaussianBarnesCanonicalPolynomialShift.subst_data,x,Δ,Z,D,i] using
      e.eqTrans (qmul_congr (polynomial_at i Z D).eqSymm (.eqRefl _))
  have common : Γ ⊢[PRAAx] qprod inverseBody N x ≐ inverseProduct N := by
    apply product_congr_bounded
    refine .allI (.impI ?_)
    simp only [inverse_at]
    exact .eqRefl _
  exact (product_congr_bounded powerBody (multiplyBody polyBody inverseBody) N x x rows).eqTrans
    ((product_multiply polyBody inverseBody N x).eqTrans (qmul_congr (.eqRefl _) common))

theorem power_shift (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (powerProduct (translated z B one) B N) (plain z B N) ≐
      qmul (powerProduct z B N) (terminal z B N) := by
  let z' := translated z B one
  let I := inverseProduct N
  let P := polynomial z B N
  let Q := polynomial z' B N
  let A := plain z B N
  let T := terminal z B N
  have left : Γ ⊢[PRAAx] qmul (powerProduct z' B N) A ≐ qmul (qmul Q A) I :=
    (qmul_congr (factorized z' B N hB) (.eqRefl A)).eqTrans (GaussianRationalPowerAlgebra.swap_last Q I A)
  have right : Γ ⊢[PRAAx] qmul (powerProduct z B N) T ≐ qmul (qmul P T) I :=
    (qmul_congr (factorized z B N hB) (.eqRefl T)).eqTrans (GaussianRationalPowerAlgebra.swap_last P I T)
  exact left.eqTrans ((qmul_congr (polynomial_shift z B N hB) (.eqRefl I)).eqTrans right.eqSymm)

theorem actual_Barnes_base_power_product_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let z := var 0
     let B := var 1
     let N := var 2
     le one B ⟶ qmul (powerProduct (translated z B one) B N) (plain z B N) ≐
       qmul (powerProduct z B N) (terminal z B N)) :=
  closeUniv 3 (.impI (power_shift _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalBaseProductShift
