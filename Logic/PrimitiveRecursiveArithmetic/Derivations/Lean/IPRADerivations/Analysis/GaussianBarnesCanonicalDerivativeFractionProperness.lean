import IPRADerivations.Analysis.GaussianBarnesCanonicalDerivativeCofinal
import IPRADerivations.Analysis.GaussianBarnesCanonicalFiniteProperness
import IPRADerivations.Analysis.GaussianNameConjugation

/-!
# Fraction encodings of the original cofinal Barnes logarithmic derivative

The identical cutoff and clock for a certified disk give exact equality
of observations at the same precision, even when the Gaussian
numerators and denominators representing the input are different.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeFractionProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalDerivativeCofinal (nameF sample_at length)
open GaussianBarnesCanonicalDerivativeTail (body body_at value)
open GaussianBarnesCanonicalLogCofinal (data source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianNameConjugation (pointwiseEqual equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalReciprocal (reciprocal qone)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem row_equal (z w B D k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeRow.value z B k ≐ GaussianBarnesCanonicalDerivativeRow.value w D k := by
  have off := GaussianBarnesCanonicalFiniteProperness.scaled_fraction_equal z w B D k hB hD hk he
  have base : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.base z B k ≐ GaussianBarnesCanonicalFactor.base w D k :=
    qadd_congr (.eqRefl qone) off
  have inv : Γ ⊢[PRAAx] reciprocal (GaussianBarnesCanonicalFactor.base z B k) ≐
      reciprocal (GaussianBarnesCanonicalFactor.base w D k) := by
    ipra_congr (reciprocal (var 0) : PTm 1) with [base]
  exact qmul_congr (qmul_congr off off) inv

theorem finite_equal (z w B D N m : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] value z B N m ≐ value w D N m := by
  apply GaussianRationalFiniteSum.sum_congr_bounded body body m
    (GaussianBarnesCanonicalDerivativeTail.data z B N) (GaussianBarnesCanonicalDerivativeTail.data w D N)
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hB.shift.wk
  have hd : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hD.shift.wk
  have eq : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.wk
  have rows := row_equal (sh z) (sh w) (sh B) (sh D) (succ (sh N+i)) hb hd (zero_lt_succ _) eq
  simpa only [termsEqual,GaussianBarnesCanonicalDerivativeTail.subst_data,Syn.shift,sh,Δ,i] using
    (body_at (sh z) (sh B) (sh N) i).eqTrans (rows.eqTrans (body_at (sh w) (sh D) (sh N) i).eqSymm)

theorem same_precision (p z w R B D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B) ≐ ap2 nameF p (data w R D) :=
  (sample_at p z R B).eqTrans
    ((finite_equal z w B D (initial R) (length p R) hB hD he).eqTrans (sample_at p w R D).eqSymm)

theorem proper (z w R B D : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data z R B) (data w R D) := by
  apply equal_samples_cross nameF nameF _ _
    (GaussianBarnesCanonicalDerivativeCofinal.regular z R B hz) (GaussianBarnesCanonicalDerivativeCofinal.regular w R D hw)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [sh,Fm.shift,Syn.shift] using hz.andE₁.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [sh,Fm.shift,Syn.shift] using hw.andE₁.shift
  have eq : Γ.map Fm.shift ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [sh,Fm.shift,Syn.shift] using he.shift
  simpa only [pointwiseEqual,Syn.shift,sh,GaussianBarnesCanonicalLogCofinal.subst_data] using
    same_precision (var 0) (sh z) (sh w) (sh R) (sh B) (sh D) hb hd eq

theorem actual_Barnes_cofinal_slope_fraction_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     (source z R B ⋏ (source w R D ⋏ (ofGaussian z B ≐ ofGaussian w D))) ⟶
       crossEquivalent nameF nameF (data z R B) (data w R D)) :=
  closeUniv 5 (.impI (proper _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeFractionProperness
