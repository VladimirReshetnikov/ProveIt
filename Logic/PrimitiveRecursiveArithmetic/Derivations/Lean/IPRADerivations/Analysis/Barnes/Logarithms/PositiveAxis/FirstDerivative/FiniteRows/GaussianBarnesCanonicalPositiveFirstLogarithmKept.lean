import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.FiniteRows.GaussianBarnesCanonicalPositiveFirstDerivativeRow
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.Cofinal.GaussianBarnesCanonicalPositiveFirstLogarithm
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Gamma.Ratios.Wendel.GaussianGammaRationalWendelBoundary

/-!
# The actual kept logarithmic derivative and correction fold

On a certified positive chart, the original first rows in the kept
prefix are exactly the sum of the original base reciprocals and the
original correction slope. Both forms retain the same finite cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveFirstLogarithmKept

open_ipra
open GaussianBarnesCanonicalDerivativeRow (offset)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalHeadCorrectionDerivative (slope)
open GaussianBarnesCanonicalPositiveFirstDerivativeRow (fraction_identity)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (base_lower)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianGammaCanonicalExponent (harmonicPoint)
open GaussianGammaHarmonicIncrement (harmonic_point_increment reciprocalPoint)
open GaussianNameArithmetic (sum_difference)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalFiniteSum (add_shuffle)
open GaussianRationalHorner (ofGaussian qadd qmul qzero)
open GaussianRationalMetric (qsub qnegative qsub_canonical)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (reciprocal qone)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qmul_zero_right qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalDerivativeTail.value

def body : PTm 2 := reciprocal (base (fstT (var 1)) (sndT (var 1)) (succ (var 0)))

def value (z B N : PTm n) : PTm n := GaussianRationalFiniteSum.sum body N (pairT z B)

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (value z B N) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [value]

theorem body_at (z B i : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (pairT z B) ≐ reciprocal (base z B (succ i)) := by
  have e : Γ ⊢[PRAAx] reciprocal (base (fstT (pairT z B)) (sndT (pairT z B)) (succ i)) ≐
      reciprocal (base z B (succ i)) := by
    ipra_congr (reciprocal (base (var 0) (var 1) (var 2)) : PTm 3)
      with [fst_pair z B,snd_pair z B,.eqRefl _]
  simpa [body,inst2] using e

theorem value_succ (z B N : PTm n) :
    Γ ⊢[PRAAx] value z B (succ N) ≐ qadd (value z B N) (reciprocal (base z B (succ N))) :=
  (GaussianRationalFiniteSum.sum_succ body N _).eqTrans (qadd_congr (.eqRefl _) (body_at z B N))

private theorem slope_succ (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] slope z B (succ N) ≐ qadd (slope z B N) (qsub (offset z B (succ N)) qone) := by
  let a := ofGaussian z B
  let v := harmonicPoint N
  let w := reciprocalPoint N
  have one_value : Γ ⊢[PRAAx] naturalPoint (one : PTm n) ≐ qone :=
    GaussianRationalNaturalScale.natural_point_one
  have size : Γ ⊢[PRAAx] naturalPoint (succ N) ≐ qadd (naturalPoint N) qone :=
    (GaussianGammaRationalFractionalChord.natural_point_sum N one (succ N) (by ipra_ring)).eqSymm.eqTrans
      (qadd_congr (.eqRefl _) one_value)
  have unfold_sum : Γ ⊢[PRAAx] qmul a (harmonicPoint (succ N)) ≐ qadd (qmul a v) (qmul a w) :=
    (qmul_congr (.eqRefl _) (harmonic_point_increment N)).eqTrans (qmul_add a v w)
  have step := GaussianBarnesCanonicalSecondDerivativeStep.step_factor z B (succ N) hB (zero_lt_succ N)
  exact (qsub_congr unfold_sum size).eqTrans
    ((sum_difference (qmul a v) (naturalPoint N) (qmul a w) qone).eqTrans
      (qadd_congr (.eqRefl _) (qsub_congr step (.eqRefl _))))

def law (A B N : PTm n) : Fm PTm n :=
  V (center A B) B zero N ≐ qadd (value (center A B) B N) (slope (center A B) B N)

@[simp] theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (A B N : PTm n) :
    (law A B N).subst σ = law (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ N) := by simp [law]

private theorem law_zero (A B : PTm n) : Γ ⊢[PRAAx] law A B zero := by
  have first : Γ ⊢[PRAAx] V (center A B) B zero zero ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
  have second : Γ ⊢[PRAAx] value (center A B) B zero ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
  have offset : Γ ⊢[PRAAx] slope (center A B) B zero ≐ qzero :=
    (qsub_congr ((qmul_congr (.eqRefl _) GaussianGammaEulerHeadQuadratic.harmonic_zero).eqTrans (qmul_zero_right _))
      (GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one))).eqTrans
      (GaussianCoefficientNormOrder.qsub_self qzero)
  exact first.eqTrans
    (((qadd_congr second offset).eqTrans (qzero_add _ GaussianRationalSyntheticDivision.qzero_canonical)).eqSymm)

private theorem law_step (A B N K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K)
    (hA : Γ ⊢[PRAAx] le B (K*A)) (ih : Γ ⊢[PRAAx] law A B N) :
    Γ ⊢[PRAAx] law A B (succ N) := by
  let z := center A B
  let i := reciprocal (base z B (succ N))
  let o := offset z B (succ N)
  let x := GaussianBarnesCanonicalDerivativeTail.data z B zero
  have row_idx : Γ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeRow.value z B (succ (zero+N)) ≐
      GaussianBarnesCanonicalDerivativeRow.value z B (succ N) := by
    ipra_congr (GaussianBarnesCanonicalDerivativeRow.value (var 0) (var 1) (var 2) : PTm 3)
      with [.eqRefl _,.eqRefl _,congrSucc (zero_add N)]
  have e := (GaussianBarnesCanonicalDerivativeTail.body_at (Γ := Γ) z B zero N).eqTrans row_idx
  have read : Γ ⊢[PRAAx] inst2 GaussianBarnesCanonicalDerivativeTail.body N x ≐ qadd i (qsub o qone) :=
    e.eqTrans ((fraction_identity z B (succ N) K hB (zero_lt_succ N) hK (base_lower A B N K hB hK hA)).eqSymm.eqTrans
      (qadd_associative i o (qnegative qone)))
  exact (GaussianRationalFiniteSum.sum_succ GaussianBarnesCanonicalDerivativeTail.body N x).eqTrans
    ((qadd_congr ih read).eqTrans ((add_shuffle (value z B N) (slope z B N) i (qsub o qone)).eqTrans
      (qadd_congr (value_succ z B N).eqSymm (slope_succ z B N hB).eqSymm)))

theorem kept_fold (A B N K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K)
    (hA : Γ ⊢[PRAAx] le B (K*A)) :
    Γ ⊢[PRAAx] V (center A B) B zero N ≐ qadd (value (center A B) B N) (slope (center A B) B N) := by
  let sh (x : PTm n) := Syn.shift x
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,one] using hB.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] le one (sh K) := by simpa [Fm.shift,Syn.shift,sh,one] using hK.shift
  have ha : Γ.map Fm.shift ⊢[PRAAx] le (sh B) (sh K*sh A) := by simpa [Fm.shift,Syn.shift,sh] using hA.shift
  have all : Γ ⊢[PRAAx] .all (law (sh A) (sh B) (var 0)) := by
    refine PRA.qfInd _ (by simp [law,Fm.QF]) ?_ ?_
    · simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using law_zero A B
    · simpa only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh] using
        law_step (sh A) (sh B) (var 0) (sh K) hb.wk hk.wk ha.wk Prf.hyp0
  have e : Γ ⊢[PRAAx] law A B N := by
    simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE N
  exact e

theorem actual_Barnes_positive_kept_logarithm_first_derivative_fold_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let A := var 0
       let B := var 1
       let N := var 2
       let K := var 3
       (le one B ⋏ (le one K ⋏ le B (K*A))) ⟶ law A B N) :=
  closeUniv 4 (.impI (kept_fold _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveFirstLogarithmKept
