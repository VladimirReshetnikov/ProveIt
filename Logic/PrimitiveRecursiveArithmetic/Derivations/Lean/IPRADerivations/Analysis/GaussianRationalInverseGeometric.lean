import IPRADerivations.Analysis.GaussianRationalQuadratureDifference
import IPRADerivations.Analysis.GaussianReconstructionRoots

/-!
# Exact finite geometric cancellation for a rational inverse pair

The actual positive-index finite power sum times `x−1` equals
`1−y^N` whenever `x*y=1`. The identity includes the empty sum and
uses the ordinary rational encodings and quantifier-free induction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalInverseGeometric

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalMetric (qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (power power_succ power_zero power_canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def body : PTm 2 := power (var 1) (succ (var 0))

def value (N y : PTm n) : PTm n := GaussianRationalFiniteSum.sum body N y

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (N y : PTm n) :
    Syn.subst σ (value N y) = value (Syn.subst σ N) (Syn.subst σ y) := by simp [value]

theorem row (x y k : PTm n) (h : Γ ⊢[PRAAx] qmul x y ≐ qone) :
    Γ ⊢[PRAAx] qmul (qsub x qone) (power y (succ k)) ≐ qsub (power y k) (power y (succ k)) := by
  let r := power y k
  let s := power y (succ k)
  have c : Γ ⊢[PRAAx] qmul x s ≐ r :=
    (qmul_commutative x s).eqTrans ((qmul_congr (power_succ y k) (.eqRefl x)).eqTrans
      ((qmul_associative r y x).eqTrans
        ((qmul_congr (.eqRefl r) ((qmul_commutative y x).eqTrans h)).eqTrans
          (qmul_one_right r (power_canonical y k)))))
  exact (qmul_commutative (qsub x qone) s).eqTrans
    ((GaussianRationalRoundedPower.multiplication_difference s x qone).eqSymm.eqTrans
      (qsub_congr ((qmul_commutative s x).eqTrans c) (qmul_one_right s (power_canonical y (succ k)))))

def law (x y N : PTm n) : Fm PTm n :=
  qmul (qsub x qone) (value N y) ≐ qsub qone (power y N)

@[simp] theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (x y N : PTm n) :
    (law x y N).subst σ = law (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ N) := by simp [law]

private theorem zero_case (x y : PTm n) : Γ ⊢[PRAAx] law x y zero := by
  have l : Γ ⊢[PRAAx] qmul (qsub x qone) (value zero y) ≐ qzero :=
    (qmul_congr (.eqRefl (qsub x qone)) (GaussianRationalFiniteSum.sum_zero body y)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_right (qsub x qone))
  have r : Γ ⊢[PRAAx] qsub qone (power y zero) ≐ qzero :=
    (qsub_congr (.eqRefl qone) (power_zero y)).eqTrans (GaussianCoefficientNormOrder.qsub_self qone)
  exact l.eqTrans r.eqSymm

private theorem step (x y k : PTm n) (h : Γ ⊢[PRAAx] qmul x y ≐ qone)
    (ih : Γ ⊢[PRAAx] law x y k) : Γ ⊢[PRAAx] law x y (succ k) := by
  have read : inst2 body k y = power y (succ k) := by
    simp only [body, inst2, GaussianRationalReciprocal.subst_power, Syn.subst_var,
      ConciseIPRA.PTm.subst_succ, Matrix.cons_val_zero, Matrix.cons_val_one]
  have e : Γ ⊢[PRAAx] value (succ k) y ≐ qadd (value k y) (power y (succ k)) := by
    simpa only [value, read] using GaussianRationalFiniteSum.sum_succ (Γ := Γ) body k y
  exact (qmul_congr (.eqRefl _) e).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add (qsub x qone) (value k y) (power y (succ k))).eqTrans
      ((qadd_congr ih (row x y k h)).eqTrans (GaussianReconstructionRoots.difference_chain _ _ _)))

theorem finite (x y N : PTm n) (h : Γ ⊢[PRAAx] qmul x y ≐ qone) : Γ ⊢[PRAAx] law x y N := by
  have all : Γ ⊢[PRAAx] .all (law (Syn.shift x) (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_law,Syn.inst_zero,Syn.subst_var,Syn.subst_inst_shift] using zero_case x y
    · have hs : Γ.map Fm.shift ⊢[PRAAx] qmul (Syn.shift x) (Syn.shift y) ≐ qone := by
        simpa [Fm.shift,Syn.shift] using h.shift
      simp only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact step _ _ _ hs.wk Prf.hyp0
  simpa only [subst_law,Syn.inst_zero,Syn.subst_var,Syn.subst_inst_shift] using all.allE N

theorem actual_exact_inverse_geometric_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((qmul (var 0) (var 1) ≐ qone) ⟶ law (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (finite _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalInverseGeometric
