import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeCenteredMesh

/-!
# Affine averaging on the actual left unit grid

The constant part has the full unit weight, and the slope is
multiplied by the exact mean `-1/(2N)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeAffineMean

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRaabeCenteredMesh (centered centered_at centered_mean)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (canonical canonical_unique ofGaussian_canonical ofGaussian_represents qadd qmul)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalRiemannRefinement (constantBody leftSum weight)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qone qone_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N K C : PTm n) : PTm n := pairT K (pairT C N)

private def constantColumn : PTm 2 := fstT (var 1)
private def slopeColumn : PTm 2 :=
  qmul (fstT (sndT (var 1))) (centered (var 0) (sndT (sndT (var 1))))
def body : PTm 2 := qadd constantColumn slopeColumn

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N K C : PTm n) :
    Syn.subst σ (data N K C) = data (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ C) := by simp [data]

private theorem constant_at (i N K C : PTm n) :
    Γ ⊢[PRAAx] inst2 constantColumn i (data N K C) ≐ K := by
  simpa only [data,constantColumn,inst2,subst_fstT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    fst_pair (Γ := Γ) K (pairT C N)

private theorem slope_at (i N K C : PTm n) :
    Γ ⊢[PRAAx] inst2 slopeColumn i (data N K C) ≐ qmul C (centered i N) := by
  let x := data N K C
  have e : Γ ⊢[PRAAx] sndT x ≐ pairT C N := snd_pair _ _
  have c := (congrFst e).eqTrans (fst_pair C N)
  have d := (congrSnd e).eqTrans (snd_pair C N)
  have f : Γ ⊢[PRAAx] centered i (sndT (sndT x)) ≐ centered i N :=
    qsub_congr (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl i) d) (.eqRefl _)
  simp only [slopeColumn,inst2,GaussianRationalHorner.subst_qmul,subst_fstT,subst_sndT,
    GaussianRaabeCenteredMesh.subst_centered,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr c f

theorem row_at (i N K C : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data N K C) ≐ qadd K (qmul C (centered i N)) := by
  unfold body
  change Γ ⊢[PRAAx] Syn.subst ![i,data N K C] (qadd constantColumn slopeColumn) ≐ _
  rw [GaussianRationalHorner.subst_qadd]
  exact qadd_congr (constant_at i N K C) (slope_at i N K C)

private theorem sum_constant (N K C : PTm n) :
    Γ ⊢[PRAAx] sum constantColumn N (data N K C) ≐ sum constantBody N K := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simp only [Syn.shift,subst_data]
  exact constant_at _ _ _ _

private theorem sum_slope (N K C : PTm n) :
    Γ ⊢[PRAAx] sum slopeColumn N (data N K C) ≐ qmul C (sum GaussianRaabeCenteredMesh.body N N) := by
  let f := GaussianRaabeCenteredMesh.body
  have e : Γ ⊢[PRAAx] sum slopeColumn N (data N K C) ≐ sum (multiplyBody f) N (pairT C N) := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
    refine .allI (.impI ?_)
    simp only [Syn.shift,subst_data,subst_pairT]
    have read := multiply_body_at (Γ := lt (var 0) (Syn.shift N)::Γ.map Fm.shift)
      GaussianRaabeCenteredMesh.body (Syn.shift C) (var 0) (Syn.shift N)
    rw [centered_at] at read
    exact (slope_at _ _ _ _).eqTrans read.eqSymm
  exact e.eqTrans (sum_multiply f C N N)

theorem unit_mass (N D : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianRationalNaturalScale.natScale N (weight D D N) ≐ qone := by
  have e : Γ ⊢[PRAAx] fraction D D ≐ qone :=
    canonical_unique _ _ _ D (ofGaussian_canonical _ _ hD) qone_canonical hD (ofGaussian_represents _ _ hD)
      (GaussianRationalReciprocal.qone_represents_scaled D)
  exact (GaussianRationalParameterTelescope.whole_step (scale D oneCode) D N hD hN).eqTrans e

theorem affine_mean (N D K C : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D)
    (hK : Γ ⊢[PRAAx] canonical K) :
    Γ ⊢[PRAAx] leftSum body N (data N K C) D D ≐ qsub K (qmul (fraction one (two*N)) C) := by
  let w := weight D D N
  let x := data N K C
  let a := sum constantBody N K
  let b := sum GaussianRaabeCenteredMesh.body N N
  let v := fraction one (two*N)
  have e : Γ ⊢[PRAAx] sum body N x ≐ qadd a (qmul C b) :=
    (GaussianRationalFiniteSum.sum_add constantColumn slopeColumn N x).eqTrans
      (qadd_congr (sum_constant N K C) (sum_slope N K C))
  have const : Γ ⊢[PRAAx] qmul w a ≐ K :=
    (GaussianRationalParameterTelescope.constant_slope_product N w K).eqTrans
      ((qmul_congr (unit_mass N D hN hD) (.eqRefl K)).eqTrans
        ((qmul_commutative qone K).eqTrans (qmul_one_right K hK)))
  have commute : Γ ⊢[PRAAx] qmul w (qmul C b) ≐ qmul C (qmul w b) :=
    (qmul_associative w C b).eqSymm.eqTrans
      ((qmul_congr (qmul_commutative w C) (.eqRefl b)).eqTrans (qmul_associative C w b))
  have slope : Γ ⊢[PRAAx] qmul w (qmul C b) ≐ qnegative (qmul v C) :=
    commute.eqTrans ((qmul_congr (.eqRefl C) (centered_mean N D hN hD)).eqTrans
      ((GaussianRationalFiberRightInverse.multiply_negative_right C v).eqTrans
        (GaussianInverseBinomialRows.negative_congr (qmul_commutative C v))))
  exact (qmul_congr (.eqRefl w) e).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add w a (qmul C b)).eqTrans (qadd_congr const slope))

theorem actual_affine_left_unit_quadrature_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let N := var 0
       let D := var 1
       let K := var 2
       let C := var 3
       (le one N ⋏ (le one D ⋏ canonical K)) ⟶
         leftSum body N (data N K C) D D ≐ qsub K (qmul (fraction one (two*N)) C)) :=
  closeUniv 4 (.impI (affine_mean _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeAffineMean
