import IPRADerivations.Analysis.GaussianRaabeLogPrimitiveGrid

/-!
# The Raabe quadrature error under integer translation

Keep the original compact meshes and logarithm clocks fixed. Subtract
the finite logarithm primitive from each log-Gamma quadrature. The
result changes by at most the summed recurrence and primitive errors
under any finite number of unit translations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeUnitGridShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature)
open GaussianRaabeLogPrimitiveCell (primitive)
open GaussianRaabeUnitGridRecurrence (logGammaEvaluator logEvaluator quadrature_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalParameterTelescope (forward forward_sum)
open GaussianRationalRiemannRefinement (termsDistance)
open GaussianRationalSyntheticDivision (qsub_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def deviation (p N A D : PTm n) : PTm n :=
  qsub (quadrature logGammaEvaluator p N A D D zero) (primitive p (A*N) (D*N))

def numerator (p N A D J : PTm n) : PTm n :=
  let R := A+J*D
  num 8*(D*(A*A)*N)+two*R*(D*D)*unit p+two*R*(A*A)*(N*N)
def denominator (p N A D : PTm n) : PTm n := D*(A*A)*N*unit p

@[simp] theorem subst_deviation {m : ℕ} (σ : Fin n → PTm m) (p N A D : PTm n) :
    Syn.subst σ (deviation p N A D) = deviation (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [deviation]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p N A D J : PTm n) :
    Syn.subst σ (numerator p N A D J) =
      numerator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ J) := by
  simp [numerator,two]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p N A D : PTm n) :
    Syn.subst σ (denominator p N A D) = denominator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [denominator]

theorem deviation_congr (p p' N N' A A' D D' : PTm n)
    (hp : Γ ⊢[PRAAx] p ≐ p') (hN : Γ ⊢[PRAAx] N ≐ N') (hA : Γ ⊢[PRAAx] A ≐ A')
    (hD : Γ ⊢[PRAAx] D ≐ D') :
    Γ ⊢[PRAAx] deviation p N A D ≐ deviation p' N' A' D' := by
  simpa only [subst_deviation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (deviation (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![p,N,A,D]) (σ' := ![p',N',A',D']) (fun k => by
        fin_cases k
        · exact hp
        · exact hN
        · exact hA
        · exact hD)

private def shiftData (p N A D : PTm n) : PTm n := pairT p (pairT N (pairT A D))

private def shiftBody : PTm 2 :=
  let d := sndT (sndT (var 1))
  deviation (fstT (var 1)) (fstT (sndT (var 1))) (fstT d+var 0*sndT d) (sndT d)

private theorem shift_at (j p N A D : PTm n) :
    Γ ⊢[PRAAx] inst2 shiftBody j (shiftData p N A D) ≐ deviation p N (A+j*D) D := by
  let x := shiftData p N A D
  let y := pairT N (pairT A D)
  let z := sndT (sndT x)
  have e : Γ ⊢[PRAAx] sndT x ≐ y := snd_pair p y
  have f := (congrSnd e).eqTrans (snd_pair N (pairT A D))
  have ea := (congrFst f).eqTrans (fst_pair A D)
  have ed := (congrSnd f).eqTrans (snd_pair A D)
  simp only [shiftBody,inst2,subst_deviation,subst_fstT,subst_sndT,PTm.subst_add,PTm.subst_mul,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact deviation_congr _ _ _ _ _ _ _ _ (fst_pair p y)
    ((congrFst e).eqTrans (fst_pair N (pairT A D))) (congrAdd ea (congrMul (.eqRefl j) ed)) ed

private theorem denominator_positive (p N A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (denominator p N A D) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ hD (positive_product _ _ hA hA)) hN) (unit_positive p)

theorem step_error (p N A D j J : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hj : Γ ⊢[PRAAx] lt j J) :
    Γ ⊢[PRAAx] distanceBounded (deviation p N (A+succ j*D) D) (deviation p N (A+j*D) D)
      (numerator p N A D J) (denominator p N A D) := by
  let a := A+j*D
  let R := A+J*D
  let U := unit p
  let W := denominator p N A D
  let W' := GaussianRaabeLogPrimitiveGrid.denominator p N a D
  let P := two*R*(D*D)*U+two*R*(A*A)*(N*N)
  let Q := num 8*(D*(A*A)*N)
  let L := quadrature logEvaluator p N a D D zero
  let x := quadrature logGammaEvaluator p N (a+D) D D zero
  let y := quadrature logGammaEvaluator p N a D D zero
  let f := primitive p ((a+D)*N) (D*N)
  let g := primitive p (a*N) (D*N)
  have lower : Γ ⊢[PRAAx] le A a := le_add_right _ _
  have cap : Γ ⊢[PRAAx] le (succ j*D+A) (J*D+A) := add_le_add_right A (mul_le_mul_right D hj)
  have upper : Γ ⊢[PRAAx] le (a+D) R :=
    le_congr (by dsimp only [a]; ipra_ring) (add_comm (J*D) A) cap
  have lowerSq := le_mul_mono lower lower
  have ha := le_trans hA lower
  have hw := denominator_positive p N A D hN hA hD
  have hw' := denominator_positive p N a D hN ha hD
  have prim : Γ ⊢[PRAAx] distanceBounded (qsub f g) L P W :=
    distance_radius_mono _ _ _ _ _ _ hw' hw (by
      dsimp only [GaussianRaabeLogPrimitiveGrid.numerator,GaussianRaabeLogPrimitiveGrid.denominator,
        W,W',P,denominator]
      ipra_le 2*𝔞(R)*𝔞(D)^3*𝔞(N)*𝔞(U)^2*sl lowerSq +
        2*𝔞(D)^3*𝔞(A)^2*𝔞(N)*𝔞(U)^2*sl upper +
        2*𝔞(D)*𝔞(A)^2*𝔞(a)^2*𝔞(N)^3*𝔞(U)*sl upper)
      (GaussianRaabeLogPrimitiveGrid.finite_grid p N a D D ha hD hN)
  have step : Γ ⊢[PRAAx] distanceBounded (qsub x y) L Q W :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive p) hw
      (le_of_eq_add (d := zero) (by dsimp only [Q,W,denominator]; ipra_ring))
      (quadrature_error p N a D hN ha hD)
  have raw := distance_triangle_same (qsub x y) L (qsub f g) Q P W hw step
    (distance_symmetric _ _ _ _ hw prim)
  have moved : Γ ⊢[PRAAx] distanceBounded (deviation p N (a+D) D) (deviation p N a D) (numerator p N A D J) W :=
    GaussianRationalReciprocal.bound_congr (GaussianNamedDifferenceAlgebra.rational_shuffle x f y g).eqSymm
      (by dsimp only [numerator,Q,P,R,U]; ipra_ring) (.eqRefl _) raw
  have next : Γ ⊢[PRAAx] A+succ j*D ≐ a+D := by dsimp only [a]; ipra_ring
  exact distance_congr (deviation_congr _ _ _ _ _ _ _ _ (.eqRefl p) (.eqRefl N) next.eqSymm (.eqRefl D))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) moved

theorem shift_error (p N A D J : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded (deviation p N (A+J*D) D) (deviation p N A D)
      (J*numerator p N A D J) (denominator p N A D) := by
  let x := shiftData p N A D
  let B := numerator p N A D J
  let W := denominator p N A D
  have hw := denominator_positive p N A D hN hA hD
  have rows : Γ ⊢[PRAAx] termsDistance (forward shiftBody) GaussianRationalRiemannRefinement.constantBody J x qzero B W := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s J)::Γ.map Fm.shift
    have sn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have sa : Δ ⊢[PRAAx] le one (s A) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hA.shift.wk
    have sd : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hD.shift.wk
    have hws := denominator_positive (s p) (s N) (s A) (s D) sn sa sd
    let i : PTm (n+1) := var 0
    let l := deviation (s p) (s N) (s A+succ i*s D) (s D)
    let r := deviation (s p) (s N) (s A+i*s D) (s D)
    have cell : Δ ⊢[PRAAx] distanceBounded (qsub l r) qzero (numerator (s p) (s N) (s A) (s D) (s J))
        (denominator (s p) (s N) (s A) (s D)) :=
      (GaussianReconstructionRoots.distance_zero_iff _ _ _ hws).iffMpr
        (step_error (s p) (s N) (s A) (s D) i (s J) sn sa sd Prf.hyp0)
    have hf := qsub_congr (shift_at (Γ := Δ) (succ i) (s p) (s N) (s A) (s D))
      (shift_at i (s p) (s N) (s A) (s D))
    have row : Δ ⊢[PRAAx] distanceBounded (inst2 (forward shiftBody) i (shiftData (s p) (s N) (s A) (s D)))
        (inst2 GaussianRationalRiemannRefinement.constantBody i qzero) (numerator (s p) (s N) (s A) (s D) (s J))
        (denominator (s p) (s N) (s A) (s D)) := by
      rw [GaussianRationalParameterTelescope.forward_at]
      exact distance_congr hf.eqSymm (.eqRefl qzero) (.eqRefl _) (.eqRefl _) cell
    simpa only [B,W,x,s,Δ,i,shiftData,Syn.shift,subst_pairT,subst_numerator,subst_denominator,
      GaussianRationalHorner.subst_qzero] using row
  have raw := GaussianRationalRiemannRefinement.sum_distance _ _ J x qzero B W hw rows
  have z : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum GaussianRationalRiemannRefinement.constantBody J qzero ≐ qzero := by
    have rawZero := GaussianRationalRiemannRefinement.constant_sum (Γ := Γ) qzero J
    have ez := GaussianRationalNaturalScale.natScale_product (Γ := Γ) J qzero qzero
    exact rawZero.eqTrans ((GaussianRationalNaturalScale.natScale_congr (.eqRefl J)
      (GaussianRationalSyntheticDivision.qmul_zero_left qzero).eqSymm).eqTrans
      (ez.eqSymm.eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)))
  have e₀ := (shift_at (Γ := Γ) zero p N A D).eqTrans
    (deviation_congr _ _ _ _ _ _ _ _ (.eqRefl p) (.eqRefl N) (by ipra_ring) (.eqRefl D))
  have eJ := shift_at (Γ := Γ) J p N A D
  have e := (forward_sum shiftBody J x).eqTrans (qsub_congr eJ e₀)
  have finite := distance_congr e z (.eqRefl _) (.eqRefl _) raw
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hw).iffMp finite

theorem actual_real_log_Gamma_unit_quadrature_shift_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let p := var 0
       let N := var 1
       let A := var 2
       let D := var 3
       let J := var 4
       (le one N ⋏ (le one A ⋏ le one D)) ⟶
         distanceBounded (deviation p N (A+J*D) D) (deviation p N A D)
           (J*numerator p N A D J) (denominator p N A D)) :=
  closeUniv 5 (.impI (shift_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeUnitGridShift
