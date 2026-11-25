import IPRADerivations.Analysis.GaussianRaabeLogPrimitiveCell
import IPRADerivations.Analysis.GaussianRaabeUnitGridRecurrence
import IPRADerivations.Analysis.GaussianRationalParameterTelescope

/-!
# The logarithm primitive on the original compact grid

The endpoints are observed with the common denominator of the
actual left grid. A finite telescope gives the mesh error and
retains an explicit allowance for the shared observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeLogPrimitiveGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData sample_body_at)
open GaussianPositiveRationalLogarithm (fraction sample)
open GaussianRaabeLogPrimitiveCell (area primitive subst_primitive)
open GaussianRaabeUnitGridRecurrence (logEvaluator log_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalParameterTelescope (localRows local_error)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private def evaluator : PR 3 :=
  PTm.toPR (primitive (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 3)

private theorem primitive_data_congr (p A B D E : PTm n)
    (hA : Γ ⊢[PRAAx] A ≐ B) (hD : Γ ⊢[PRAAx] D ≐ E) :
    Γ ⊢[PRAAx] primitive p A D ≐ primitive p B E := by
  simpa only [subst_primitive,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (primitive (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,A,D]) (σ' := ![p,B,E]) (fun i => by fin_cases i; exact .eqRefl p; exact hA; exact hD)

private theorem evaluator_at (p A D x : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluator p (pairT A D) x ≐ primitive p A D := by
  have read : Γ ⊢[PRAAx] ap3 evaluator p (pairT A D) x ≐
      primitive p (fstT (pairT A D)) (sndT (pairT A D)) := by
    simpa only [evaluator,ap3,subst_primitive,subst_fstT,subst_sndT,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (primitive (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 3)
        ![p,pairT A D,x]
  exact read.eqTrans (primitive_data_congr _ _ _ _ _ (fst_pair A D) (snd_pair A D))

def numerator (p N A C : PTm n) : PTm n :=
  two*(A+C)*(C*C)*unit p+two*(A+C)*(A*A)*(N*N)
def denominator (p N A D : PTm n) : PTm n := D*(A*A)*N*unit p

private def rowNumerator (p N A C : PTm n) : PTm n :=
  (two*((A+C)*N))*(C*C)*unit p+(two*((A+C)*N))*((A*N)*(A*N))
private def rowDenominator (p N A D : PTm n) : PTm n := D*N*((A*N)*(A*N))*unit p

@[simp] private theorem subst_rowNumerator {m : ℕ} (σ : Fin n → PTm m) (p N A C : PTm n) :
    Syn.subst σ (rowNumerator p N A C) = rowNumerator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ C) := by
  simp [rowNumerator,two]

@[simp] private theorem subst_rowDenominator {m : ℕ} (σ : Fin n → PTm m) (p N A D : PTm n) :
    Syn.subst σ (rowDenominator p N A D) = rowDenominator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [rowDenominator]

private theorem row_bound (p i N A C D : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (primitive p (A*N+C*i+C) (D*N)) (primitive p (A*N+C*i) (D*N)))
      (area p (A*N+C*i) (D*N) C) (rowNumerator p N A C) (rowDenominator p N A D) := by
  let L := A*N
  let R := (A+C)*N
  let a := L+C*i
  let d := D*N
  let U := unit p
  have hl := positive_product A N hA hN
  have hd := positive_product D N hD hN
  have hu := unit_positive (Γ := Γ) p
  have hlo : Γ ⊢[PRAAx] le L a := le_add_right _ _
  have ha := le_trans hl hlo
  have hhi : Γ ⊢[PRAAx] le (a+C) R :=
    le_congr (by dsimp only [a,L]; ipra_ring) (by dsimp only [R,L]; ipra_ring)
      (add_le_add_right L (mul_le_mul_right C hi))
  have hmid : Γ ⊢[PRAAx] le (two*a+C) (two*R) := by
    exact le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_trans (le_add_right a C) hhi) hhi)
  have hloSq := le_mul_mono hlo hlo
  have old := positive_product _ _ (positive_product _ _ hd (positive_product _ _ ha ha)) hu
  have new := positive_product _ _ (positive_product _ _ hd (positive_product _ _ hl hl)) hu
  have cross : Γ ⊢[PRAAx]
      le (GaussianRaabeLogPrimitiveCell.numerator p a C*rowDenominator p N A D)
        (rowNumerator p N A C*GaussianRaabeLogPrimitiveCell.denominator p a d) := by
    change Γ ⊢[PRAAx] le (((two*a+C)*(C*C)*U+two*(a+C)*(a*a))*(d*(L*L)*U))
      (((two*R)*(C*C)*U+(two*R)*(L*L))*(d*(a*a)*U))
    ipra_le 2*𝔞(d)*𝔞(R)*𝔞(C)^2*𝔞(U)^2*sl hloSq +
      𝔞(d)*𝔞(L)^2*𝔞(C)^2*𝔞(U)^2*sl hmid +
      2*𝔞(d)*𝔞(U)*𝔞(a)^2*𝔞(L)^2*sl hhi
  exact distance_radius_mono _ _ _ _ _ _ old new cross
    (GaussianRaabeLogPrimitiveCell.cell_error p a d C ha hd)

private theorem row_error (p i N A C D : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (GaussianRationalParameterTelescope.forward (sampleBody evaluator)) i (sampleData p N A C D zero))
      (inst2 (GaussianRationalFiniteSum.multiplyBody (sampleBody logEvaluator)) i
        (pairT (weight C D N) (sampleData p N A C D zero))) (rowNumerator p N A C) (rowDenominator p N A D) := by
  let x := sampleData p N A C D zero
  let a := A*N+C*i
  let d := D*N
  have now := (sample_body_at (Γ := Γ) evaluator i p N A C D zero).eqTrans (evaluator_at p a d zero)
  have next := (sample_body_at (Γ := Γ) evaluator (succ i) p N A C D zero).eqTrans
    ((evaluator_at p (A*N+C*succ i) d zero).eqTrans
      (primitive_data_congr p _ (a+C) d d (by dsimp only [a]; ipra_ring) (.eqRefl d)))
  have log := (sample_body_at (Γ := Γ) logEvaluator i p N A C D zero).eqTrans (log_at p a d zero)
  have line := (GaussianRationalFiniteSum.multiply_body_at (sampleBody logEvaluator) (weight C D N) i x).eqTrans
    (qmul_congr (.eqRefl (fraction C d)) log)
  rw [GaussianRationalParameterTelescope.forward_at]
  exact distance_congr (qsub_congr next now).eqSymm line.eqSymm (.eqRefl _) (.eqRefl _)
    (row_bound p i N A C D hA hD hN hi)

theorem finite_grid (p N A C D : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (primitive p ((A+C)*N) (D*N)) (primitive p (A*N) (D*N)))
      (quadrature logEvaluator p N A C D zero) (numerator p N A C) (denominator p N A D) := by
  let x := sampleData p N A C D zero
  let f := sampleBody evaluator
  let g := sampleBody logEvaluator
  let d := D*N
  let a := A*N
  have hu := unit_positive (Γ := Γ) p
  have hx := positive_product A N hA hN
  have hd := positive_product D N hD hN
  have old := positive_product _ _ (positive_product _ _ hd (positive_product _ _ hx hx)) hu
  have new := positive_product _ _ (positive_product _ _ (positive_product _ _ hD
    (positive_product _ _ hA hA)) hN) hu
  have rows : Γ ⊢[PRAAx] localRows f g N x x (weight C D N) (rowNumerator p N A C) (rowDenominator p N A D) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N)::Γ.map Fm.shift
    have sa : Δ ⊢[PRAAx] le one (s A) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hA.shift.wk
    have sd : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hD.shift.wk
    have sn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    simpa only [f,g,x,s,Δ,Syn.shift,subst_pairT,GaussianCompactRiemannName.subst_sampleData,
      GaussianRationalRiemannRefinement.subst_weight,subst_rowNumerator,subst_rowDenominator,
      ConciseIPRA.PTm.subst_zero] using
      row_error (s p) (var 0) (s N) (s A) (s C) (s D) sa sd sn Prf.hyp0
  have left := (sample_body_at (Γ := Γ) evaluator zero p N A C D zero).eqTrans
    ((evaluator_at p (a+C*zero) d zero).eqTrans (primitive_data_congr p _ a d d (by ipra_ring) (.eqRefl d)))
  have right := (sample_body_at (Γ := Γ) evaluator N p N A C D zero).eqTrans
    ((evaluator_at p (a+C*N) d zero).eqTrans
      (primitive_data_congr p _ ((A+C)*N) d d (by dsimp only [a]; ipra_ring) (.eqRefl d)))
  have sum := local_error f g N x x (weight C D N) (rowNumerator p N A C) (rowDenominator p N A D) old rows
  exact distance_congr (qsub_congr right left) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ old new
      (le_of_eq_add (d := zero) (by dsimp only [numerator,denominator,rowNumerator,rowDenominator]; ipra_ring)) sum)

theorem actual_positive_logarithm_primitive_grid_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let p := var 0
       let N := var 1
       let A := var 2
       let C := var 3
       let D := var 4
       (le one A ⋏ (le one D ⋏ le one N)) ⟶
         distanceBounded (qsub (primitive p ((A+C)*N) (D*N)) (primitive p (A*N) (D*N)))
           (quadrature logEvaluator p N A C D zero) (numerator p N A C) (denominator p N A D)) :=
  closeUniv 5 (.impI (finite_grid _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeLogPrimitiveGrid
