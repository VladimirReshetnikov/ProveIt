import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.NamedValues.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Recurrence.GaussianLogGammaEulerRecurrence
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference

/-!
# The real log-Gamma recurrence on adjacent unit quadratures

The positive real log-Gamma evaluator is sampled at the same physical
offset in the two intervals of length one. The difference agrees
with the logarithm quadrature up to a dyadic observation error
independent of the number of cells.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeUnitGridRecurrence

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData sample_body_at)
open GaussianNameEquivalence
  (crossEquivalent cross_symm cross_trans cross_to_diagonal diagonal_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalRiemannRefinement (termsDistance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => GaussianLogGammaEulerCofinal.nameF
local notation "G" => GaussianStirlingGammaLogarithm.logGammaF
local notation "L" => GaussianPositiveRationalLogarithm.logF
local notation "P" => GaussianRightHalfPlaneLogarithm.nameF
local notation "gd" => GaussianStirlingGammaLogarithm.logGammaData
local notation "ld" => GaussianPositiveRationalLogarithm.data
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data

private def evaluator (f : PR 2) (d : PTm 2) : PR 3 :=
  PTm.toPR (ap2 f (var 0) (inst2 d (fstT (var 1)) (sndT (var 1))) : PTm 3)

private theorem evaluator_at (f : PR 2) (d : PTm 2) (p A D x : PTm n) :
    Γ ⊢[PRAAx] ap3 (evaluator f d) p (pairT A D) x ≐ ap2 f p (inst2 d A D) := by
  have read : Γ ⊢[PRAAx] ap3 (evaluator f d) p (pairT A D) x ≐
      ap2 f p (inst2 d (fstT (pairT A D)) (sndT (pairT A D))) := by
    simpa only [evaluator, ap3, subst_ap2, subst_inst2, subst_fstT, subst_sndT,
      Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (ap2 f (var 0) (inst2 d (fstT (var 1)) (sndT (var 1))) : PTm 3)
        ![p,pairT A D,x]
  exact read.eqTrans (congrAp2 f (.eqRefl _) (congrInst2 d (fst_pair A D) (snd_pair A D)))

def logGammaEvaluator : PR 3 := evaluator G (gd (var 0) (var 1))
def logEvaluator : PR 3 := evaluator L (ld (var 0) (var 1))

theorem log_gamma_at (p A D x : PTm n) :
    Γ ⊢[PRAAx] ap3 logGammaEvaluator p (pairT A D) x ≐ ap2 G p (gd A D) := by
  simpa only [logGammaEvaluator,inst2,GaussianStirlingGammaLogarithm.subst_logGammaData,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    evaluator_at (Γ := Γ) G (gd (var 0) (var 1)) p A D x

theorem log_at (p A D x : PTm n) :
    Γ ⊢[PRAAx] ap3 logEvaluator p (pairT A D) x ≐ ap2 L p (ld A D) := by
  simpa only [logEvaluator,inst2,GaussianPositiveRationalLogarithm.subst_data,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    evaluator_at (Γ := Γ) L (ld (var 0) (var 1)) p A D x

theorem real_recurrence (A D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent (diffF G G) L (diffData (gd (A+D) D) (gd A D)) (ld A D) := by
  let a := gd (A+D) D
  let b := gd A D
  let x := GaussianLogGammaEulerCofinal.canonicalData (A+D) zero D zero
  let y := GaussianLogGammaEulerCofinal.canonicalData A zero D zero
  let t := GaussianRightHalfPlaneLogarithm.data A zero D zero
  have hs : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D zero :=
    .andI (.andI hA (.orI₁ (.eqRefl zero))) hD
  have hs' := GaussianLogGammaEulerRecurrenceFinite.shift_source A D zero hs
  have ha := GaussianStirlingGammaLogarithm.log_gamma_regular (A+D) D (.andI hs'.andE₁.andE₁ hD)
  have hb := GaussianStirlingGammaLogarithm.log_gamma_regular A D (.andI hA hD)
  have hx := GaussianLogGammaEulerCofinal.canonical_regular (A+D) zero D zero hs'
  have hy := GaussianLogGammaEulerCofinal.canonical_regular A zero D zero hs
  have ex := GaussianLogGammaEulerPositiveAxis.equivalent (A+D) D zero hs'
  have ey := GaussianLogGammaEulerPositiveAxis.equivalent A D zero hs
  have ed := GaussianNamedDifferenceQuotientProperness.difference_proper G C G C a x b y ha hx hb hy
    (cross_symm C G x a ex) (cross_symm C G y b ey)
  exact cross_trans (diffF G G) (diffF C C) L (diffData a b) (diffData x y) (ld A D) ed
    (cross_trans (diffF C C) P L (diffData x y) t (ld A D)
      (GaussianLogGammaEulerRecurrence.recurrence A zero D zero hs)
      (GaussianRightHalfPlaneLogarithm.positive_axis A D zero hs))

theorem sample_error (p A D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (ap2 G p (gd (A+D) D)) (ap2 G p (gd A D))) (ap2 L p (ld A D)) (num 8) (unit p) := by
  let a := gd (A+D) D
  let b := gd A D
  let v := ap2 (diffF G G) p (diffData a b)
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have ha := GaussianStirlingGammaLogarithm.log_gamma_regular (A+D) D
    (.andI (le_trans hA (le_add_right A D)) hD)
  have hb := GaussianStirlingGammaLogarithm.log_gamma_regular A D (.andI hA hD)
  have he := diagonal_at (diffF G G) L (diffData a b) (ld A D) p
    (cross_to_diagonal (diffF G G) L (diffData a b) (ld A D) (real_recurrence A D hA hD))
  have hr := GaussianNamedDifference.sample_error G G a b p ha hb
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same (qsub (ap2 G p a) (ap2 G p b)) v (ap2 L p (ld A D))
      (num 6) two U hu (distance_symmetric _ _ _ _ hu hr) he)

private theorem cell_error (i p N A W D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (GaussianRationalQuadratureDifference.differenceBody (sampleBody logGammaEvaluator)
        (sampleBody logGammaEvaluator)) i
          (pairT (sampleData p N (A+D) W D zero) (sampleData p N A W D zero)))
      (inst2 (sampleBody logEvaluator) i (sampleData p N A W D zero)) (num 8) (unit p) := by
  let a := A*N+W*i
  let d := D*N
  have ha : Γ ⊢[PRAAx] le one a :=
    le_trans (positive_product A N hA hN) (le_add_right (A*N) (W*i))
  have hd : Γ ⊢[PRAAx] le one d := positive_product D N hD hN
  have e : Γ ⊢[PRAAx] grid i N (A+D) W D ≐ pairT (a+d) d :=
    congrPairT (by dsimp only [a,d]; ipra_ring) (.eqRefl _)
  have e₁ := (sample_body_at logGammaEvaluator i p N (A+D) W D zero).eqTrans
    ((congrAp3 logGammaEvaluator (.eqRefl p) e (.eqRefl zero)).eqTrans (log_gamma_at p (a+d) d zero))
  have e₂ := (sample_body_at (Γ := Γ) logGammaEvaluator i p N A W D zero).eqTrans (log_gamma_at p a d zero)
  have e₃ := (sample_body_at (Γ := Γ) logEvaluator i p N A W D zero).eqTrans (log_at p a d zero)
  have ed := (GaussianRationalQuadratureDifference.difference_body_at (sampleBody logGammaEvaluator)
    (sampleBody logGammaEvaluator) i (sampleData p N (A+D) W D zero) (sampleData p N A W D zero)).eqTrans
      (GaussianRationalSyntheticDivision.qsub_congr e₁ e₂)
  exact distance_congr ed.eqSymm e₃.eqSymm (.eqRefl _) (.eqRefl _) (sample_error p a d ha hd)

/-- The shifted log-Gamma recurrence on a strip of width `W/D`. -/
theorem strip_quadrature_error (p N A W D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (quadrature logGammaEvaluator p N (A+D) W D zero)
        (quadrature logGammaEvaluator p N A W D zero))
      (quadrature logEvaluator p N A W D zero) (W*num 8) (D*unit p) := by
  let g := sampleBody logGammaEvaluator
  let f := GaussianRationalQuadratureDifference.differenceBody g g
  let x := sampleData p N (A+D) W D zero
  let y := sampleData p N A W D zero
  have rows : Γ ⊢[PRAAx] termsDistance f (sampleBody logEvaluator) N (pairT x y) y (num 8) (unit p) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N)::Γ.map Fm.shift
    have sn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have sa : Δ ⊢[PRAAx] le one (s A) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hA.shift.wk
    have sd : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hD.shift.wk
    simpa only [f,g,x,y,s,Δ,Syn.shift,subst_pairT,GaussianCompactRiemannName.subst_sampleData,
      PTm.subst_add,ConciseIPRA.PTm.subst_zero,LeanProofs.IPRA.PTm.subst_num,
      GaussianCoefficientNameBounds.subst_unit] using
      cell_error (var 0) (s p) (s N) (s A) (s W) (s D) sn sa sd
  have raw := GaussianCompactScalarMajorant.common_mesh_distance f (sampleBody logEvaluator) N
    (pairT x y) y W D (num 8) (unit p) hN hD (unit_positive p) rows
  exact distance_congr (GaussianRationalQuadratureDifference.weighted_difference g g N x y W D).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

theorem quadrature_error (p N A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (quadrature logGammaEvaluator p N (A+D) D D zero)
        (quadrature logGammaEvaluator p N A D D zero))
      (quadrature logEvaluator p N A D D zero) (num 8) (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ (num 8) (unit p) (positive_product _ _ hD hu) hu
    (le_of_eq_add (d := zero) (by ipra_ring)) (strip_quadrature_error p N A D D hN hA hD)

theorem actual_real_log_Gamma_adjacent_unit_quadratures_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let p := var 0
       let N := var 1
       let A := var 2
       let D := var 3
       (le one N ⋏ (le one A ⋏ le one D)) ⟶
         distanceBounded (qsub (quadrature logGammaEvaluator p N (A+D) D D zero)
           (quadrature logGammaEvaluator p N A D D zero))
           (quadrature logEvaluator p N A D D zero) (num 8) (unit p)) :=
  closeUniv 4 (.impI (quadrature_error _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeUnitGridRecurrence
