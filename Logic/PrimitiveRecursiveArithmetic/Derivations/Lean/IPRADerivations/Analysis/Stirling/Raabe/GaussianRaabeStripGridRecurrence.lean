import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeUnitGridRecurrence

/-!
# The real log-Gamma recurrence on shifted compact quadratures

The original uniform left tags are paired across a shift by one.
Summing the pointwise recurrence retains the exact interval width in
the observation error, including the case of zero width.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeStripGridRecurrence

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData sample_body_at)
open GaussianRaabeUnitGridRecurrence (logGammaEvaluator logEvaluator log_gamma_at log_at sample_error)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalRiemannRefinement (termsDistance)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem cell_error (i p N A C D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (GaussianRationalQuadratureDifference.differenceBody (sampleBody logGammaEvaluator)
        (sampleBody logGammaEvaluator)) i
          (pairT (sampleData p N (A+D) C D zero) (sampleData p N A C D zero)))
      (inst2 (sampleBody logEvaluator) i (sampleData p N A C D zero)) (num 8) (unit p) := by
  let a := A*N+C*i
  let d := D*N
  have ha : Γ ⊢[PRAAx] le one a :=
    le_trans (positive_product A N hA hN) (le_add_right (A*N) (C*i))
  have hd : Γ ⊢[PRAAx] le one d := positive_product D N hD hN
  have e : Γ ⊢[PRAAx] grid i N (A+D) C D ≐ pairT (a+d) d :=
    congrPairT (by dsimp only [a,d]; ipra_ring) (.eqRefl _)
  have e₁ := (sample_body_at logGammaEvaluator i p N (A+D) C D zero).eqTrans
    ((congrAp3 logGammaEvaluator (.eqRefl p) e (.eqRefl zero)).eqTrans (log_gamma_at p (a+d) d zero))
  have e₂ := (sample_body_at (Γ := Γ) logGammaEvaluator i p N A C D zero).eqTrans (log_gamma_at p a d zero)
  have e₃ := (sample_body_at (Γ := Γ) logEvaluator i p N A C D zero).eqTrans (log_at p a d zero)
  have ed := (GaussianRationalQuadratureDifference.difference_body_at (sampleBody logGammaEvaluator)
    (sampleBody logGammaEvaluator) i (sampleData p N (A+D) C D zero) (sampleData p N A C D zero)).eqTrans
      (GaussianRationalSyntheticDivision.qsub_congr e₁ e₂)
  exact distance_congr ed.eqSymm e₃.eqSymm (.eqRefl _) (.eqRefl _) (sample_error p a d ha hd)

theorem quadrature_error (p N A C D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (quadrature logGammaEvaluator p N (A+D) C D zero)
        (quadrature logGammaEvaluator p N A C D zero))
      (quadrature logEvaluator p N A C D zero) (C*num 8) (D*unit p) := by
  let g := sampleBody logGammaEvaluator
  let f := GaussianRationalQuadratureDifference.differenceBody g g
  let x := sampleData p N (A+D) C D zero
  let y := sampleData p N A C D zero
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
      cell_error (var 0) (s p) (s N) (s A) (s C) (s D) sn sa sd
  have raw := GaussianCompactScalarMajorant.common_mesh_distance f (sampleBody logEvaluator) N
    (pairT x y) y C D (num 8) (unit p) hN hD (unit_positive p) rows
  exact distance_congr (GaussianRationalQuadratureDifference.weighted_difference g g N x y C D).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

theorem actual_shifted_log_Gamma_strip_quadratures_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let p := var 0
       let N := var 1
       let A := var 2
       let C := var 3
       let D := var 4
       (le one N ⋏ (le one A ⋏ le one D)) ⟶
         distanceBounded (qsub (quadrature logGammaEvaluator p N (A+D) C D zero)
           (quadrature logGammaEvaluator p N A C D zero))
           (quadrature logEvaluator p N A C D zero) (C*num 8) (D*unit p)) :=
  closeUniv 5 (.impI (quadrature_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeStripGridRecurrence
