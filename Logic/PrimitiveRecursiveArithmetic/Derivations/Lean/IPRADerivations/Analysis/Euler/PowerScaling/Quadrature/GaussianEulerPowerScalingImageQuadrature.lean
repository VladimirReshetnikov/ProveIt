import IPRADerivations.Analysis.Euler.PowerScaling.Quadrature.GaussianEulerPowerScalingCell
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingCompactName
import IPRADerivations.Foundations.BoundedSyntax

/-!
# Finite power substitution on the original compact quadrature

The source sum is the ordinary affine quadrature of the actual
power-damped Euler evaluator. The image sum has the actual corrected
widths and original rescaled Euler samples at the literal decoded
points. One original scale observation multiplies the entire image
sum. The radius is the sum of the checked cell bounds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingImageQuadrature

open_ipra
open GaussianEulerPowerScalingCell (source scaleSample physicalCell imageCell numerator denominator)
open GaussianEulerPowerScalingCompactName (evaluatorF fixedData)
open GaussianCompactRiemannName (sampleBody sampleData quadrature)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def payload (p k z B e f d h Q S E T a C N : PTm n) : PTm n :=
  Foundations.BoundedSyntax.pack (![p,k,z,B,e,f,d,h,Q,S,E,T,a,C,N] : Fin 15 → PTm n)
private def fields (i x : PTm n) : Fin 16 → PTm n :=
  Fin.cases i (fun j => Foundations.BoundedFormulas.at1 (Foundations.BoundedSyntax.projections 15 j) x)
private def body : PTm 16 :=
  imageCell (var 1) (var 2) (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15)
def imageBody : PTm 2 := Syn.subst (fields (var 0) (var 1)) body
def imageSum (p k z B e f d h Q S E T a C N : PTm n) : PTm n :=
  sum imageBody N (payload p k z B e f d h Q S E T a C N)

ipra_subst payload [Foundations.BoundedSyntax.subst_pack]

theorem image_body_at (p k i z B e f d h Q S E T a C N : PTm n) :
    Γ ⊢[PRAAx] inst2 imageBody i (payload p k z B e f d h Q S E T a C N) ≐ imageCell p k i z B e f d h Q S E T a C N := by
  let args : Fin 15 → PTm n := ![p,k,z,B,e,f,d,h,Q,S,E,T,a,C,N]
  let P := Foundations.BoundedSyntax.pack args
  have eval : inst2 imageBody i P = Syn.subst (fields i P) body := by
    simp only [inst2,imageBody,Syn.subst_subst]
    congr 1
    funext j
    cases j using Fin.cases with
    | zero => simp [fields]
    | succ j =>
      simp only [fields,Fin.cases_succ,Foundations.BoundedFormulas.at1,Syn.subst_subst]
      congr 1
      funext l
      fin_cases l
      rfl
  have decode : Syn.subst (Fin.cases i args) body = imageCell p k i z B e f d h Q S E T a C N := by
    simp only [body,GaussianEulerPowerScalingCell.subst_imageCell,Syn.subst_var]
    rfl
  have equality : Γ ⊢[PRAAx] Syn.subst (fields i P) body ≐ Syn.subst (Fin.cases i args) body := by
    refine Prf.eqCongr body (fun j => ?_)
    cases j using Fin.cases with
    | zero => exact .eqRefl _
    | succ j => exact Foundations.BoundedSyntax.projections_pack args j
  change Γ ⊢[PRAAx] inst2 imageBody i P ≐ imageCell p k i z B e f d h Q S E T a C N
  rw [eval,←decode]
  exact equality

theorem physical_body_at (p i z B e f d h S E a C N : PTm n) :
    Γ ⊢[PRAAx] inst2 (multiplyBody (sampleBody evaluatorF)) i
      (pairT (qmul (fraction e f) (fraction C (E*N))) (sampleData p N a C E (fixedData z B e f d h S))) ≐
      physicalCell p i z B e f d h S E a C N := by
  let t := GaussianCompactRiemannName.grid i N a C E
  let F := GaussianEulerPowerScalingCompactRate.nameF
  let b := E*N
  let c := a*N+C*i
  have pair : t = pairT c b := rfl
  have getFirst : Γ ⊢[PRAAx] fstT t ≐ c := by rw [pair]; exact fst_pair _ _
  have getSecond : Γ ⊢[PRAAx] sndT t ≐ b := by rw [pair]; exact snd_pair _ _
  have getA : Γ ⊢[PRAAx] GaussianEulerPowerScalingCompactRate.data z B e f d h S (fstT t) (sndT t) ≐
      GaussianEulerPowerScalingCompactRate.data z B e f d h S c (sndT t) := by
    simpa only [GaussianEulerPowerScalingCompactRate.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianEulerPowerScalingCompactRate.data (Syn.shift z) (Syn.shift B) (Syn.shift e) (Syn.shift f)
        (Syn.shift d) (Syn.shift h) (Syn.shift S) (var 0) (Syn.shift (sndT t))) getFirst
  have getB : Γ ⊢[PRAAx] GaussianEulerPowerScalingCompactRate.data z B e f d h S c (sndT t) ≐
      GaussianEulerPowerScalingCompactRate.data z B e f d h S c b := by
    simpa only [GaussianEulerPowerScalingCompactRate.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianEulerPowerScalingCompactRate.data (Syn.shift z) (Syn.shift B) (Syn.shift e) (Syn.shift f)
        (Syn.shift d) (Syn.shift h) (Syn.shift S) (Syn.shift c) (var 0)) getSecond
  have row := (GaussianCompactRiemannName.sample_body_at (Γ := Γ) evaluatorF i p N a C E (fixedData z B e f d h S)).eqTrans
    ((GaussianEulerPowerScalingCompactName.evaluator_at p t z B e f d h S).eqTrans (congrAp2 F (.eqRefl p) (getA.eqTrans getB)))
  exact (multiply_body_at _ (qmul (fraction e f) (fraction C b)) i _).eqTrans (qmul_congr (.eqRefl _) row)

private theorem row_distances (p k z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B e f d h Q S E T a C N) :
    Γ ⊢[PRAAx] termsDistance (multiplyBody (sampleBody evaluatorF)) (multiplyBody imageBody) N
      (pairT (qmul (fraction e f) (fraction C (E*N))) (sampleData p N a C E (fixedData z B e f d h S)))
      (pairT (scaleSample p z B e f d h) (payload p k z B e f d h Q S E T a C N))
      (numerator p k z R B e f d h Q S E T C N) (denominator p k h Q E T N) := by
  let sh (t : PTm n) := Syn.shift t
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S)
      (sh E) (sh T) (sh a) (sh C) (sh N) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerPowerScalingCell.subst_source,sh] using hs.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have left := physical_body_at (Γ := Δ) (sh p) (var 0) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h)
    (sh S) (sh E) (sh a) (sh C) (sh N)
  let rightData := payload (sh p) (sh k) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N)
  have right := (multiply_body_at (Γ := Δ) imageBody (scaleSample (sh p) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h))
    (var 0) rightData).eqTrans (qmul_congr (.eqRefl _)
      (image_body_at (sh p) (sh k) (var 0) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S)
        (sh E) (sh T) (sh a) (sh C) (sh N)))
  simp only [GaussianRationalHorner.subst_qmul,GaussianPositiveRationalLogarithm.subst_fraction,
    subst_pairT,PTm.subst_mul,GaussianCompactRiemannName.subst_sampleData,GaussianEulerPowerScalingCompactName.subst_fixedData,
    GaussianEulerPowerScalingCell.subst_scaleSample,subst_payload,GaussianEulerPowerScalingCell.subst_numerator,
    GaussianEulerPowerScalingCell.subst_denominator,Syn.shift]
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerPowerScalingCell.original_cell (sh p) (sh k) (var 0) (sh z) (sh R) (sh B) (sh e) (sh f) (sh d) (sh h)
        (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N) ss.wk Prf.hyp0)

theorem original_quadrature_to_image (p k z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B e f d h Q S E T a C N) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction e f) (quadrature evaluatorF p N a C E (fixedData z B e f d h S)))
      (qmul (scaleSample p z B e f d h) (imageSum p k z B e f d h Q S E T a C N))
      (N*numerator p k z R B e f d h Q S E T C N) (denominator p k h Q E T N) := by
  let x := sampleData p N a C E (fixedData z B e f d h S)
  let y := payload p k z B e f d h Q S E T a C N
  let s := qmul (fraction e f) (fraction C (E*N))
  let t := scaleSample p z B e f d h
  have hm := hs.andE₂.andE₁
  have hd := GaussianEulerPowerScalingCell.denominator_positive p k h Q E T N hm.andE₂.andE₁ hm.andE₂.andE₂.andE₂.andE₂
  have sums := sum_distance _ _ N (pairT s x) (pairT t y) _ _ hd
    (row_distances p k z R B e f d h Q S E T a C N hs)
  have left := (sum_multiply (Γ := Γ) (sampleBody evaluatorF) s N x).eqTrans
    (qmul_associative (fraction e f) (fraction C (E*N)) (sum (sampleBody evaluatorF) N x))
  exact distance_congr left (sum_multiply imageBody t N y) (.eqRefl _) (.eqRefl _) sums

theorem actual_original_power_scaling_image_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)
      (var 13) (var 14) (var 15) ⟶ distanceBounded
      (qmul (fraction (var 5) (var 6)) (quadrature evaluatorF (var 0) (var 15) (var 13) (var 14) (var 11)
        (fixedData (var 2) (var 4) (var 5) (var 6) (var 7) (var 8) (var 10))))
      (qmul (scaleSample (var 0) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8))
        (imageSum (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
          (var 11) (var 12) (var 13) (var 14) (var 15)))
      ((var 15)*numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
        (var 10) (var 11) (var 12) (var 14) (var 15))
      (denominator (var 0) (var 1) (var 8) (var 9) (var 11) (var 12) (var 15))) :=
  closeUniv 16 (.impI (original_quadrature_to_image _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingImageQuadrature
