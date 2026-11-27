import IPRADerivations.Analysis.Euler.Integration.Parts.Grids.GaussianEulerIntegrationByPartsGridObservation
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadrature

/-!
# Original Euler rows weighted by actual unit-substitution cells

On the unchanged affine time grid, the image cell for u = exp(-t)
is the difference of the two actual decay observations. Multiplication
by the original power observation gives a literal finite density sum.
The checked decay increment and original power-times-decay identity
compare this sum with the unchanged Euler quadrature. No ordering or
positivity of rounded image cells is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionDensity

open_ipra
open GaussianEulerIntegrandName (fixedData)
open GaussianEulerPowerIncrement (point)
open GaussianEulerIntegrationByPartsLinear (originalProduct)
open GaussianEulerIntegrationByPartsGridObservation (rawF raw_grid_at grid_source rowCost)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianEulerDecayMesh (consecutiveDifference consecutive_difference_at stepError errorDen)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powerTerm (p t x : PTm n) : PTm n := point p (fstT x) (sndT x) (fstT t) (sndT t)
def powerEvaluatorF : PR 3 := PTm.toPR (powerTerm (var 0) (var 1) (var 2))
def densityBody : PTm 2 := qmul (sampleBody powerEvaluatorF)
  (consecutiveDifference (sampleBody GaussianEulerDecayQuadrature.evaluatorF))
def density (p N z B a C E : PTm n) : PTm n :=
  sum densityBody N (sampleData p N a C E (fixedData z B))
def source (z R B a C E T N : PTm n) : Fm PTm n :=
  intervalSource z R B a C E T ⋏ (le one N ⋏ (le one C ⋏ le C (E*N)))
def numerator (p R E T C N : PTm n) : PTm n :=
  num 3*majorant R E T*C*C*unit p+
    num 20*majorant R E T*(E*E*N*N)+C*rowCost R E T*(E*N)
def denominator (p E N : PTm n) : PTm n := E*E*N*unit p

ipra_subst powerTerm [point]
ipra_subst density
ipra_subst source

ipra_subst majorant [GaussianEulerCompactPowerMajorant.exponentRadius]
ipra_subst stepError [GaussianNameRingLaws.three]
ipra_subst errorDen

theorem power_evaluator_at (p a b z B : PTm n) : Γ ⊢[PRAAx]
    ap3 powerEvaluatorF p (pairT a b) (fixedData z B) ≐ point p z B a b := by
  have program : Γ ⊢[PRAAx] ap3 powerEvaluatorF p (pairT a b) (fixedData z B) ≐
      powerTerm p (pairT a b) (fixedData z B) := by
    simpa only [powerEvaluatorF,ap3,subst_powerTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (powerTerm (var 0) (var 1) (var 2) : PTm 3) ![p,pairT a b,fixedData z B]
  have value := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (point (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![p,fstT (fixedData z B),sndT (fixedData z B),fstT (pairT a b),sndT (pairT a b)]) (σ' := ![p,z,B,a,b])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _; exact fst_pair _ _; exact snd_pair _ _)
  exact program.eqTrans (by simpa only [powerTerm,point,GaussianEulerIntegrandName.subst_powerData,subst_ap2,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using value)

theorem power_grid_at (i p N z B a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody powerEvaluatorF) i (sampleData p N a C E (fixedData z B)) ≐
      point p z B (a*N+C*i) (E*N) :=
  (sample_body_at powerEvaluatorF i p N a C E _).eqTrans (power_evaluator_at p _ _ z B)

theorem density_row_at (i x : PTm n) :
    inst2 densityBody i x = qmul (inst2 (sampleBody powerEvaluatorF) i x)
      (inst2 (consecutiveDifference (sampleBody GaussianEulerDecayQuadrature.evaluatorF)) i x) := by
  simp [densityBody,inst2]

theorem original_cell_bound (i p z R B a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (multiplyBody (sampleBody rawF)) i
        (pairT (weight C E N) (sampleData p N a C E (fixedData z B))))
      (inst2 densityBody i (sampleData p N a C E (fixedData z B)))
      (majorant R E T*stepError (E*N) C p) (errorDen (E*N) p) := by
  let d := sampleData p N a C E (fixedData z B)
  let P := point p z B (a*N+C*i) (E*N)
  let D := GaussianEulerDecayMesh.observation (a*N+C*i) (E*N) p
  let w := weight C E N
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have hN := hs.andE₂.andE₁
  have hb := positive_product _ _ hE hN
  have hDen := positive_product _ _ (positive_product _ _ hb hb) (unit_positive p)
  have here := grid_source i N z R B a C E T hs.andE₁ hN (le_of_lt hi)
  have decayCell := GaussianEulerDecayQuadrature.cell_distance i p N a C E (fixedData z B)
    hs.andE₁.andE₂.andE₁ hN hE hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂
  have powerBound := original_power_observation p z R B E T _ _ here.andE₁ here.andE₂
  have multiplied := GaussianApproximateInverseDistance.multiply_distance P _ _ (majorant R E T) _ _ hDen powerBound decayCell
  have first : Γ ⊢[PRAAx]
      inst2 (multiplyBody (sampleBody rawF)) i (pairT w d) ≐
        qmul P (inst2 (multiplyBody (sampleBody GaussianEulerDecayQuadrature.evaluatorF)) i (pairT w d)) := by
    have read : Γ ⊢[PRAAx] inst2 (multiplyBody (sampleBody rawF)) i (pairT w d) ≐ qmul w (qmul P D) :=
      (multiply_body_at (sampleBody rawF) w i d).eqTrans
      (qmul_congr (.eqRefl _) (raw_grid_at i p N z B a C E))
    have decayRead : Γ ⊢[PRAAx] inst2 (multiplyBody (sampleBody GaussianEulerDecayQuadrature.evaluatorF)) i (pairT w d) ≐ qmul w D :=
      (multiply_body_at (sampleBody GaussianEulerDecayQuadrature.evaluatorF) w i d).eqTrans
      (qmul_congr (.eqRefl _) (GaussianEulerDecayQuadrature.cell_at i p N a C E (fixedData z B)))
    exact read.eqTrans ((GaussianRationalPowerAlgebra.qmul_commutative w (qmul P D)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative P D w).eqTrans
        ((qmul_congr (.eqRefl P) (GaussianRationalPowerAlgebra.qmul_commutative D w)).eqTrans
          (qmul_congr (.eqRefl P) decayRead.eqSymm))))
  have second : Γ ⊢[PRAAx] inst2 densityBody i d ≐
      qmul P (inst2 (consecutiveDifference (sampleBody GaussianEulerDecayQuadrature.evaluatorF)) i d) := by
    rw [density_row_at]
    exact qmul_congr (power_grid_at i p N z B a C E) (.eqRefl _)
  exact distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _) multiplied

theorem original_raw_finite_bound (p z R B a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature rawF p N a C E (fixedData z B)) (density p N z B a C E)
      (majorant R E T*stepError (E*N) C p) (denominator p E N) := by
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have hN := hs.andE₂.andE₁
  have hb := positive_product _ _ hE hN
  have hd := positive_product _ _ (positive_product _ _ hb hb) (unit_positive p)
  have hs' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have rows : Γ ⊢[PRAAx] termsDistance (multiplyBody (sampleBody rawF)) densityBody N
      (pairT (weight C E N) (sampleData p N a C E (fixedData z B)))
      (sampleData p N a C E (fixedData z B)) (majorant R E T*stepError (E*N) C p) (errorDen (E*N) p) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,subst_pairT,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerIntegrandName.subst_fixedData,GaussianRationalRiemannRefinement.subst_weight,
      PTm.subst_mul,subst_majorant,subst_stepError,subst_errorDen,Syn.shift] using
      original_cell_bound (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a)
        (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) hs'.wk Prf.hyp0
  have raw := distance_congr (sum_multiply (sampleBody rawF) (weight C E N) N _)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (sum_distance _ _ _ _ _ _ _ hd rows)
  exact distance_radius_mono _ _ _ _ _ _ hd
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hE hE) hN) (unit_positive p))
    (le_of_eq_add (d := zero) (by dsimp only [denominator,errorDen]; ipra_ring)) raw

theorem original_finite_bound (p z R B a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature GaussianEulerIntegrandName.evaluatorF p N a C E (fixedData z B))
      (density p N z B a C E) (numerator p R E T C N) (denominator p E N) := by
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have hN := hs.andE₂.andE₁
  have hd := positive_product _ _ (positive_product _ _ (positive_product _ _ hE hE) hN) (unit_positive p)
  have first := GaussianEulerIntegrationByPartsGridObservation.original_grid_observations p N z R B a C E T hs.andE₁ hN
  have widened := distance_radius_mono _ _ _ _ (C*rowCost R E T*(E*N)) (denominator p E N)
    (positive_product _ _ hE (unit_positive p)) hd
    (le_of_eq_add (d := zero) (by unfold denominator; ipra_ring)) first
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator stepError GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd widened (original_raw_finite_bound p z R B a C E T N hs))

theorem actual_original_unit_substitution_density_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 8)
        (var 4) (var 5) (var 6) (fixedData (var 1) (var 3)))
        (density (var 0) (var 8) (var 1) (var 3) (var 4) (var 5) (var 6))
        (numerator (var 0) (var 2) (var 6) (var 7) (var 5) (var 8)) (denominator (var 0) (var 6) (var 8))) :=
  closeUniv 9 (.impI (original_finite_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionDensity
