import IPRADerivations.Analysis.GaussianEulerPositiveScalingQuadrature
import IPRADerivations.Foundations.FiniteQueryDemand

/-!
# One original scale-factor observation outside the actual finite sum

The finite maximum is computed from the actual per-row multiplication
moduli. Each original normalized scaling row is compared to the original
power at the fixed scale times the unchanged modified evaluator at the
same requested precision. The genuine finite sum multiplication law
extracts that single observation, including zero interval width.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingFactorExtraction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEulerPositiveScalingIntegrand (dampedF dampedData productF productData fixedData)
open GaussianEulerPositiveScalingQuadrature (source)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianNameArithmetic (multiplyModulus)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factor (p z B c d : PTm n) : PTm n := ap2 powerF p (powerData z B c d)
def rowCost (z B a b c d : PTm n) : PTm n :=
  multiplyModulus powerF dampedF (powerData z B c d) (dampedData z B a b c d)+one
def costTerm (_p t x : PTm n) : PTm n :=
  rowCost (fstT (fstT x)) (sndT (fstT x)) (fstT t) (sndT t) (fstT (sndT x)) (sndT (sndT x))
def costF : PR 3 := PTm.toPR (costTerm (var 0) (var 1) (var 2))
def costData (N z B a C E c d : PTm n) : PTm n := sampleData zero N a C E (fixedData z B c d)
def maximumCost (N z B a C E c d : PTm n) : PTm n := finiteMaximum (sampleBody costF) N (costData N z B a C E c d)

@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (p z B c d : PTm n) :
    Syn.subst σ (factor p z B c d) = factor (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ c) (Syn.subst σ d) := by simp [factor]
@[simp] theorem subst_rowCost {m : ℕ} (σ : Fin n → PTm m) (z B a b c d : PTm n) :
    Syn.subst σ (rowCost z B a b c d) = rowCost (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a)
      (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [rowCost]
@[simp] theorem subst_costTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (costTerm p t x) = costTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [costTerm]
@[simp] theorem subst_costData {m : ℕ} (σ : Fin n → PTm m) (N z B a C E c d : PTm n) :
    Syn.subst σ (costData N z B a C E c d) = costData (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ c) (Syn.subst σ d) := by simp [costData]
@[simp] theorem subst_maximumCost {m : ℕ} (σ : Fin n → PTm m) (N z B a C E c d : PTm n) :
    Syn.subst σ (maximumCost N z B a C E c d) = maximumCost (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ c) (Syn.subst σ d) := by simp [maximumCost]

private theorem cost_congr (z B a b c d z' B' a' b' c' d' : PTm n)
    (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B') (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') (hc : Γ ⊢[PRAAx] c ≐ c') (hd : Γ ⊢[PRAAx] d ≐ d') : Γ ⊢[PRAAx]
    rowCost z B a b c d ≐ rowCost z' B' a' b' c' d' := by
  have e1 : Γ ⊢[PRAAx] rowCost z B a b c d ≐ rowCost z' B a b c d := by
    simpa only [subst_rowCost,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rowCost (var 0) (Syn.shift B) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)) hz
  have e2 : Γ ⊢[PRAAx] rowCost z' B a b c d ≐ rowCost z' B' a b c d := by
    simpa only [subst_rowCost,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rowCost (Syn.shift z') (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)) hB
  have e3 : Γ ⊢[PRAAx] rowCost z' B' a b c d ≐ rowCost z' B' a' b c d := by
    simpa only [subst_rowCost,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rowCost (Syn.shift z') (Syn.shift B') (var 0) (Syn.shift b) (Syn.shift c) (Syn.shift d)) ha
  have e4 : Γ ⊢[PRAAx] rowCost z' B' a' b c d ≐ rowCost z' B' a' b' c d := by
    simpa only [subst_rowCost,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rowCost (Syn.shift z') (Syn.shift B') (Syn.shift a') (var 0) (Syn.shift c) (Syn.shift d)) hb
  have e5 : Γ ⊢[PRAAx] rowCost z' B' a' b' c d ≐ rowCost z' B' a' b' c' d := by
    simpa only [subst_rowCost,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rowCost (Syn.shift z') (Syn.shift B') (Syn.shift a') (Syn.shift b') (var 0) (Syn.shift d)) hc
  have e6 : Γ ⊢[PRAAx] rowCost z' B' a' b' c' d ≐ rowCost z' B' a' b' c' d' := by
    simpa only [subst_rowCost,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rowCost (Syn.shift z') (Syn.shift B') (Syn.shift a') (Syn.shift b') (Syn.shift c') (var 0)) hd
  exact e1.eqTrans (e2.eqTrans (e3.eqTrans (e4.eqTrans (e5.eqTrans e6))))

theorem cost_at (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    ap3 costF p (pairT a b) (fixedData z B c d) ≐ rowCost z B a b c d := by
  have program : Γ ⊢[PRAAx] ap3 costF p (pairT a b) (fixedData z B c d) ≐ costTerm p (pairT a b) (fixedData z B c d) := by
    simpa [costF,ap3] using toPR_eq (Γ := Γ) (costTerm (var 0) (var 1) (var 2) : PTm 3) ![p,pairT a b,fixedData z B c d]
  have left := fst_pair (Γ := Γ) (pairT z B) (pairT c d)
  have right := snd_pair (Γ := Γ) (pairT z B) (pairT c d)
  exact program.eqTrans (cost_congr _ _ _ _ _ _ _ _ _ _ _ _
    ((congrFst left).eqTrans (fst_pair _ _)) ((congrSnd left).eqTrans (snd_pair _ _))
    (fst_pair _ _) (snd_pair _ _)
    ((congrFst right).eqTrans (fst_pair _ _)) ((congrSnd right).eqTrans (snd_pair _ _)))

theorem row_cost_at (i N z B a C E c d : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody costF) i (costData N z B a C E c d) ≐ rowCost z B (a*N+C*i) (E*N) c d :=
  (sample_body_at costF i zero N a C E (fixedData z B c d)).eqTrans (cost_at zero z B _ _ c d)

theorem row_cost_bound (i N z B a C E c d : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    le (rowCost z B (a*N+C*i) (E*N) c d) (maximumCost N z B a C E c d) :=
  le_congr (row_cost_at i N z B a C E c d) (.eqRefl _) (finiteMaximum_at (sampleBody costF) hi)

theorem row_error (i p N z B a C E c d : PTm n) (hs : Γ ⊢[PRAAx] source B a E N c d)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (sampleBody GaussianEulerPositiveScalingQuadrature.evaluatorF) i (sampleData p N a C E (fixedData z B c d)))
      (inst2 (multiplyBody (sampleBody GaussianEulerPositiveScalingIntegrand.evaluatorF)) i
        (pairT (factor p z B c d) (sampleData p N a C E (fixedData z B c d))))
      (maximumCost N z B a C E c d) (unit p) := by
  have s := GaussianEulerPositiveScalingQuadrature.grid_source i B a C E N c d hs
  have hP := GaussianEulerIntegrandName.power_regular z B c d (.andI s.andE₁ s.andE₂.andE₁)
  have hD := GaussianEulerPositiveScalingIntegrand.damped_regular z B (a*N+C*i) (E*N) c d s
  have original := GaussianNameRingLaws.multiply_sample_error powerF dampedF (powerData z B c d)
    (dampedData z B (a*N+C*i) (E*N) c d) p hP hD
  have left := (sample_body_at (Γ := Γ) GaussianEulerPositiveScalingQuadrature.evaluatorF i p N a C E (fixedData z B c d)).eqTrans
    (GaussianEulerPositiveScalingQuadrature.sample_at p z B _ _ c d)
  have right := (multiply_body_at (Γ := Γ) (sampleBody GaussianEulerPositiveScalingIntegrand.evaluatorF) (factor p z B c d) i
      (sampleData p N a C E (fixedData z B c d))).eqTrans
    (qmul_congr (.eqRefl _) ((sample_body_at GaussianEulerPositiveScalingIntegrand.evaluatorF i p N a C E (fixedData z B c d)).eqTrans
      (GaussianEulerPositiveScalingIntegrand.sample_at p z B _ _ c d)))
  have raw : Γ ⊢[PRAAx] distanceBounded
      (inst2 (sampleBody GaussianEulerPositiveScalingQuadrature.evaluatorF) i (sampleData p N a C E (fixedData z B c d)))
      (inst2 (multiplyBody (sampleBody GaussianEulerPositiveScalingIntegrand.evaluatorF)) i
        (pairT (factor p z B c d) (sampleData p N a C E (fixedData z B c d))))
      (rowCost z B (a*N+C*i) (E*N) c d) (unit p) :=
    distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) original
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p)
    (mul_le_mul_right (unit p) (row_cost_bound i N z B a C E c d hi)) raw

/-- One fixed original factor observation is outside the entire genuine
finite modified quadrature; its clock is exactly p on every row. -/
theorem original_extraction (p N z B a C E c d : PTm n) (hs : Γ ⊢[PRAAx] source B a E N c d) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerPositiveScalingQuadrature.evaluatorF p N a C E (fixedData z B c d))
      (qmul (factor p z B c d) (quadrature GaussianEulerPositiveScalingIntegrand.evaluatorF p N a C E (fixedData z B c d)))
      (C*maximumCost N z B a C E c d) (E*unit p) := by
  let f := sampleBody GaussianEulerPositiveScalingQuadrature.evaluatorF
  let g := sampleBody GaussianEulerPositiveScalingIntegrand.evaluatorF
  let x := sampleData p N a C E (fixedData z B c d)
  let w := factor p z B c d
  let y := pairT w x
  let L := maximumCost N z B a C E c d
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift B) (Syn.shift a) (Syn.shift E) (Syn.shift N) (Syn.shift c) (Syn.shift d) :=
    by simpa only [Fm.shift,GaussianEulerPositiveScalingQuadrature.subst_source,Syn.shift] using hs.shift
  have rows : Γ ⊢[PRAAx] termsDistance f (multiplyBody g) N x y L (unit p) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,f,g,x,y,w,L,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerPositiveScalingIntegrand.subst_fixedData,subst_factor,subst_maximumCost,subst_pairT,GaussianCoefficientNameBounds.subst_unit,Syn.shift] using
      row_error (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift C)
        (Syn.shift E) (Syn.shift c) (Syn.shift d) hh.wk Prf.hyp0
  have he := hs.andE₂.andE₂.andE₁
  have hn := hs.andE₂.andE₂.andE₂.andE₁
  have en := positive_product E N he hn
  have finite := sum_distance f (multiplyBody g) N x y L (unit p) (unit_positive p) rows
  have weighted := GaussianRationalReciprocal.bounded_product _ _ C (E*N) (N*L) (unit p) en (unit_positive p)
    (weight_bound C E N he hn) finite
  have difference := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (weight C E N) _ _).eqSymm (.eqRefl _) (.eqRefl _) weighted
  have result : Γ ⊢[PRAAx] distanceBounded
      (quadrature GaussianEulerPositiveScalingQuadrature.evaluatorF p N a C E (fixedData z B c d))
      (qmul (weight C E N) (sum (multiplyBody g) N y)) (C*L) (E*unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ en (unit_positive p)) (positive_product _ _ he (unit_positive p))
      (le_of_eq_add (d := zero) (by ipra_ring)) difference
  have extracted : Γ ⊢[PRAAx] qmul (weight C E N) (sum (multiplyBody g) N y) ≐
      qmul w (quadrature GaussianEulerPositiveScalingIntegrand.evaluatorF p N a C E (fixedData z B c d)) :=
    (qmul_congr (.eqRefl _) (sum_multiply g w N x)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
        ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
          (GaussianReciprocalHorner.qmul_associative _ _ _)))
  exact distance_congr (.eqRefl _) extracted (.eqRefl _) (.eqRefl _) result

theorem original_scaled_quadrature (p q N z B a C E c d : PTm n) (hs : Γ ⊢[PRAAx] source B a E N c d) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerIntegrandName.evaluatorF p N (c*a) (c*C) (d*E) (GaussianEulerIntegrandName.fixedData z B))
      (qmul (fraction c d) (qmul (factor q z B c d)
        (quadrature GaussianEulerPositiveScalingIntegrand.evaluatorF q N a C E (fixedData z B c d))))
      (c*C*(unit q+(maximumCost N z B a C E c d+one)*unit p)) (d*E*unit p*unit q) := by
  have hd := hs.andE₂.andE₂.andE₂.andE₂.andE₂
  have he := hs.andE₂.andE₂.andE₁
  have de := positive_product _ _ hd he
  have old := GaussianEulerPositiveScalingQuadrature.original_quadrature_scaling p q N z B a C E c d hs
  have extraction := original_extraction q N z B a C E c d hs
  have scale : Γ ⊢[PRAAx] bounded (fraction c d) c d :=
    GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point c d hd).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded c d hd)
  have multiplied := GaussianRationalReciprocal.bounded_product _ _ c d (C*maximumCost N z B a C E c d) (E*unit q)
    hd (positive_product _ _ he (unit_positive q)) scale extraction
  have second := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (fraction c d) _ _).eqSymm (.eqRefl _) (.eqRefl _) multiplied
  have den := positive_product _ _ (positive_product _ _ de (unit_positive p)) (unit_positive q)
  have second' : Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction c d) (quadrature GaussianEulerPositiveScalingQuadrature.evaluatorF q N a C E (fixedData z B c d)))
      (qmul (fraction c d) (qmul (factor q z B c d)
        (quadrature GaussianEulerPositiveScalingIntegrand.evaluatorF q N a C E (fixedData z B c d))))
      (c*C*maximumCost N z B a C E c d*unit p) (d*E*unit p*unit q) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd (positive_product _ _ he (unit_positive q))) den
      (le_of_eq_add (d := zero) (by ipra_ring)) second
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den old second')

theorem actual_single_original_scale_factor_outside_finite_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 4) (var 5) (var 7) (var 2) (var 8) (var 9) ⟶ distanceBounded
      (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 2) (var 8*var 5) (var 8*var 6) (var 9*var 7)
        (GaussianEulerIntegrandName.fixedData (var 3) (var 4)))
      (qmul (fraction (var 8) (var 9)) (qmul (factor (var 1) (var 3) (var 4) (var 8) (var 9))
        (quadrature GaussianEulerPositiveScalingIntegrand.evaluatorF (var 1) (var 2) (var 5) (var 6) (var 7)
          (fixedData (var 3) (var 4) (var 8) (var 9)))))
      (var 8*var 6*(unit (var 1)+(maximumCost (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)+one)*unit (var 0)))
      (var 9*var 7*unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (original_scaled_quadrature _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingFactorExtraction
