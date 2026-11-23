import IPRADerivations.Analysis.GaussianEulerSquareFactorObservation

/-!
# One fixed original factor outside the actual quadratic kernel grid

The retimed Jacobian and unfactored kernel keep the same original
numerical affine mesh. Every row uses one fixed original factor
observation. The source-only point comparison is aggregated by the
actual finite sum and weight, including zero width. All three original
observation precisions remain independent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareFactorExtraction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerSquareIntegrand (factorF factorData)
open GaussianEulerSquareKernel (doubled kernelF kernelData)
open GaussianEulerSquareFactorObservation (factorBound kernelBound leadingNumerator leadingDenominator)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalRiemannRefinement (termsDistance weight weight_bound sum_distance)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "J" => GaussianEulerSquareJacobianCompactName.evaluatorF
local notation "JD" => GaussianEulerSquareJacobianCompactName.fixedData
local notation "K" => GaussianEulerQuadraticKernelCompactName.evaluatorF
local notation "KD" => GaussianEulerPositiveScalingIntegrand.fixedData
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B c d a C E T N : PTm n) : Fm PTm n :=
  GaussianEulerQuadraticKernelCompactName.source z R B c d a C E T ⋏ le one N
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B c d a C E T N : PTm n) :
    (source z R B c d a C E T N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ c) (Syn.subst σ d)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ N) := by simp [source]
@[simp] theorem subst_factorData {m : ℕ} (σ : Fin n → PTm m) (z B c d : PTm n) :
    Syn.subst σ (factorData z B c d) = factorData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [factorData,GaussianEulerPositiveScalingConstant.scaleData]

theorem kernel_sample_at (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    ap3 K p (pairT a b) (KD z B c d) ≐ ap2 kernelF p (kernelData (doubled z B) B a b c d) := by
  have first : Γ ⊢[PRAAx] kernelData (doubled z B) B (fstT (pairT a b)) (sndT (pairT a b)) c d ≐
      kernelData (doubled z B) B a (sndT (pairT a b)) c d := by
    simpa only [GaussianEulerQuadraticKernelCompactName.subst_kernelData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (kernelData (Syn.shift (doubled z B)) (Syn.shift B) (var 0) (Syn.shift (sndT (pairT a b))) (Syn.shift c) (Syn.shift d)) (fst_pair a b)
  have second : Γ ⊢[PRAAx] kernelData (doubled z B) B a (sndT (pairT a b)) c d ≐ kernelData (doubled z B) B a b c d := by
    simpa only [GaussianEulerQuadraticKernelCompactName.subst_kernelData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (kernelData (Syn.shift (doubled z B)) (Syn.shift B) (Syn.shift a) (var 0) (Syn.shift c) (Syn.shift d)) (snd_pair a b)
  exact (GaussianEulerQuadraticKernelCompactName.evaluator_at p (pairT a b) z B c d).eqTrans
    (congrAp2 kernelF (.eqRefl _) (first.eqTrans second))

theorem grid_domain (i z R B c d a C E T N : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (a*N+C*i) (E*N) E T := by
  have ha := hs.andE₁.andE₁.andE₂.andE₁
  have hE := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  have he := hs.andE₁.andE₁.andE₂.andE₂
  have hn := positive_product _ _ ha hs.andE₂
  have hd := positive_product _ _ hE hs.andE₂
  have lowStart : Γ ⊢[PRAAx] le (E*N) (a*(E*N)) := le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (E*N) ha)
  have lowStep : Γ ⊢[PRAAx] le (a*(E*N)) (E*(a*N+C*i)) := le_of_eq_add (d := E*C*i) (by ipra_ring)
  have upperNode : Γ ⊢[PRAAx] le (a*N+C*i) ((a+C)*N) := by ipra_le 𝔞(C)*sl (le_of_lt hi)
  have upper : Γ ⊢[PRAAx] le (a*N+C*i) (T*(E*N)) := le_trans upperNode
    (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right N he))
  exact .andI (.andI (le_trans hn (le_add_right _ _)) hd) (.andI (le_trans lowStart lowStep) upper)

theorem row_error (i p q r z R B c d a C E T N : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded
      (inst2 (sampleBody J) i (sampleData p N a C E (JD z B c d T)))
      (inst2 (multiplyBody (sampleBody K)) i (pairT (ap2 factorF q (factorData z B c d)) (sampleData r N a C E (KD z B c d))))
      (leadingNumerator p q r (kernelBound R E T c) (factorBound z B c d)) (leadingDenominator p q r) := by
  have geom : Γ ⊢[PRAAx] GaussianEulerSquareTimeGeometry.source z R B E c d := .andI hs.andE₁.andE₁.andE₁ hs.andE₁.andE₂
  have original := GaussianEulerSquareFactorObservation.original_point_bound p q r z R B E T c d (a*N+C*i) (E*N) geom (grid_domain i z R B c d a C E T N hs hi)
  have left := sample_body_at (Γ := Γ) J i p N a C E (JD z B c d T)
  have right := (multiply_body_at (Γ := Γ) (sampleBody K) (ap2 factorF q (factorData z B c d)) i (sampleData r N a C E (KD z B c d))).eqTrans
    (qmul_congr (.eqRefl _) ((sample_body_at K i r N a C E (KD z B c d)).eqTrans (kernel_sample_at r z B _ _ c d)))
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) original

/-- The factor query q is the same on every actual finite row. -/
theorem original_same_grid_bound (p q r z R B c d a C E T N : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature J p N a C E (JD z B c d T))
      (qmul (ap2 factorF q (factorData z B c d)) (quadrature K r N a C E (KD z B c d)))
      (C*leadingNumerator p q r (kernelBound R E T c) (factorBound z B c d)) (E*leadingDenominator p q r) := by
  let f := sampleBody J
  let g := sampleBody K
  let x := sampleData p N a C E (JD z B c d T)
  let y := sampleData r N a C E (KD z B c d)
  let w := ap2 factorF q (factorData z B c d)
  let A := leadingNumerator p q r (kernelBound R E T c) (factorBound z B c d)
  let D := leadingDenominator p q r
  have hD := GaussianEulerSquareFactorObservation.denominator_positive (Γ := Γ) p q r
  have hE := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  have en := positive_product _ _ hE hs.andE₂
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift c) (Syn.shift d) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have rows : Γ ⊢[PRAAx] termsDistance f (multiplyBody g) N x (pairT w y) A D := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,f,g,x,y,w,A,D,GaussianCompactRiemannName.subst_sampleData,subst_factorData,
      GaussianEulerSquareJacobianCompactName.subst_fixedData,GaussianEulerPositiveScalingIntegrand.subst_fixedData,
      GaussianEulerSquareFactorObservation.subst_leadingNumerator,GaussianEulerSquareFactorObservation.subst_leadingDenominator,
      GaussianEulerSquareFactorObservation.subst_factorBound,GaussianEulerSquareFactorObservation.subst_kernelBound,subst_pairT,subst_ap2,Syn.shift] using
      row_error (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift r) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift c) (Syn.shift d)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) ss.wk Prf.hyp0
  have finite := sum_distance f (multiplyBody g) N x (pairT w y) A D hD rows
  have weighted := GaussianRationalReciprocal.bounded_product _ _ C (E*N) (N*A) D en hD (weight_bound C E N hE hs.andE₂) finite
  have raw := GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference (weight C E N) _ _).eqSymm (.eqRefl _) (.eqRefl _) weighted
  have short : Γ ⊢[PRAAx] distanceBounded (quadrature J p N a C E (JD z B c d T))
      (qmul (weight C E N) (sum (multiplyBody g) N (pairT w y))) (C*A) (E*D) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ en hD) (positive_product _ _ hE hD)
      (le_of_eq_add (d := zero) (by ipra_ring)) raw
  have extracted : Γ ⊢[PRAAx] qmul (weight C E N) (sum (multiplyBody g) N (pairT w y)) ≐ qmul w (quadrature K r N a C E (KD z B c d)) :=
    (qmul_congr (.eqRefl _) (sum_multiply g w N y)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
        ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans (GaussianReciprocalHorner.qmul_associative _ _ _)))
  exact distance_congr (.eqRefl _) extracted (.eqRefl _) (.eqRefl _) short

theorem original_same_query_bound (p z R B c d a C E T N : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature J p N a C E (JD z B c d T))
      (qmul (ap2 factorF p (factorData z B c d)) (quadrature K p N a C E (KD z B c d)))
      (C*(one+kernelBound R E T c+factorBound z B c d)) (E*unit p) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs.andE₁.andE₁.andE₁.andE₂.andE₁ (GaussianEulerSquareFactorObservation.denominator_positive p p p))
    (positive_product _ _ hs.andE₁.andE₁.andE₁.andE₂.andE₁ (unit_positive p))
    (le_of_eq_add (d := zero) (by unfold leadingNumerator leadingDenominator; ipra_ring))
    (original_same_grid_bound p p p z R B c d a C E T N hs)

theorem actual_single_factor_outside_quadratic_kernel_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      distanceBounded (quadrature J (var 0) (var 12) (var 8) (var 9) (var 10) (JD (var 3) (var 5) (var 6) (var 7) (var 11)))
        (qmul (ap2 factorF (var 1) (factorData (var 3) (var 5) (var 6) (var 7)))
          (quadrature K (var 2) (var 12) (var 8) (var 9) (var 10) (KD (var 3) (var 5) (var 6) (var 7))))
        (var 9*leadingNumerator (var 0) (var 1) (var 2) (kernelBound (var 4) (var 10) (var 11) (var 6)) (factorBound (var 3) (var 5) (var 6) (var 7)))
        (var 10*leadingDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 13 (.impI (original_same_grid_bound _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareFactorExtraction
