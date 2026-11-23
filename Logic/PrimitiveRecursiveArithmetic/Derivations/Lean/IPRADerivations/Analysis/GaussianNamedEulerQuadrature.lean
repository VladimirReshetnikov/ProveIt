import IPRADerivations.Analysis.GaussianNamedEulerIntegrandParameterContinuity
import IPRADerivations.Analysis.GaussianNamedRationalApproximation
import IPRADerivations.Analysis.GaussianEulerIntegrandParameterContinuity
import IPRADerivations.Analysis.GaussianNamedGamma
import IPRADerivations.Analysis.GaussianEulerIntegralGammaIdentification

/-!
# The original Euler quadrature schedule on a named parameter

Keep the original cutoffs, cells, endpoint encoding and row precision.
The evaluator uses the genuine named Euler integrand at each row.
The sole extra clock controls which frozen rational input represents
the named parameter for the proof of agreement.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (source radius numerator denominator)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaCompactQuadratureBoundary (width width_bound exact_right_endpoint)
open GaussianEulerVaryingCutoffName (cells evaluationPrecision)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at)
open GaussianEulerIntegrandParameterContinuity (factor)
open GaussianRationalRiemannRefinement (termsDistance)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The literal quadrature uses every named evaluation at the original
precision and on the original grid. -/
def original (f : PR 2) (p x A : PTm n) : PTm n :=
  let R := radius f x
  let m := two*A
  quadrature (GaussianNamedEulerIntegrand.evaluatorF f) (evaluationPrecision p m R) (cells p m R)
    one (width p m R) (etaDen p m R) x

def parameterGain (p R m : PTm n) : PTm n := top p m R*factor R (etaDen p m R) (top p m R)

def clock (f : PR 2) (p x A : PTm n) : PTm n :=
  GaussianNamedGamma.clock f p x A+
    GaussianFastValueCut.exponent (two*parameterGain p (radius f x) (two*A)) p

def frozen (f : PR 2) (p x A : PTm n) : PTm n :=
  let r := clock f p x A
  ap2 GaussianEulerImproperName.nameF p
    (GaussianEulerImproperName.data (numerator f r x) (radius f x) (denominator f r x) (two*A))

/-- The same native parameter sample works for every row. -/
theorem frozen_margin (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source
      (numerator f (clock f p x A) x) (radius f x) (denominator f (clock f p x A) x) (two*A) :=
  .andI (GaussianNamedRightHalfPlane.actual_late_source f x A (clock f p x A) h
    (le_trans (GaussianNamedGamma.clock_margin f p x A) (le_add_right _ _)))
    (GaussianNameBounds.U_positive f x)

theorem parameter_budget (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] le (two*parameterGain p (radius f x) (two*A)*unit p) (unit (clock f p x A)) :=
  le_trans (GaussianFastValueCut.query_budget _ _)
    (GaussianExponentialReference.unit_monotone (le_add_left _ _))

theorem row_budget (p R A : PTm n) :
    Γ ⊢[PRAAx] le ((two*two)*top p A R*unit p) (unit (evaluationPrecision p A R)) := by
  let T := top p A R
  have ep : Γ ⊢[PRAAx] unit (p+num 2) ≐ unit p*(two*two) :=
    (pw_add two p (num 2)).eqTrans (congrMul (.eqRefl _)
      ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl two))))
  have later : Γ ⊢[PRAAx] le (p+num 2) (p+num 6) := le_of_eq_add (d := num 4) (by ipra_ring)
  have first := GaussianExponentialReference.unit_monotone later
  have rest := GaussianCompactRiemannName.precision_lower (Γ := Γ) p T
  exact le_trans (le_congr ((congrMul ep (.eqRefl T)).eqTrans (by ipra_ring))
    (.eqRefl _) (mul_le_mul_right T first)) (le_trans rest
      (GaussianExponentialReference.unit_monotone (le_of_eq_add (d := num 4)
        (by unfold GaussianCompactRiemannName.precision evaluationPrecision T; ipra_ring))))

private def comparisonRows (f : PR 2) (p x A : PTm n) : Fm PTm n :=
  let r := clock f p x A
  let R := radius f x
  let m := two*A
  let q := evaluationPrecision p m R
  let M := cells p m R
  let C := width p m R
  let E := etaDen p m R
  let T := top p m R
  let z := GaussianEulerIntegrandName.fixedData (numerator f r x) (denominator f r x)
  termsDistance (sampleBody (GaussianNamedEulerIntegrand.evaluatorF f)) (sampleBody GaussianEulerIntegrandName.evaluatorF)
    M (sampleData q M one C E x) (sampleData q M one C E z)
    (rateNumerator (factor R E T*one) (unit r) q q) (rateDenominator (unit r) q q)

private theorem original_grid_from_rows (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] comparisonRows f p x A) :
    Γ ⊢[PRAAx] distanceBounded (original f p x A) (frozen f p x A) one (unit p) := by
  let r := clock f p x A
  let R := radius f x
  let m := two*A
  let E := etaDen p m R
  let C := width p m R
  let T := top p m R
  let q := evaluationPrecision p m R
  let M := cells p m R
  let K := factor R E T
  let U := unit r
  let V := unit q
  let W := unit p
  let a := rateNumerator (K*one) U q q
  let d := rateDenominator U q q
  let z := GaussianEulerIntegrandName.fixedData (numerator f r x) (denominator f r x)
  have hE : Γ ⊢[PRAAx] le one E := eta_den_positive p m R
  have hM : Γ ⊢[PRAAx] le one M := GaussianCompactRiemannName.mesh_positive _ _ _
  have hd : Γ ⊢[PRAAx] le one d := denominator_positive _ _ _ (unit_positive r)
  have rows := GaussianCompactScalarMajorant.common_mesh_distance
    (sampleBody (GaussianNamedEulerIntegrand.evaluatorF f)) (sampleBody GaussianEulerIntegrandName.evaluatorF)
    M (sampleData q M one C E x) (sampleData q M one C E z) C E a d hM hE hd h
  have out := GaussianEulerImproperName.actual_sampler (Γ := Γ) p (numerator f r x) R (denominator f r x) m
  have whole : Γ ⊢[PRAAx] distanceBounded (original f p x A) (frozen f p x A) (C*a) (E*d) :=
    distance_congr (.eqRefl _) out.eqSymm (.eqRefl _) (.eqRefl _) rows
  have first : Γ ⊢[PRAAx] le (two*T*K*W) U :=
    le_congr (by dsimp only [W,K,T,E,parameterGain]; ipra_ring) (.eqRefl _) (parameter_budget f p x A)
  have second : Γ ⊢[PRAAx] le ((two*two)*T*W) V := row_budget p R m
  have twoHalves := add_le_add₂ (mul_le_mul_right (V*V) first) (mul_le_mul_right (U*V) second)
  have heightBudget : Γ ⊢[PRAAx] le (T*a*W) d :=
    RationalValueBounds.positive_cancel RationalAlgebra.two_positive
      (le_congr (by dsimp only [a,V,rateNumerator]; ipra_ring)
        (by dsimp only [d,V,rateDenominator]; ipra_ring) twoHalves)
  have scaleWidth := mul_le_mul_right (a*W) (width_bound (Γ := Γ) p m R)
  have scaleBound := mul_le_mul_right E heightBudget
  have weighted : Γ ⊢[PRAAx] le ((C*a)*W) (T*a*W*E) :=
    le_congr (by dsimp only [C]; ipra_ring) (by dsimp only [T,E]; ipra_ring) scaleWidth
  have enough : Γ ⊢[PRAAx] le ((C*a)*W) (one*(E*d)) :=
    le_trans weighted (le_congr (.eqRefl _) (by ipra_ring) scaleBound)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE hd) (unit_positive p) enough whole


@[simp] theorem subst_original {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x A : PTm n) :
    Syn.subst σ (original f p x A) = original f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ A) := by
  simp [original,width,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]

@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x A : PTm n) :
    Syn.subst σ (clock f p x A) = clock f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ A) := by
  simp [clock,parameterGain,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]

private theorem cell (f : PR 2) (i p x A : PTm n)
    (h : Γ ⊢[PRAAx] source f x A) (hi : Γ ⊢[PRAAx] lt i (cells p (two*A) (radius f x))) :
    Γ ⊢[PRAAx]
      let r := clock f p x A
      let R := radius f x
      let m := two*A
      let q := evaluationPrecision p m R
      let M := cells p m R
      let C := width p m R
      let E := etaDen p m R
      let T := top p m R
      let z := GaussianEulerIntegrandName.fixedData (numerator f r x) (denominator f r x)
      distanceBounded
        (inst2 (sampleBody (GaussianNamedEulerIntegrand.evaluatorF f)) i (sampleData q M one C E x))
        (inst2 (sampleBody GaussianEulerIntegrandName.evaluatorF) i (sampleData q M one C E z))
        (rateNumerator (factor R E T*one) (unit r) q q) (rateDenominator (unit r) q q) := by
  let r := clock f p x A
  let R := radius f x
  let m := two*A
  let q := evaluationPrecision p m R
  let M := cells p m R
  let C := width p m R
  let E := etaDen p m R
  let T := top p m R
  let z := numerator f r x
  let B := denominator f r x
  let a := M+C*i
  let b := E*M
  let F := GaussianNamedEulerIntegrand.evaluatorF f
  let G := GaussianEulerIntegrandName.evaluatorF
  have hM : Γ ⊢[PRAAx] le one M := GaussianCompactRiemannName.mesh_positive _ _ _
  have hE : Γ ⊢[PRAAx] le one E := eta_den_positive p m R
  have hend : Γ ⊢[PRAAx] le (one+C) (E*T) :=
    le_congr (exact_right_endpoint p m R).eqSymm (.eqRefl _) (le_refl _)
  have domain := GaussianBetaKernelGridComparison.grid_domain i M C E T hM hE (le_of_lt hi) hend
  have native := (frozen_margin f p x A h).andE₁.andE₂.andE₁
  have src : Γ ⊢[PRAAx] GaussianNamedEulerIntegrandParameterContinuity.input f x z B E T a b one (unit r) :=
    .andI h.andE₁ (.andI (.andI native.andE₁ (.andI hE native.andE₂))
      (.andI domain (.andI (unit_positive r) (GaussianNamedRationalApproximation.frozen_constant_rate f x r h.andE₁))))
  have close := GaussianNamedEulerIntegrandParameterContinuity.original_observations f q q x z B E T a b one (unit r) src
  have grid : Γ ⊢[PRAAx] GaussianCompactRiemannName.grid i M one C E ≐ pairT a b :=
    congrPairT (by dsimp only [a]; ipra_ring) (.eqRefl b)
  have left := (sample_body_at F i q M one C E x).eqTrans
    (congrAp3 F (.eqRefl q) grid (.eqRefl x))
  have right := (sample_body_at G i q M one C E (GaussianEulerIntegrandName.fixedData z B)).eqTrans
    (congrAp3 G (.eqRefl q) grid (.eqRefl _))
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) close

private theorem original_rows (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] comparisonRows f p x A := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift A) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedRightHalfPlane.subst_source] using h.shift
  simpa [comparisonRows,termsDistance,Syn.shift,width,etaDen,top,
    GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient] using
    cell f (var 0) (Syn.shift p) (Syn.shift x) (Syn.shift A) hs.wk Prf.hyp0

theorem original_grid_comparison (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (original f p x A) (frozen f p x A) one (unit p) :=
  original_grid_from_rows f p x A (original_rows f p x A h)


/-- Compare the actual named grid to Gamma before retiming the integral. -/
theorem original_diagonal (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (original f p x A)
      (ap2 (GaussianNamedGamma.nameF f) p (GaussianNamedGamma.data x A)) (num 4) (unit p) := by
  let k := succ p
  let r := clock f p x A
  let t := GaussianNamedGamma.clock f p x A
  let R := radius f x
  let m := two*A
  let z := numerator f r x
  let B := denominator f r x
  let w := numerator f t x
  let D := denominator f t x
  let U := unit p
  let V := unit k
  let I := original f p x A
  let J := frozen f p x A
  let G := ap2 gammaF k (gammaData z R B m)
  let H := GaussianNamedGamma.sample f p x A
  have hp : Γ ⊢[PRAAx] le one U := unit_positive p
  have hk : Γ ⊢[PRAAx] le one V := unit_positive k
  have dp : Γ ⊢[PRAAx] V ≐ U*two := pw_succ two p
  have hn := frozen_margin f p x A h
  have left : Γ ⊢[PRAAx] distanceBounded I J two V :=
    distance_radius_mono _ _ _ _ _ _ hp hk
      (le_congr (one_mul V).eqSymm (mul_comm _ _) (le_congr dp.eqSymm (.eqRefl _) (le_refl _)))
      (original_grid_comparison f p x A h)
  have old := cross_at _ _ _ _ p k
    (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B m hn)
  have budget : Γ ⊢[PRAAx] (U+V)*V ≐ num 3*(U*V) :=
    (congrMul (congrAdd (.eqRefl U) dp) (.eqRefl V)).eqTrans (by ipra_ring)
  have compare : Γ ⊢[PRAAx] le ((U+V)*V) (num 3*(U*V)) :=
    le_congr budget.eqSymm (.eqRefl _) (le_refl _)
  have middle : Γ ⊢[PRAAx] distanceBounded J G (num 3) V :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hk) hk compare old
  have cap := GaussianNamedGamma.clock_demand f p x A k (le_refl (Γ := Γ) k)
  have close := GaussianNamedGamma.input_observations f x r t
    (GaussianGammaHalfPlaneInputContinuity.modulus k R m) h.andE₁ (le_trans cap (le_add_right _ _)) cap
  have wSource := GaussianNamedRightHalfPlane.actual_late_source f x A t h
    (GaussianNamedGamma.clock_margin f p x A)
  have mixed := GaussianGammaHalfPlaneInputContinuity.original_gamma_observations k k k z w R B D m hn
    (.andI wSource (GaussianNameBounds.U_positive f x)) close
  have right : Γ ⊢[PRAAx] distanceBounded G H (num 3) V :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hk) hk
      (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,V]; ipra_ring)) mixed
  have sum := distance_triangle_same I G H (two+num 3) (num 3) V hk
    (distance_triangle_same I J G two (num 3) V hk left middle) right
  have e : Γ ⊢[PRAAx] (two+num 3+num 3)*U ≐ num 4*V :=
    (by ipra_ring : Γ ⊢[PRAAx] (two+num 3+num 3)*U ≐ num 4*(U*two)).eqTrans
      (congrMul (.eqRefl _) dp.eqSymm)
  have final : Γ ⊢[PRAAx] distanceBounded I H (num 4) U :=
    distance_radius_mono _ _ _ _ _ _ hk hp (le_congr e.eqSymm (.eqRefl _) (le_refl _)) sum
  exact distance_congr (.eqRefl _) (GaussianNamedGamma.name_at f p x A).eqSymm (.eqRefl _) (.eqRefl _) final

def retimed (p : PTm n) : PTm n := p+num 3
def body (f : PR 2) : PTm 2 := original f (retimed (var 0)) (fstT (var 1)) (sndT (var 1))
def nameF (f : PR 2) : PR 2 := PTm.toPR (body f)

@[simp] theorem subst_retimed {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (retimed p) = retimed (Syn.subst σ p) := by simp [retimed]

theorem name_at (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (GaussianNamedGamma.data x A) ≐ original f (retimed p) x A := by
  let a := GaussianNamedGamma.data x A
  have step : Γ ⊢[PRAAx] ap2 (nameF f) p a ≐ original f (retimed p) (fstT a) (sndT a) := by
    simpa only [nameF,body,ap2,subst_original,subst_retimed,Syn.subst_var,subst_fstT,subst_sndT,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (body f) ![p,a]
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (original f (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![retimed p,fstT a,sndT a]) (σ' := ![retimed p,x,A])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)
  exact step.eqTrans (by simpa only [subst_original,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using eq)

theorem independent_observations (f : PR 2) (p q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (GaussianNamedGamma.data x A))
      (ap2 (GaussianNamedGamma.nameF f) q (GaussianNamedGamma.data x A))
      (unit p+unit q) (unit p*unit q) := by
  let t := retimed p
  let H := GaussianNamedGamma.nameF f
  let a := GaussianNamedGamma.data x A
  let U := unit p
  let V := unit q
  let W := unit t
  have eq : Γ ⊢[PRAAx] W ≐ U*num 8 :=
    (pw_add two p (num 3)).eqTrans (congrMul (.eqRefl _) (by
      exact (pw_succ two (num 2)).eqTrans ((congrMul
        ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl two))) (.eqRefl two)).eqTrans (by ipra_ring))))
  have cap : Γ ⊢[PRAAx] le (num 5*U) W :=
    le_of_eq_add (d := num 3*U) (eq.eqTrans (by ipra_ring))
  have pos : Γ ⊢[PRAAx] le one (W*V) := positive_product _ _ (unit_positive t) (unit_positive q)
  have left := distance_radius_mono _ _ _ _ (num 4*V) (W*V) (unit_positive t) pos
    (le_of_eq_add (d := zero) (by ipra_ring)) (original_diagonal f t x A h)
  have right := GaussianNameEquivalence.point_at H a t q (GaussianNamedGamma.name_regular f x A h)
  have total := distance_triangle_same (original f t x A) (ap2 H t a) (ap2 H q a) (num 4*V) (W+V) (W*V) pos left right
  have bound := add_le_add₂ (mul_le_mul_right (V*V) cap) (le_refl (Γ := Γ) (W*U*V))
  have final : Γ ⊢[PRAAx] distanceBounded (original f t x A) (ap2 H q a) (U+V) (U*V) :=
    distance_radius_mono _ _ _ _ _ _ pos (positive_product _ _ (unit_positive p) (unit_positive q))
      (le_congr (by ipra_ring) (by ipra_ring) bound) total
  exact distance_congr (name_at f p x A).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) final

theorem original_named_Euler_integral_is_Gamma (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (GaussianNamedGamma.nameF f)
      (GaussianNamedGamma.data x A) (GaussianNamedGamma.data x A) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedRightHalfPlane.subst_source] using h.shift.shift
  simpa only [Syn.shift,GaussianNamedGamma.subst_data] using
    independent_observations f (var 1) (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) hs

theorem name_regular (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] pointCN (nameF f) (GaussianNamedGamma.data x A) := by
  have cross := original_named_Euler_integral_is_Gamma f x A h
  exact cross_trans _ _ _ _ _ _ cross (cross_symm _ _ _ _ cross)

theorem original_Euler_integral_is_Gamma_at_fixed_complex_name_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ crossEquivalent (nameF f) (GaussianNamedGamma.nameF f)
        (GaussianNamedGamma.data (var 0) (var 1)) (GaussianNamedGamma.data (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_named_Euler_integral_is_Gamma f _ _ Prf.hyp0))

theorem original_named_Euler_improper_quadrature_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ pointCN (nameF f) (GaussianNamedGamma.data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular f _ _ Prf.hyp0))

theorem original_named_Euler_improper_quadrature_program_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap2 (nameF f) (var 0) (GaussianNamedGamma.data (var 1) (var 2)) ≐ original f (retimed (var 0)) (var 1) (var 2)) :=
  closeUniv 3 (name_at f _ _ _)

end LeanProofs.IPRA.Analysis.GaussianNamedEulerQuadrature
