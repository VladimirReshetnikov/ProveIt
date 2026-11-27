import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativeParameterPath
import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.Compact.GaussianEulerLogarithmicCompactTaylor
import IPRADerivations.Analysis.Euler.Logarithms.Compact.GaussianEulerLogarithmicInputProperness
import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianEulerPowerShiftRate

/-!
# Actual compact Taylor estimates on the finite native parameter path

The original half-plane source supplies every native path certificate.
The increment h/(D*N) has radius 1/N and the actual logarithm guard is
paid by N. Exact rational path-step equality transports the temporary
R+2 client to the literal successor with its proved R+1 certificate.
Only auxiliary observation slack is removed, leaving the unchanged
interval weight and the genuine quadratic factor 1/N^2.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicPathCompactTaylor

open_ipra
open GaussianEulerDerivativeParameterPath (increment)
open GaussianEulerLogarithmicIntervalName (nameF data name_regular)
open GaussianEulerLogarithmicMultiplier (logRadius)
open GaussianEulerLogarithmicParameterIncrement (curvature)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A h D a C E T N i : PTm n) : Fm PTm n :=
  GaussianEulerDerivativeParameterPath.source z R B A h D ⋏
    (le one E ⋏ (le one a ⋏ (le (a+C) (E*T) ⋏ (lt i N ⋏ le (logRadius E T) N))))
def pathData (i j z R B h D N a C E T : PTm n) : PTm n :=
  data j (GaussianEulerDerivativeParameterPath.numerator z B h D N i) (R+one)
    (GaussianEulerDerivativeParameterPath.denominator B D N) a C E T
def point (p i j z R B h D N a C E T : PTm n) : PTm n := ap2 nameF p (pathData i j z R B h D N a C E T)
def model (q r i j z R B h D N a C E T : PTm n) : PTm n :=
  GaussianRationalHorner.qadd (point q i j z R B h D N a C E T)
    (GaussianRationalHorner.qmul (increment h D N) (point r i (succ j) z R B h D N a C E T))
def quadraticNumerator (j R C E T : PTm n) : PTm n := C*curvature j (R+one) E T
def quadraticDenominator (E N : PTm n) : PTm n := E*(N*N)
def numerator (p q r j R C E T N : PTm n) : PTm n :=
  GaussianNamedAffineRemainderRate.numerator (quadraticNumerator j R C E T) (quadraticDenominator E N) p q r
def denominator (p q r E N : PTm n) : PTm n := GaussianNamedAffineRemainderRate.denominator (quadraticDenominator E N) p q r

ipra_subst source
ipra_subst pathData

theorem count_positive (z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) : Γ ⊢[PRAAx] le one N := by
  have jpos : Γ ⊢[PRAAx] le one (logRadius E T) :=
    le_of_eq_add (d := E*(T+one)+num 24) (by unfold logRadius GaussianCompactLogarithmBounds.radius; ipra_ring)
  exact le_trans jpos hs.andE₂.andE₂.andE₂.andE₂.andE₂

theorem step_bound (z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) : Γ ⊢[PRAAx] bounded (increment h D N) one N := by
  have hd := hs.andE₁.andE₂.andE₁
  have native := GaussianEulerDerivativeParameterPath.increment_native_disk z R B A h D hs.andE₁
  have old := GaussianGammaEulerHead.fraction_disk h one D hd (le_congr (.eqRefl _) (by ipra_ring) native)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
    (GaussianEulerDerivativeParameterPath.increment_bound h D N one one hd (count_positive z R B A h D a C E T N i hs)
      (le_refl one) old)

theorem path_interval (l z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) (hl : Γ ⊢[PRAAx] le l N) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.intervalSource (GaussianEulerDerivativeParameterPath.numerator z B h D N l)
      (R+one) (GaussianEulerDerivativeParameterPath.denominator B D N) a C E T := by
  have path := GaussianEulerDerivativeParameterPath.path_source z R B A h D N l hs.andE₁ (count_positive z R B A h D a C E T N i hs) hl
  exact .andI (.andI path.andE₂.andE₁.andE₁ (.andI hs.andE₂.andE₁ path.andE₂.andE₁.andE₂))
    (.andI hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁)

theorem compact_step_source (z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicTaylorGrid.source (GaussianEulerDerivativeParameterPath.numerator z B h D N i)
      (R+one) (GaussianEulerDerivativeParameterPath.denominator B D N) a C E T h (D*N) one N :=
  .andI (path_interval i z R B A h D a C E T N i hs (le_of_lt hs.andE₂.andE₂.andE₂.andE₂.andE₁))
    (.andI (positive_product _ _ hs.andE₁.andE₂.andE₁ (count_positive z R B A h D a C E T N i hs))
      (.andI (count_positive z R B A h D a C E T N i hs)
        (.andI (le_congr (by ipra_ring) (.eqRefl _) hs.andE₂.andE₂.andE₂.andE₂.andE₂)
          (step_bound z R B A h D a C E T N i hs))))

theorem successor_alignment (p q j z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) : Γ ⊢[PRAAx]
    distanceBounded (point p (succ i) j z R B h D N a C E T)
      (GaussianEulerLogarithmicCompactTaylor.point q j
        (GaussianEulerParameterExponentialIncrement.shifted (GaussianEulerDerivativeParameterPath.numerator z B h D N i)
          (GaussianEulerDerivativeParameterPath.denominator B D N) h (D*N)) ((R+one)+one)
        (GaussianEulerDerivativeParameterPath.denominator B D N*(D*N)) a C E T)
      (unit p+unit q) (unit p*unit q) := by
  have npos := count_positive z R B A h D a C E T N i hs
  have next := path_interval (succ i) z R B A h D a C E T N i hs hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have shifted := GaussianEulerLogarithmicCompactTaylor.shifted_source _ _ _ _ _ _ _ _ _ _ _ (compact_step_source z R B A h D a C E T N i hs)
  have same := GaussianEulerDerivativeParameterPath.local_step_fraction z B h D N i
    hs.andE₁.andE₁.andE₂.andE₁.andE₁ hs.andE₁.andE₂.andE₁ npos
  exact GaussianEulerLogarithmicInputProperness.original_observations p q j _ _ _ _ _ _ _ _ _ _
    (.andI next (.andI shifted same.eqSymm))

theorem original_diagonal (p j z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) : Γ ⊢[PRAAx]
    distanceBounded (point p (succ i) j z R B h D N a C E T) (model p p i j z R B h D N a C E T)
      (quadraticNumerator j R C E T*unit p+num 14*quadraticDenominator E N) (quadraticDenominator E N*unit p) := by
  let Q := quadraticDenominator E N
  let V := unit p
  let DD := Q*V
  have npos := count_positive z R B A h D a C E T N i hs
  have qp : Γ ⊢[PRAAx] le one Q := positive_product _ _ hs.andE₂.andE₁ (positive_product _ _ npos npos)
  have den : Γ ⊢[PRAAx] le one DD := positive_product _ _ qp (unit_positive p)
  have first := distance_radius_mono _ _ _ _ (two*Q) DD (positive_product _ _ (unit_positive p) (unit_positive p)) den
    (le_of_eq_add (d := zero) (by dsimp only [DD,V]; ipra_ring)) (successor_alignment p p j z R B A h D a C E T N i hs)
  have second := GaussianNamedAffineRemainderRate.diagonal_at nameF nameF nameF _ _ _ _ _ _ _ p
    (GaussianEulerLogarithmicCompactTaylor.diagonal_envelope j
      (GaussianEulerDerivativeParameterPath.numerator z B h D N i) (R+one)
      (GaussianEulerDerivativeParameterPath.denominator B D N) a C E T h (D*N) one N
      (compact_step_source z R B A h D a C E T N i hs))
  have adjusted : Γ ⊢[PRAAx] distanceBounded
      (GaussianEulerLogarithmicCompactTaylor.point p j
        (GaussianEulerParameterExponentialIncrement.shifted (GaussianEulerDerivativeParameterPath.numerator z B h D N i)
          (GaussianEulerDerivativeParameterPath.denominator B D N) h (D*N)) ((R+one)+one)
        (GaussianEulerDerivativeParameterPath.denominator B D N*(D*N)) a C E T)
      (model p p i j z R B h D N a C E T)
      (quadraticNumerator j R C E T*V+num 12*Q) DD :=
    distance_congr (.eqRefl _) (.eqRefl _)
      (by unfold GaussianNamedLipschitzRate.diagonalNumerator GaussianEulerLogarithmicCompactTaylor.quadraticNumerator
            GaussianEulerLogarithmicCompactTaylor.quadraticDenominator
          dsimp only [quadraticNumerator,Q,quadraticDenominator,V]; ipra_ring) (.eqRefl _) second
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [Q,V]; ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ den first adjusted)

theorem diagonal_envelope (j z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) : Γ ⊢[PRAAx]
    GaussianNamedAffineRemainderRate.diagonalEnvelope nameF nameF nameF
      (pathData (succ i) j z R B h D N a C E T) (pathData i j z R B h D N a C E T)
      (pathData i (succ j) z R B h D N a C E T) (increment h D N)
      (quadraticNumerator j R C E T) (quadraticDenominator E N) (num 14) := by
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A)
      (Syn.shift h) (Syn.shift D) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) (Syn.shift i) :=
    by simpa only [Fm.shift,subst_source,Syn.shift] using hs.shift
  refine .allI ?_
  simpa [GaussianNamedAffineRemainderRate.diagonalEnvelope,GaussianNamedAffineRemainderRate.affine,
    GaussianNamedLipschitzRate.diagonalNumerator,GaussianNamedLipschitzRate.diagonalDenominator,
    point,model,quadraticNumerator,quadraticDenominator,Syn.shift] using
    original_diagonal (var 0) (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift h)
      (Syn.shift D) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) (Syn.shift i) hh

/-- Literal native path successor versus the actual previous-path compact
value and its actual order-successor slope, with three independent queries. -/
theorem original_observations (p q r j z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) : Γ ⊢[PRAAx]
    distanceBounded (point p (succ i) j z R B h D N a C E T) (model q r i j z R B h D N a C E T)
      (numerator p q r j R C E T N) (denominator p q r E N) := by
  have np := count_positive z R B A h D a C E T N i hs
  have here := path_interval i z R B A h D a C E T N i hs (le_of_lt hs.andE₂.andE₂.andE₂.andE₂.andE₁)
  have next := path_interval (succ i) z R B A h D a C E T N i hs hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have coefficient := GaussianCoefficientNameBounds.bounded_radius_mono (increment h D N) one N one one np (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) np) (step_bound z R B A h D a C E T N i hs)
  exact GaussianNamedAffineRemainderRate.independent_at nameF nameF nameF _ _ _ _ _ _ _ p q r
    (positive_product _ _ hs.andE₂.andE₁ (positive_product _ _ np np)) coefficient
    (name_regular _ _ _ _ _ _ _ _ next) (name_regular _ _ _ _ _ _ _ _ here) (name_regular _ _ _ _ _ _ _ _ here)
    (diagonal_envelope j z R B A h D a C E T N i hs)

/-- The identical bound in the literal adjacent-difference form used by
the original finite parameter telescope. -/
theorem original_difference_observations (p q r j z R B A h D a C E T N i : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A h D a C E T N i) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalMetric.qsub (point p (succ i) j z R B h D N a C E T) (point q i j z R B h D N a C E T))
      (GaussianRationalHorner.qmul (increment h D N) (point r i (succ j) z R B h D N a C E T))
      (numerator p q r j R C E T N) (denominator p q r E N) :=
  GaussianRationalReciprocal.bound_congr
    (GaussianEulerPowerShiftRate.displaced_difference _ _ _ (GaussianRationalHorner.qmul_canonical _ _)).eqSymm
    (.eqRefl _) (.eqRefl _) (original_observations p q r j z R B A h D a C E T N i hs)

theorem actual_original_subdivided_parameter_path_compact_Taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
    (source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15) ⟶
      distanceBounded (point (var 0) (succ (var 15)) (var 3) (var 4) (var 5) (var 6) (var 8) (var 9) (var 14)
        (var 10) (var 11) (var 12) (var 13))
        (model (var 1) (var 2) (var 15) (var 3) (var 4) (var 5) (var 6) (var 8) (var 9) (var 14)
          (var 10) (var 11) (var 12) (var 13))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 11) (var 12) (var 13) (var 14))
        (denominator (var 0) (var 1) (var 2) (var 12) (var 14))) :=
  closeUniv 16 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicPathCompactTaylor
