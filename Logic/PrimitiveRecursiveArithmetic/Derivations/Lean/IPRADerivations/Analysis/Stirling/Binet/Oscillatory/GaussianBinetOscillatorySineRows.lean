import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetOscillatoryZeroColumn

/-!
# All original transposed columns have the regularized sine value

Use the actual sine exponential quotient at positive time and its
exact removable value at the first grid point. The same cleared
uniform error applies throughout the original finite rectangle.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatorySineRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open GaussianBinetExponentialIntegral (numerator)
open GaussianBinetOscillatoryColumns (columnTarget column_error)
open GaussianBinetOscillatoryRectangleTranspose (matrix data)
open GaussianBinetOscillatorySineQuotient (target quotient_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFubini (column)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (weight)
open RationalArithmetic (select select_zero select_one)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (j p X Y D sign A B R U L N : PTm n) : PTm n :=
  select (sg j) (fraction A B) (target j p X Y D sign A B R U L N)
def numeratorBound (p M D A B U L N : PTm n) : PTm n :=
  A*num 10*M+B*(N*(two*numerator (p+N) (U*(D*L)) one M))

@[simp] theorem subst_cosineValue {m : ℕ} (σ : Fin n → PTm m) (p A B R T N : PTm n) :
    Syn.subst σ (GaussianBinetCosinePrimitive.cosineValue p A B R T N) =
      GaussianBinetCosinePrimitive.cosineValue (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B)
        (Syn.subst σ R) (Syn.subst σ T) (Syn.subst σ N) := by simp [GaussianBinetCosinePrimitive.cosineValue]
@[simp] theorem subst_endpoint {m : ℕ} (σ : Fin n → PTm m) (p A B R T : PTm n) :
    Syn.subst σ (GaussianBinetCosinePrimitive.endpoint p A B R T) =
      GaussianBinetCosinePrimitive.endpoint (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ T) := by
  simp [GaussianBinetCosinePrimitive.endpoint,one,two]
@[simp] theorem subst_columnTarget {m : ℕ} (σ : Fin n → PTm m) (j p M X Y D sign A B R U L N : PTm n) :
    Syn.subst σ (columnTarget j p M X Y D sign A B R U L N) = columnTarget (Syn.subst σ j) (Syn.subst σ p) (Syn.subst σ M)
      (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) := by simp [columnTarget,one]
@[simp] theorem subst_target {m : ℕ} (σ : Fin n → PTm m) (j p X Y D sign A B R U L N : PTm n) :
    Syn.subst σ (target j p X Y D sign A B R U L N) = target (Syn.subst σ j) (Syn.subst σ p)
      (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) := by
  simp [target,GaussianBinetOscillatorySineQuotient.quotient,one]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (j p X Y D sign A B R U L N : PTm n) :
    Syn.subst σ (value j p X Y D sign A B R U L N) = value (Syn.subst σ j) (Syn.subst σ p)
      (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) := by simp [value,sg]
@[simp] theorem subst_numeratorBound {m : ℕ} (σ : Fin n → PTm m) (p M D A B U L N : PTm n) :
    Syn.subst σ (numeratorBound p M D A B U L N) = numeratorBound (Syn.subst σ p) (Syn.subst σ M) (Syn.subst σ D)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) := by simp [numeratorBound,one,two]

theorem value_at_zero (j p X Y D sign A B R U L N : PTm n) (h : Γ ⊢[PRAAx] j ≐ zero) : Γ ⊢[PRAAx]
    value j p X Y D sign A B R U L N ≐ fraction A B :=
  select_zero _ _ _ ((congrMonus (.eqRefl one) (congrMonus (.eqRefl one) h)).eqTrans sg_zero)

theorem value_at_positive (j p X Y D sign A B R U L N : PTm n) (h : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx]
    value j p X Y D sign A B R U L N ≐ target j p X Y D sign A B R U L N :=
  select_one _ _ _ ((congrMonus (.eqRefl one) (congrMonus (.eqRefl one) (RationalIntegerNormalization.positive_form h))).eqTrans
    (sg_succ (pred j)))

theorem all_time_column_error (j p M X Y D sign A B R U L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] le one N) (hL : Γ ⊢[PRAAx] le one L) (hA : Γ ⊢[PRAAx] le A (B*U))
    (hj : Γ ⊢[PRAAx] le j N) (hC : Γ ⊢[PRAAx] le (U*(D*L)) M) :
    Γ ⊢[PRAAx] distanceBounded (qmul (weight A B M) (column matrix j M (data p M X Y D sign A B R U L N)))
      (value j p X Y D sign A B R U L N) (numeratorBound p M D A B U L N) ((B*M)*unit (p+N)) := by
  let r := p+N
  let G := N*(two*numerator r (U*(D*L)) one M)
  let Q := unit r
  let e := columnTarget j p M X Y D sign A B R U L N
  let w := value j p X Y D sign A B R U L N
  have hQ := unit_positive (Γ := Γ) r
  have h₁ := positive_product _ _ hB hQ
  have h₂ := positive_product _ _ hQ hM
  have hh := positive_product _ _ (positive_product _ _ hB hM) hQ
  have first := column_error j p M X Y D sign A B R U L N hz hB hM hN hA hj
  have last : Γ ⊢[PRAAx] distanceBounded e w G (Q*M) := by
    refine .orE (zero_or_succ j) ?_ ?_
    · have a := GaussianBinetOscillatoryZeroColumn.zero_column_at j p M X Y D sign A B R U L N Prf.hyp0 hB.wk hM.wk hN.wk
      have b := value_at_zero (Γ := (j ≐ zero) :: Γ) j p X Y D sign A B R U L N Prf.hyp0
      have zero' := GaussianRationalPowerDifference.distance_refl_zero (Γ := (j ≐ zero) :: Γ) (fraction A B) (Q*M) h₂.wk
      have increase : ((j ≐ zero) :: Γ) ⊢[PRAAx] le (zero*(Q*M)) (G*(Q*M)) :=
        le_congr (zero_mul _).eqSymm (.eqRefl _) (zero_le _)
      exact distance_congr a.eqSymm b.eqSymm (.eqRefl _) (.eqRefl _)
        (distance_radius_mono _ _ zero (Q*M) G (Q*M) h₂.wk h₂.wk increase zero')
    · have pos : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] le one j := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
      have b := value_at_positive j p X Y D sign A B R U L N pos
      exact distance_congr (.eqRefl _) b.eqSymm (.eqRefl _) (.eqRefl _)
        (quotient_error j p M X Y D sign A B R U L N hz.wk hB.wk hM.wk hN.wk hL.wk hA.wk pos hj.wk hC.wk)
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ (A*num 10) (B*Q) G (Q*M) h₁ h₂ first last
  have scale : Γ ⊢[PRAAx] le (((A*num 10)*(Q*M)+G*(B*Q))*((B*M)*Q))
      ((numeratorBound p M D A B U L N)*((B*Q)*(Q*M))) :=
    le_of_eq_add (d := zero) (by dsimp only [numeratorBound,G,Q,r]; ipra_ring)
  exact distance_radius_mono _ _ _ _ (numeratorBound p M D A B U L N) ((B*M)*Q)
    (positive_product _ _ h₁ h₂) hh scale joined

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatorySineRows
