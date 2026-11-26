import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetCosinePrimitive
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetOscillatoryMatrixCell

/-!
# Actual transposed columns approach the normalized cosine primitive

After transposition, each damping sample is constant over a column.
The rational time product is exactly the same when read from either
axis. The resulting column is the actual finite cosine primitive on
the unit interval, multiplied by the original outer length and the
damping sample, with only the pointwise product error.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryColumns

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentCosineLaplace (mean)
open GaussianBinetCosinePrimitive (cosineValue)
open GaussianBinetExponentialIntegralGrid (row exponent)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetImaginaryExponentialScale (exponent_scale coefficient_congr)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetOscillatoryRectangleTranspose (matrix data)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid sampleBody sampleData)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply)
open GaussianRationalFubini (column columnBody column_entry)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianReciprocalHorner (qadd_commutative qmul_associative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetExponentialIntegralGrid.evaluatorF
local notation "f" => sampleBody F
local notation "mF" => GaussianRationalQuadratureMean.body f f
local notation "dM" => GaussianRationalQuadratureMean.data

def imaginaryData (s : Bool) (p M A B T j N U : PTm n) : PTm n :=
  sampleData (p+N) M one one one (pairT (coefficient (A*(T*j)) (B*N) (polarity s)) ((U*T)*one))
def damping (p X Y D sign T j N R : PTm n) : PTm n := row (p+N) (qnegative (argument X Y D sign)) (R*T) (T*j) N

def columnTarget (j p M X Y D sign A B R U L N : PTm n) : PTm n :=
  let T := D*L
  qmul (damping p X Y D sign T j N R)
    (qmul (fraction A B) (cosineValue (p+N) (A*(T*j)) (B*N) (U*T) one M))

@[simp] theorem subst_polarity {m : ℕ} (σ : Fin n → PTm m) (s : Bool) :
    Syn.subst σ (polarity s : PTm n) = (polarity s : PTm m) := by cases s <;> simp [polarity,one]
@[simp] theorem subst_imaginaryData {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (p M A B T j N U : PTm n) :
    Syn.subst σ (imaginaryData s p M A B T j N U) = imaginaryData s (Syn.subst σ p) (Syn.subst σ M)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ T) (Syn.subst σ j) (Syn.subst σ N) (Syn.subst σ U) := by
  simp [imaginaryData,one]
@[simp] theorem subst_damping {m : ℕ} (σ : Fin n → PTm m) (p X Y D sign T j N R : PTm n) :
    Syn.subst σ (damping p X Y D sign T j N R) = damping (Syn.subst σ p) (Syn.subst σ X) (Syn.subst σ Y)
      (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ T) (Syn.subst σ j) (Syn.subst σ N) (Syn.subst σ R) := by
  simp [damping,GaussianLogGammaEulerRepresentation.subst_argument]

private theorem frequency_numerator (i M A B : PTm n) : Γ ⊢[PRAAx]
    tagNumerator (grid i M (B+zero) A B) ≐ A*i := by
  let t := grid i M (B+zero) A B
  have hn : Γ ⊢[PRAAx] fstT t ≐ A*i+B*M := (fst_pair _ _).eqTrans (by ipra_ring)
  have hd : Γ ⊢[PRAAx] sndT t ≐ B*M := snd_pair _ _
  exact (congrMonus hn hd).eqTrans (add_monus _ _)

private theorem sample_cast (r R R' x y : PTm n) (hr : Γ ⊢[PRAAx] R ≐ R') (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] GaussianBinetExponentialPanel.sample r x R ≐ GaussianBinetExponentialPanel.sample r y R' := by
  simpa only [GaussianBinetExponentialPanel.subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianBinetExponentialPanel.sample (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![r,x,R]) (σ' := ![r,y,R']) (fun j => by fin_cases j; exact .eqRefl r; exact h; exact hr)

theorem imaginary_cell (s : Bool) (i j p M A B T N U : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) :
    let t := grid i M (B+zero) A B
    Γ ⊢[PRAAx] row (p+N) (coefficient (tagNumerator t) (sndT t) (polarity s)) (U*T) (T*j) N ≐
      inst2 f i (imaginaryData s p M A B T j N U) := by
  let t := grid i M (B+zero) A B
  let C := U*T
  let v := coefficient (A*(T*j)) (B*N) (polarity s)
  have b : Γ ⊢[PRAAx] sndT t ≐ B*M := snd_pair _ _
  have hBM := positive_product _ _ hB hM
  have hB' : Γ ⊢[PRAAx] le one (sndT t) := le_congr (.eqRefl _) b.eqSymm hBM
  have hBN := positive_product _ _ hB hN
  have one' : Γ ⊢[PRAAx] C ≐ C*one := by dsimp only [C]; ipra_ring
  have en : Γ ⊢[PRAAx] coefficient (tagNumerator t*(T*j)) (sndT t*N) (polarity s) ≐
      coefficient ((A*(T*j))*(one*i)) ((B*N)*M) (polarity s) :=
    coefficient_congr s ((congrMul (frequency_numerator i M A B) (.eqRefl (T*j))).eqTrans (by ipra_ring))
      ((congrMul b (.eqRefl N)).eqTrans (by ipra_ring))
  have eq : Γ ⊢[PRAAx] exponent (coefficient (tagNumerator t) (sndT t) (polarity s)) (T*j) N ≐ exponent v (one*i) M :=
    (exponent_scale s _ _ _ _ hB' hN).eqTrans (en.eqTrans (exponent_scale s _ _ _ _ hBN hM).eqSymm)
  exact (sample_cast (p+N) C (C*one) _ _ one' eq).eqTrans
    (GaussianBinetExponentialIntegralGrid.cell_at i (p+N) v (C*one) one M).eqSymm

private theorem cell_error (i j p M X Y D sign A B R U L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le A (B*U)) (hi : Γ ⊢[PRAAx] le i M) (hj : Γ ⊢[PRAAx] le j N) :
    let T := D*L
    let d := data p M X Y D sign A B R U L N
    let a := imaginaryData true p M A B T j N U
    let b := imaginaryData false p M A B T j N U
    let e := damping p X Y D sign T j N R
    Γ ⊢[PRAAx] distanceBounded (inst2 (columnBody matrix) i (pairT j d))
      (inst2 (multiplyBody mF) i (pairT e (dM a b))) (num 10) (unit (p+N)) := by
  let T := D*L
  let d := data p M X Y D sign A B R U L N
  let a := imaginaryData true p M A B T j N U
  let b := imaginaryData false p M A B T j N U
  let e := damping p X Y D sign T j N R
  have actual := GaussianBinetOscillatoryMatrixCell.factor_error i j p M X Y D sign A B R U L N hz hB hM hN hA hi hj
  have qa := imaginary_cell true i j p M A B T N U hB hM hN
  have qb := imaginary_cell false i j p M A B T N U hB hM hN
  have rwMean : Γ ⊢[PRAAx] mean (inst2 f i b) (inst2 f i a) ≐ inst2 mF i (dM a b) :=
    (qmul_congr (.eqRefl _) (qadd_commutative _ _)).eqTrans (GaussianRationalQuadratureMean.entry f f i a b).eqSymm
  have right := (qmul_congr (.eqRefl e) ((qmul_congr (.eqRefl _) (qadd_congr qb qa)).eqTrans rwMean)).eqTrans
    (multiply_body_at mF e i (dM a b)).eqSymm
  exact distance_congr (column_entry matrix i j d).eqSymm right (.eqRefl _) (.eqRefl _) actual

private theorem outer_weight (A B M : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] weight A B M ≐ qmul (fraction A B) (weight one one M) := by
  have e : Γ ⊢[PRAAx] weight one one M ≐ fraction one M :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul M)
  exact ((qmul_congr (.eqRefl _) e).eqTrans
    ((GaussianEulerDampedTimeRate.fraction_product A B one M hB hM).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)))).eqSymm

theorem column_error (j p M X Y D sign A B R U L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le A (B*U)) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] distanceBounded (qmul (weight A B M) (column matrix j M (data p M X Y D sign A B R U L N)))
      (columnTarget j p M X Y D sign A B R U L N) (A*num 10) (B*unit (p+N)) := by
  let T := D*L
  let d := data p M X Y D sign A B R U L N
  let a := imaginaryData true p M A B T j N U
  let b := imaginaryData false p M A B T j N U
  let e := damping p X Y D sign T j N R
  let x := pairT j d
  let y := pairT e (dM a b)
  let H := unit (p+N)
  let w := weight A B M
  have rows : Γ ⊢[PRAAx] termsDistance (columnBody matrix) (multiplyBody mF) M x y (num 10) H := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) := by simpa [Δ,s,Syn.shift,Fm.shift] using hz.shift
    have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Syn.shift,Fm.shift] using hB.shift
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Syn.shift,Fm.shift] using hM.shift
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Syn.shift,Fm.shift] using hN.shift
    have as' : Δ ⊢[PRAAx] le (s A) (s B*s U) := by simpa [Δ,s,Syn.shift,Fm.shift] using hA.shift
    have js : Δ ⊢[PRAAx] le (s j) (s N) := by simpa [Δ,s,Syn.shift,Fm.shift] using hj.shift
    simpa only [T,d,a,b,e,x,y,H,s,Δ,Syn.shift,subst_imaginaryData,subst_damping,subst_pairT,PTm.subst_mul,PTm.subst_add,
      GaussianBinetOscillatoryRectangleTranspose.subst_data,GaussianRationalQuadratureMean.subst_data,
      GaussianCoefficientNameBounds.subst_unit,LeanProofs.IPRA.PTm.subst_num] using
      cell_error (var 0) (s j) (s p) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B) (s R) (s U) (s L) (s N)
        zs.wk bs.wk ms.wk ns.wk as'.wk (le_of_lt Prf.hyp0) js.wk
  let u := column matrix j M d
  let v := sum (multiplyBody mF) M y
  let m := sum mF M (dM a b)
  have hBM := positive_product _ _ hB hM
  have hH := unit_positive (Γ := Γ) (p+N)
  have du : Γ ⊢[PRAAx] distanceBounded u v (M*num 10) H := sum_distance _ _ _ _ _ _ _ hH rows
  have prod := bounded_product w _ A (B*M) (M*num 10) H hBM hH (weight_bound A B M hB hM) du
  have mul : Γ ⊢[PRAAx] distanceBounded (qmul w u) (qmul w v) (A*(M*num 10)) ((B*M)*H) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference w u v).eqSymm (.eqRefl _) (.eqRefl _) prod
  have reduce : Γ ⊢[PRAAx] qmul w v ≐ qmul e (qmul w m) :=
    (qmul_congr (.eqRefl _) (sum_multiply mF e M (dM a b))).eqTrans
      ((qmul_associative w e m).eqSymm.eqTrans ((qmul_congr (qmul_commutative w e) (.eqRefl _)).eqTrans (qmul_associative e w m)))
  have read : Γ ⊢[PRAAx] qmul w m ≐ qmul (fraction A B) (cosineValue (p+N) (A*(T*j)) (B*N) (U*T) one M) :=
    (qmul_congr (outer_weight A B M hB hM) (.eqRefl _)).eqTrans
      ((qmul_associative _ _ _).eqTrans (qmul_congr (.eqRefl _) (GaussianRationalQuadratureMean.left_mean f f M a b one one).eqSymm))
  exact distance_radius_mono _ _ (A*(M*num 10)) ((B*M)*H) (A*num 10) (B*H)
    (positive_product _ _ hBM hH) (positive_product _ _ hB hH)
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr (.eqRefl _) (reduce.eqTrans (qmul_congr (.eqRefl _) read)) (.eqRefl _) (.eqRefl _) mul)

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatoryColumns
