/-
The logarithm of the relative shift of the literal kept Barnes base powers.
The certified half disk controls the Mercator argument.
-/
import IPRADerivations.Analysis.GaussianBarnesCanonicalBaseProductShift
import IPRADerivations.Analysis.GaussianLocalLogarithmMultiplicativeIncrement
import IPRADerivations.Analysis.GaussianGammaWeierstrassApproximant
import IPRADerivations.Analysis.GaussianRationalInverseQuadraticAlgebra

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadRelativeLog

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianRationalHorner (qadd qmul ofGaussian qmul_canonical)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianRationalReciprocal (reciprocal normNumerator reciprocal_identity)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open ComplexLogarithmRemainder (add)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def relative (z h B N : PTm n) : PTm n :=
  qmul (reciprocal (powerProduct z B N))
    (qsub (powerProduct (add z h) B N) (powerProduct z B N))

def numerator (z h B N : PTm n) : PTm n := rawGaussian (relative z h B N)
def denominator (z h B N : PTm n) : PTm n := rawDen (relative z h B N)
def radius (z h B N : PTm n) : PTm n := GaussianL1.norm1 (numerator z h B N)

def source (z h B N : PTm n) : Fm PTm n :=
  le one (normNumerator (powerProduct z B N)) ⋏
  le (two*radius z h B N) (denominator z h B N)

def nameF : PR 2 := GaussianLocalLogarithmName.pointF

def data (z h B N : PTm n) : PTm n :=
  GaussianLocalLogarithmName.data (numerator z h B N) (radius z h B N) (denominator z h B N)

def expF : PR 2 := GaussianRadiusExponentialName.nameF nameF
def expData (z h B N : PTm n) : PTm n := GaussianRadiusExponentialName.data one (data z h B N)

@[simp] theorem subst_relative {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (relative z h B N) = relative (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [relative]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    (source z h B N).subst σ = source (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [source,numerator,denominator,radius]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (data z h B N) = data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [data,numerator,denominator,radius]

@[simp] theorem subst_expData {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (expData z h B N) = expData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [expData]

theorem local_source (z h B N : PTm n) (hs : Γ ⊢[PRAAx] source z h B N) : Γ ⊢[PRAAx]
    GaussianLocalLogarithmName.source (numerator z h B N) (radius z h B N) (denominator z h B N) :=
  .andI (raw_den_positive _) (.andI (GaussianL1.normSq_le_norm1_square _) hs.andE₂)

theorem regular (z h B N : PTm n) (hs : Γ ⊢[PRAAx] source z h B N) :
    Γ ⊢[PRAAx] pointCN nameF (data z h B N) :=
  GaussianLocalLogarithmName.name_regular _ _ _ (local_source z h B N hs)

theorem exp_input (z h B N : PTm n) (hs : Γ ⊢[PRAAx] source z h B N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input nameF one (data z h B N) :=
  GaussianExponentialRadiusIndependence.radius_one_input _ _
    (GaussianLocalLogarithmName.original_exponential_input _ _ _ (local_source z h B N hs))

theorem decoded (z h B N : PTm n) : Γ ⊢[PRAAx]
    ofGaussian (numerator z h B N) (denominator z h B N) ≐ relative z h B N :=
  GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)

theorem restore (z h B N : PTm n)
    (ha : Γ ⊢[PRAAx] le one (normNumerator (powerProduct z B N))) : Γ ⊢[PRAAx]
    qmul (qadd qone (relative z h B N)) (powerProduct z B N) ≐ powerProduct (add z h) B N := by
  let a := powerProduct z B N
  let b := powerProduct (add z h) B N
  let d := qsub b a
  let i := reciprocal a
  have ac : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a :=
    GaussianRationalFiniteProduct.product_canonical _ _ _
  have bc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical b :=
    GaussianRationalFiniteProduct.product_canonical _ _ _
  have tail : Γ ⊢[PRAAx] qmul a (qmul i d) ≐ d :=
    GaussianRationalInverseQuadraticAlgebra.cancel_nested_product a i d (qsub_canonical b a)
      (reciprocal_identity a ha)
  have head : Γ ⊢[PRAAx] qmul a qone ≐ a := GaussianReciprocalHorner.qmul_one_right a ac
  change Γ ⊢[PRAAx] qmul (qadd qone (qmul i d)) a ≐ b
  exact (qmul_commutative _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add a qone (qmul i d)).eqTrans
      ((qadd_congr head tail).eqTrans (GaussianRationalLinearProduct.add_sub_right a b bc)))

theorem exponential_cross (z h B N : PTm n) (hs : Γ ⊢[PRAAx] source z h B N) : Γ ⊢[PRAAx]
    crossEquivalent expF constantF (expData z h B N) (qadd qone (relative z h B N)) := by
  have e := GaussianLocalLogarithmMultiplicativeIncrement.exponential_base_cross _ _ _
    (local_source z h B N hs)
  have a : Γ ⊢[PRAAx] qadd qone (ofGaussian (numerator z h B N) (denominator z h B N)) ≐
      qadd qone (relative z h B N) := qadd_congr (.eqRefl _) (decoded z h B N)
  exact cross_trans expF constantF constantF _ _ _ e
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ a)

theorem exponential_restores (z h B N : PTm n) (hs : Γ ⊢[PRAAx] source z h B N) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF expF constantF) constantF
      (multiplyData expF constantF (expData z h B N) (powerProduct z B N))
      (powerProduct (add z h) B N) := by
  let y := qadd qone (relative z h B N)
  let x := powerProduct z B N
  have e : Γ ⊢[PRAAx] crossEquivalent (multiplyF expF constantF) (multiplyF constantF constantF)
      (multiplyData expF constantF (expData z h B N) x) (multiplyData constantF constantF y x) :=
    GaussianGammaAdjacentCutoff.multiply_cross expF constantF constantF constantF _ _ _ _
      (GaussianRadiusExponentialName.name_regular _ _ _ (exp_input z h B N hs))
      (constant_regular y) (constant_regular x) (constant_regular x)
      (exponential_cross z h B N hs) (cross_refl constantF x (constant_regular x))
  exact cross_trans _ _ _ _ _ _ e (cross_trans _ _ _ _ _ _
    (GaussianGammaWeierstrassApproximant.constant_product_cross y x)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (restore z h B N hs.andE₁)))

theorem actual_Barnes_kept_power_relative_log_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (multiplyF expF constantF) constantF
        (multiplyData expF constantF (expData (var 0) (var 1) (var 2) (var 3))
          (powerProduct (var 0) (var 2) (var 3)))
        (powerProduct (add (var 0) (var 1)) (var 2) (var 3))) :=
  closeUniv 4 (.impI (exponential_restores _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadRelativeLog
