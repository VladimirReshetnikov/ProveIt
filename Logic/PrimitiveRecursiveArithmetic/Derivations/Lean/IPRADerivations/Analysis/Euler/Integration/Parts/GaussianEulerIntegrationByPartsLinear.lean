import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveLinearStep
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFirstOrderProductError
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayIncrement

/-!
# The exact original Euler linear term for integration by parts

The actual power and decay observations have their original first-order
increments. Multiplication by rational time produces the linear term
`dt * F(t) * (z/B - t)`. This is the operator whose finite telescope
gives z times the Euler integral minus the next time moment. All
observations and linear increments are literal original program terms.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsLinear

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (coefficient decayF decayData)
open GaussianEulerPowerIncrement (point slopeTerm)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qmul canonical qmul_canonical ofGaussian ofGaussian_canonical)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalCoefficientScaling (qmul_add)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def decay (p a b : PTm n) : PTm n := ap2 decayF p (decayData a b)
def originalProduct (p z B a b : PTm n) : PTm n := qmul (point p z B a b) (decay p a b)
def primitive (p z B a b : PTm n) : PTm n := qmul (fraction a b) (originalProduct p z B a b)
def decayLinear (p a b c : PTm n) : PTm n := qmul (decay p a b) (qnegative (fraction c b))
def productLinear (p z B a b c : PTm n) : PTm n :=
  GaussianRationalFirstOrderProductError.linearPart (point p z B a b) (decay p a b)
    (slopeTerm p z B a b c) (decayLinear p a b c)
def linear (p z B a b c : PTm n) : PTm n := qadd
  (qmul (originalProduct p z B a b) (fraction c b)) (qmul (fraction a b) (productLinear p z B a b c))
def cell (p z B a b c : PTm n) : PTm n :=
  qmul (fraction c b) (qmul (originalProduct p z B a b) (qsub (ofGaussian z B) (fraction a b)))

@[simp] theorem subst_decay {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (decay p a b) = decay (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by simp [decay]
@[simp] theorem subst_originalProduct {m : ℕ} (σ : Fin n → PTm m) (p z B a b : PTm n) :
    Syn.subst σ (originalProduct p z B a b) = originalProduct (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [originalProduct,point]
@[simp] theorem subst_primitive {m : ℕ} (σ : Fin n → PTm m) (p z B a b : PTm n) :
    Syn.subst σ (primitive p z B a b) = primitive (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [primitive]
@[simp] theorem subst_decayLinear {m : ℕ} (σ : Fin n → PTm m) (p a b c : PTm n) :
    Syn.subst σ (decayLinear p a b c) = decayLinear (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) := by simp [decayLinear]
@[simp] theorem subst_productLinear {m : ℕ} (σ : Fin n → PTm m) (p z B a b c : PTm n) :
    Syn.subst σ (productLinear p z B a b c) = productLinear (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) := by simp [productLinear,slopeTerm,point]
@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (p z B a b c : PTm n) :
    Syn.subst σ (linear p z B a b c) = linear (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) := by simp [linear]
@[simp] theorem subst_cell {m : ℕ} (σ : Fin n → PTm m) (p z B a b c : PTm n) :
    Syn.subst σ (cell p z B a b c) = cell (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) := by simp [cell]

private theorem exchange (x y a : PTm n) : Γ ⊢[PRAAx] qmul (qmul x a) y ≐ qmul (qmul x y) a :=
  (qmul_associative x a y).eqTrans ((qmul_congr (.eqRefl x) (qmul_commutative a y)).eqTrans (qmul_associative x y a).eqSymm)

theorem original_product_linear (p z B a b c : PTm n) : Γ ⊢[PRAAx]
    productLinear p z B a b c ≐ qmul (originalProduct p z B a b)
      (qsub (qmul (coefficient z B) (fraction c a)) (fraction c b)) :=
  (qadd_congr (exchange _ _ _) (qmul_associative _ _ _).eqSymm).eqTrans
    (qmul_add (originalProduct p z B a b) (qmul (coefficient z B) (fraction c a)) (qnegative (fraction c b))).eqSymm

theorem original_ratio_time (a b c : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qmul (fraction c a) (fraction a b) ≐ fraction c b :=
  (qmul_congr (.eqRefl _) (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring))).eqTrans
    ((GaussianBetaPrimitiveLinearStep.argument_ratio_step a b c one ha hb (le_refl one)).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring)))

theorem coefficient_plus_one (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd qone (coefficient z B) ≐ ofGaussian z B :=
  GaussianRationalLinearProduct.add_sub_right qone _ (ofGaussian_canonical _ _ hB)

private theorem inner_linear (K V U F H : PTm n) (hH : Γ ⊢[PRAAx] canonical H)
    (hUF : Γ ⊢[PRAAx] qmul F U ≐ H) (hK : Γ ⊢[PRAAx] qadd qone K ≐ V) : Γ ⊢[PRAAx]
    qadd H (qmul U (qsub (qmul K F) H)) ≐ qmul H (qsub V U) := by
  have first : Γ ⊢[PRAAx] qmul U (qmul K F) ≐ qmul K H :=
    (qmul_commutative U (qmul K F)).eqTrans ((qmul_associative K F U).eqTrans (qmul_congr (.eqRefl _) hUF))
  have sum : Γ ⊢[PRAAx] qadd H (qmul K H) ≐ qmul H V :=
    (qadd_congr (qmul_one_right H hH).eqSymm (qmul_commutative K H)).eqTrans
      ((qmul_add H qone K).eqSymm.eqTrans (qmul_congr (.eqRefl _) hK))
  have distributed : Γ ⊢[PRAAx] qmul U (qsub (qmul K F) H) ≐ qsub (qmul K H) (qmul H U) :=
    (GaussianRationalRoundedPower.multiplication_difference U (qmul K F) H).eqSymm.eqTrans (qsub_congr first (qmul_commutative U H))
  exact (qadd_congr (.eqRefl H) distributed).eqTrans
    ((qadd_associative H (qmul K H) (qnegative (qmul H U))).eqSymm.eqTrans
      ((qsub_congr sum (.eqRefl _)).eqTrans (GaussianRationalRoundedPower.multiplication_difference H V U)))

/-- The actual original first-order terms bind to the Euler
integration-by-parts operator, before taking a mesh or endpoint limit. -/
theorem original_linear_is_cell (p z B a b c : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    linear p z B a b c ≐ cell p z B a b c := by
  let J := originalProduct p z B a b
  let K := coefficient z B
  let V := ofGaussian z B
  let U := fraction a b
  let F := fraction c a
  let H := fraction c b
  have second : Γ ⊢[PRAAx] qmul U (productLinear p z B a b c) ≐ qmul J (qmul U (qsub (qmul K F) H)) :=
    (qmul_congr (.eqRefl U) (original_product_linear p z B a b c)).eqTrans
      ((qmul_commutative U (qmul J (qsub (qmul K F) H))).eqTrans
        ((qmul_associative J (qsub (qmul K F) H) U).eqTrans (qmul_congr (.eqRefl _) (qmul_commutative _ _))))
  have shaped : Γ ⊢[PRAAx] linear p z B a b c ≐ qmul J (qadd H (qmul U (qsub (qmul K F) H))) :=
    (qadd_congr (.eqRefl _) second).eqTrans (qmul_add J H (qmul U (qsub (qmul K F) H))).eqSymm
  have inner := inner_linear K V U F H (ofGaussian_canonical _ _ hb) (original_ratio_time a b c ha hb) (coefficient_plus_one z B hB)
  exact shaped.eqTrans ((qmul_congr (.eqRefl _) inner).eqTrans
    ((qmul_associative J H (qsub V U)).eqSymm.eqTrans
      ((qmul_congr (qmul_commutative J H) (.eqRefl _)).eqTrans (qmul_associative H J (qsub V U)))))

theorem original_Euler_integration_by_parts_linear_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 2) ⋏ (le one (var 3) ⋏ le one (var 4))) ⟶
      linear (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ cell (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (original_linear_is_cell _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsLinear
