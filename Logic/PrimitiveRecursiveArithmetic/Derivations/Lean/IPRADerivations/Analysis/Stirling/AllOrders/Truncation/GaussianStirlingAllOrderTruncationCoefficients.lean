import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsNames
import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingExpansionCoefficients

/-!
# Literal correction coefficients in the Bernoulli recurrence

The signed reciprocal degree converts the centered kernel to the
logarithmic remainder. Multiplying the actual mean by the
inverse-power primitive gives one literal correction term.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderTruncationCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BernoulliBounds (zint toZ_zint bint bden bden_pos bint_eq)
open GaussianStirlingAllOrderPanelPartsSolve (ratio inverseHigh coefficient_positive)
open GaussianStirlingAllOrderPanelPartsDensities (lowScalar)
open GaussianStirlingAllOrderPanelDerivative (signedMean meanNumerator degreeProduct)
open GaussianStirlingAllOrderCenteredBernoulli (factor)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderReciprocalWeightError (coefficient power)
open GaussianStirlingExpansionCoefficients (logCoefficient)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalArithmetic (multiply negative represents)
open RationalRepresentations (represents_multiply represents_negative)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalFiniteSum (canonical_equal)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sign (m : ℕ) : ℤ := (-1)^m
def scaleCode (m : ℕ) : PTm n := normalize (zint (sign m)) (num (2*m+2))
def coefficientNumerator (m : ℕ) : ℤ := ((2*m).factorial : ℤ)*bint (2*m+2) 0
def literalCoefficient (m : ℕ) : PTm n := normalize (zint (coefficientNumerator m)) (num (bden (2*m+2)))
def literalPower (m : ℕ) (A B : PTm n) : PTm n := fraction (power (2*m+1) B) (power (2*m+1) A)
def literalTerm (m : ℕ) (A B : PTm n) : PTm n := multiply (literalCoefficient m) (literalPower m A B)

theorem coefficient_value (m : ℕ) :
    (coefficientNumerator m : ℚ) = logCoefficient (2*m+1) * (bden (2*m+2) : ℚ) := by
  have odd : (2*m+1)%2=1 := by omega
  simp only [coefficientNumerator,Int.cast_mul,Int.cast_natCast,bint_eq,logCoefficient,if_pos odd,Nat.add_sub_cancel,Fin.val_zero]
  ring

@[simp] theorem subst_scaleCode {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (scaleCode m : PTm n) = (scaleCode m : PTm l) := by simp [scaleCode,zint]
@[simp] theorem subst_literalTerm {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (literalTerm m A B) = literalTerm m (Syn.subst σ A) (Syn.subst σ B) :=
  by simp [literalTerm,literalCoefficient,literalPower,power,zint]

private theorem scale_positive (m : ℕ) : Γ ⊢[PRAAx] le one (num (2*m+2) : PTm n) :=
  Foundations.NumeralPrimes.num_le (a := 1) (by omega)

theorem scale_ratio (m : ℕ) : Γ ⊢[PRAAx]
    multiply (scaleCode (m+1) : PTm n) (ratio (m+1) (2*m+2)) ≐ negative (scaleCode m) := by
  let d : PTm n := num (2*m+2)
  let e : PTm n := num (2*(m+1)+2)
  let h : PTm n := coefficient (2*m+2)
  let l : PTm n := num (degreeProduct (m+1))
  have hd := scale_positive (Γ := Γ) m
  have he := scale_positive (Γ := Γ) (m+1)
  have hh := coefficient_positive (Γ := Γ) (2*m+2) (by omega)
  have hh' := positive_product _ _ hh (le_refl one)
  have r : Γ ⊢[PRAAx] represents (ratio (m+1) (2*m+2))
      (ZT.ofNat one*ZT.ofNat l) (h*one) :=
    represents_multiply _ _ _ _ _ _ (fraction_represents _ _ hh) (fraction_represents _ _ (le_refl one))
  have rl := represents_multiply _ _ _ _ _ _ (normalize_preserves_value (zint (sign (m+1))) e he) r
  have rr := represents_negative _ _ _ (normalize_preserves_value (zint (sign m)) d hd)
  apply canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _) (RationalArithmetic.negative_guard _)
    rl rr (positive_product _ _ he hh') hd
  apply ZT.derive
  simp only [ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint]
  unfold l h d e coefficient GaussianStirlingAllOrderReciprocalTaylor.secondCoefficient degreeProduct sign
  ipra_simps
  rw [pow_succ]
  push_cast
  ring

theorem scale_mean_primitive (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    multiply (scaleCode m) (multiply (signedMean (m+1)) (primitive (2*m+2) A B)) ≐ literalTerm m A B := by
  let j := 2*m+1
  let v := 2*m+2
  let D : PTm n := num (bden v)
  let d : PTm n := num v
  let k : PTm n := num j
  let U := power j B
  let V := power j A
  have ej : 2*m+2-1=j := by unfold j; omega
  have hD : Γ ⊢[PRAAx] le one D := Foundations.NumeralPrimes.num_le (a := 1) (bden_pos v)
  have hV : Γ ⊢[PRAAx] le one V := GaussianFactorBudget.power_positive _ _ hA
  have hk : Γ ⊢[PRAAx] le one k := Foundations.NumeralPrimes.num_le (a := 1) (by unfold j; omega)
  have hd := scale_positive (Γ := Γ) m
  let u : ZT n := zint (-factor (m+1)*bint v 0)
  have ra : Γ ⊢[PRAAx] represents (signedMean (m+1)) u D := by
    unfold signedMean meanNumerator
    simp only [Nat.mul_add,Nat.mul_one]
    exact normalize_preserves_value u D hD
  have rb : Γ ⊢[PRAAx] represents (primitive (2*m+2) A B) (ZT.ofNat U) (k*V) := by
    simpa only [primitive,ej,j,k,U,V] using fraction_represents U (k*V) (positive_product _ _ hk hV)
  have r := represents_multiply _ _ _ _ _ _ ra rb
  have rl := represents_multiply _ _ _ _ _ _ (normalize_preserves_value (zint (sign m)) d hd) r
  have rr := represents_multiply _ _ _ _ _ _
    (normalize_preserves_value (zint (coefficientNumerator m)) D hD) (fraction_represents U V hV)
  apply canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _) (RationalArithmetic.multiply_guard _ _)
    rl rr (positive_product _ _ hd (positive_product _ _ hD (positive_product _ _ hk hV))) (positive_product _ _ hD hV)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint]
  unfold u coefficientNumerator factor sign d k j v D
  simp only [toZ_zint]
  rw [show 2*(m+1)=2*m+2 by omega]
  rw [show (2*m+2).factorial=(2*m+2)*(2*m+1)*(2*m).factorial by
    rw [show (2*m+2)=(2*m+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ (2*m)]
    ring]
  ipra_simps
  rw [pow_succ]
  push_cast
  have powerSign : ((-1 : Groth (Q Γ))^m)*(-1)^m = 1 := by
    rw [← mul_pow]
    simp
  dsimp only [v]
  linear_combination
    (2*(m : Groth (Q Γ))+2)*(2*(m : Groth (Q Γ))+1)*
      ((2*m).factorial : Groth (Q Γ))*(bint (2*m+2) 0 : Groth (Q Γ))*
      Groth.ι (Q.mk Γ U)*(bden (2*m+2) : Groth (Q Γ))*Groth.ι (Q.mk Γ V)*powerSign

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderTruncationCoefficients
