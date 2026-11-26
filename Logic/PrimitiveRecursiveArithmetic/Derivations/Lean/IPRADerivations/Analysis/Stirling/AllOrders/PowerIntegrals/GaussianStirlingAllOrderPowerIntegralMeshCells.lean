import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderPowerIntegralStride
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsFinite

/-!
# Antiderivative bounds on the original reciprocal-power grid

A stride in the integer numerator at common denominator B·M
corresponds to one original mesh cell of width 1/M. The scaled
antiderivative and the two endpoint samples are canonical rational codes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralMeshCells

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.Foundations.NumeralPrimes (num_le)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianFactorBudget (power_positive)
open GaussianRationalL1 (nonnegative_of_representation)
open GaussianStirlingAllOrderPowerIntegralStride (strideSample potential stride_brackets)
open GaussianStirlingAllOrderReciprocalWeightError (power weight)
open GaussianStirlingAllOrderReciprocalGridError (gridDen)
open GaussianStirlingAllOrderPanelPartsFinite (weightAt)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_add positive_product)
open RationalArithmetic (add multiply multiply_monotone)
open RationalArgmin (rationalLE rationalLE_congr reflexive)
open RationalFiniteSum (canonical_equal)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalNormalForm (normalize_well_formed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def endpoint (e : ℕ) (B M K : PTm n) : PTm n :=
  fraction (power (e-1) (B*M)) (num (e-1)*power (e-1) K)

def primitive (e : ℕ) (U B : PTm n) : PTm n :=
  fraction (power (e-1) B) (num (e-1)*power (e-1) U)

def cellSample (e : ℕ) (B M K : PTm n) : PTm n := multiply (fraction one M) (weight e B M K)

def endpointSample (e : ℕ) (U B M : PTm n) : PTm n :=
  multiply (fraction one M) (fraction (power e B) (power e U))

ipra_subst primitive [power, pw]

ipra_subst endpointSample [power, pw]

ipra_subst endpoint [power, pw]

ipra_subst cellSample [weight, power, pw]

private theorem same_fraction (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] a*d ≐ c*b) : Γ ⊢[PRAAx] fraction a b ≐ fraction c d := by
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hb) (normalize_well_formed _ _ hd)
    (fraction_represents _ _ hb) (fraction_represents _ _ hd) hb hd
  apply ZT.derive
  simpa only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul] using natEq h

theorem endpoint_canonical (e : ℕ) (he : 2≤e) (B M K : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed (endpoint e B M K) :=
  normalize_well_formed _ _ (positive_product (num_le (by omega : 1≤e-1)) (power_positive _ _ hK))

theorem primitive_canonical (e : ℕ) (he : 2≤e) (U B : PTm n) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed (primitive e U B) :=
  normalize_well_formed _ _ (positive_product (num_le (by omega : 1≤e-1)) (power_positive _ _ hU))

theorem endpoint_at_multiple (e : ℕ) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] endpoint e B M (U*M) ≐ primitive e U B := by
  have h₂ : Γ ⊢[PRAAx] le one (num (e-1) : PTm n) := num_le (by omega : 1≤e-1)
  have hE := positive_product h₂ (power_positive (U*M) (num (e-1)) (positive_product hU hM))
  have hP := positive_product h₂ (power_positive U (num (e-1)) hU)
  apply same_fraction _ _ _ _ hE hP
  have l := natEq (pw_mul_base (Γ := Γ) B M (num (e-1)))
  have r := natEq (pw_mul_base (Γ := Γ) U M (num (e-1)))
  unfold power
  apply deriveNat
  ipra_simps
  rw [l,r]
  ring

theorem cell_at_multiple (e : ℕ) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] cellSample e B M (U*M) ≐ endpointSample e U B M := by
  apply multiply_congr (.eqRefl _)
  have hD := power_positive (U*M) (num e) (positive_product hU hM)
  have hE := power_positive U (num e) hU
  apply same_fraction _ _ _ _ hD hE
  have l := natEq (pw_mul_base (Γ := Γ) B M (num e))
  have r := natEq (pw_mul_base (Γ := Γ) U M (num e))
  unfold power
  apply deriveNat
  ipra_simps
  rw [l,r]
  ring

private theorem pow_succ (e : ℕ) (he : 2≤e) (K : PTm n) :
    Γ ⊢[PRAAx] power e K ≐ power (e-1) K*K := by
  have c : succ (num (e-1) : PTm n) = num e := by
    change num ((e-1)+1) = num e
    congr 1
    omega
  unfold power
  rw [← c]
  exact pw_succ K _

theorem scaled_cell (e : ℕ) (he : 2≤e) (B M K : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] multiply (fraction (power (e-1) (B*M)) one) (fraction B (power e K)) ≐ cellSample e B M K := by
  have hP := power_positive (Γ := Γ) K (num e) hK
  have hL := positive_product (le_refl one) hP
  have hR := positive_product hM hP
  have eq : Γ ⊢[PRAAx] fraction (power (e-1) (B*M)*B) (one*power e K) ≐
      fraction (one*power e (B*M)) (M*power e K) := by
    apply same_fraction _ _ _ _ hL hR
    have c := natEq (pow_succ e he (B*M) : Γ ⊢[PRAAx] _)
    apply deriveNat
    ipra_simps
    rw [c]
    ring
  exact (fraction_multiply _ _ _ _ (le_refl one) hP).eqTrans
    (eq.eqTrans (fraction_multiply _ _ _ _ hM hP).eqSymm)

private theorem scaled_primitive (e : ℕ) (he : 2≤e) (B M K : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] multiply (fraction (power (e-1) (B*M)) one) (fraction one (num (e-1)*power (e-1) K)) ≐
      endpoint e B M K := by
  have h₂ : Γ ⊢[PRAAx] le one (num (e-1) : PTm n) := num_le (by omega : 1≤e-1)
  have hD := positive_product h₂ (power_positive K (num (e-1)) hK)
  exact (fraction_multiply _ _ _ _ (le_refl one) hD).eqTrans
    (fraction_congr (by ipra_ring) (one_mul _))

theorem cell_brackets (e : ℕ) (he : 2≤e) (B M K : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] rationalLE (add (cellSample e B M (K+B)) (endpoint e B M (K+B))) (endpoint e B M K) ⋏
      rationalLE (endpoint e B M K) (add (cellSample e B M K) (endpoint e B M (K+B))) := by
  let j := e-2
  let q : PTm n := num j
  let c := fraction (power (e-1) (B*M)) one
  have a : succ q = num (e-1) := by change num (j+1) = num (e-1); dsimp [j]; congr 1; omega
  have b : succ (num (e-1) : PTm n) = num e := by change num ((e-1)+1) = num e; congr 1; omega
  have c₀ := nonnegative_of_representation (Γ := Γ) c _ _ (le_refl one)
    (fraction_represents (power (e-1) (B*M)) one (le_refl one))
  have hnext := le_trans hK (le_add_right K B)
  have s0 : Γ ⊢[PRAAx] multiply c (strideSample q B K) ≐ cellSample e B M K := by
    simpa only [strideSample,a,b,c,power] using scaled_cell e he B M K hM hK
  have s1 : Γ ⊢[PRAAx] multiply c (strideSample q B (K+B)) ≐ cellSample e B M (K+B) := by
    simpa only [strideSample,a,b,c,power] using scaled_cell e he B M (K+B) hM hnext
  have p0 : Γ ⊢[PRAAx] multiply c (potential q K) ≐ endpoint e B M K := by
    simpa only [potential,a,c,power] using scaled_primitive e he B M K hK
  have p1 : Γ ⊢[PRAAx] multiply c (potential q (K+B)) ≐ endpoint e B M (K+B) := by
    simpa only [potential,a,c,power] using scaled_primitive e he B M (K+B) hnext
  have h := stride_brackets q K B hK
  have hi := multiply_monotone c _ _ c₀ h.andE₁
  have lo := multiply_monotone c _ _ c₀ h.andE₂
  exact .andI (rationalLE_congr ((multiply_add _ _ _).eqTrans (add_congr s1 p1)) p0 hi)
    (rationalLE_congr p0 ((multiply_add _ _ _).eqTrans (add_congr s0 p1)) lo)

theorem cell_endpoint_corrections (e : ℕ) (he : 2≤e) (B M K : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] rationalLE (endpoint e B M K) (add (cellSample e B M K) (endpoint e B M (K+B))) ⋏
      rationalLE (add (cellSample e B M K) (add (endpoint e B M (K+B)) (cellSample e B M (K+B))))
        (add (endpoint e B M K) (cellSample e B M K)) := by
  have h := cell_brackets e he B M K hM hK
  have hi := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ (reflexive (cellSample e B M K)) h.andE₁
  exact .andI h.andE₂ (rationalLE_congr (add_congr (.eqRefl _) (add_commutative _ _)) (add_commutative _ _) hi)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralMeshCells
