import IPRADerivations.Analysis.GaussianBinetStirlingRemainder

/-!
# Exact rational residual for the complex Stirling unit difference

The four logarithm observations may be arbitrary Gaussian rationals.
After clearing denominators, the unit-step residual is precisely the
residual of the log-Gamma recurrence. The common Stirling constant
cancels for every observation of that constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingUnitDifferenceAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add mul scale oneCode eval_re_code eval_im_code)
open GaussianBinetStirlingRemainder (offset)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner
  (qadd qmul represents qadd_represents qmul_represents ofGaussian_represents positive_product canonical_unique represents_congr)
open GaussianRationalL1 (rawDen rawGaussian raw_represents)
open GaussianRationalMetric (qsub qnegative qsub_canonical qsub_represents)
open GaussianRationalSyntheticDivision (qone qadd_congr qsub_congr rescale_to remainingDen remaining_den_positive)
open GaussianRootAlgebra (sub equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_scale im_scale re_one im_one)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (A B D sign : PTm n) : PTm n := qadd (argument A B D sign) (fraction one two)

def rawCore (A B D sign g l : PTm n) : PTm n :=
  qadd (qsub g (qmul (offset A B D sign) l)) (argument A B D sign)

def rawRemainder (A B D sign g l c : PTm n) : PTm n := qsub (rawCore A B D sign g l) c

def rawDifference (A B D sign l m : PTm n) : PTm n :=
  qsub (qmul (coefficient A B D sign) (qsub m l)) qone

@[simp] theorem subst_coefficient {k : ℕ} (σ : Fin n → PTm k) (A B D sign : PTm n) :
    Syn.subst σ (coefficient A B D sign) =
      coefficient (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ sign) := by
  simp [coefficient,one,two,GaussianLogGammaEulerRepresentation.subst_argument]

private theorem cancel_constant (x y c : PTm n) :
    Γ ⊢[PRAAx] qsub (qsub x c) (qsub y c) ≐ qsub x y :=
  (GaussianNameArithmetic.sum_difference x y (qnegative c) (qnegative c)).eqTrans
    ((qadd_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self _)).eqTrans
      (GaussianRationalLinearProduct.qadd_zero_right _ (qsub_canonical _ _)))

private theorem point_rep (A B D sign : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] represents (argument A B D sign) (scale two (native A B sign)) (two*D) :=
  rescale_to _ _ D two (two*D) (ofGaussian_represents (native A B sign) D hD) (mul_comm _ _)

private theorem half_rep (D : PTm n) :
    Γ ⊢[PRAAx] represents (fraction one two) (scale D oneCode) (two*D) := by
  have h := GaussianRationalHorner.represents_rescale _ _ two D
    (ofGaussian_represents (Γ := Γ) (scale one oneCode) two (le_succ_self one))
  exact represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring) (.eqRefl _) h

private theorem core_residual (A B D sign g h l m : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qsub (qsub (rawCore A B D sign g l) (rawCore (A+D) B D sign h m)) (rawDifference A B D sign l m)
      ≐ qsub l (qsub h g) := by
  let C := two*D
  let E := remainingDen g h l m
  let T := C*E
  let G := scale (rawDen h*rawDen l*rawDen m) (rawGaussian g)
  let H := scale (rawDen g*rawDen l*rawDen m) (rawGaussian h)
  let L := scale (rawDen g*rawDen h*rawDen m) (rawGaussian l)
  let M := scale (rawDen g*rawDen h*rawDen l) (rawGaussian m)
  let Z := scale two (native A B sign)
  let W := scale two (native (A+D) B sign)
  let K := scale D oneCode
  have hc : Γ ⊢[PRAAx] le one C := positive_product _ _ (le_succ_self one) hD
  have he : Γ ⊢[PRAAx] le one E := remaining_den_positive g h l m
  have ht : Γ ⊢[PRAAx] le one T := positive_product _ _ hc he
  have rg : Γ ⊢[PRAAx] represents g G E := rescale_to _ _ _ _ _ (raw_represents g) (by dsimp [E,remainingDen]; ipra_ring)
  have rh : Γ ⊢[PRAAx] represents h H E := rescale_to _ _ _ _ _ (raw_represents h) (by dsimp [E,remainingDen]; ipra_ring)
  have rl : Γ ⊢[PRAAx] represents l L E := rescale_to _ _ _ _ _ (raw_represents l) (by dsimp [E,remainingDen]; ipra_ring)
  have rm : Γ ⊢[PRAAx] represents m M E := rescale_to _ _ _ _ _ (raw_represents m) (by dsimp [E,remainingDen]; ipra_ring)
  have rz : Γ ⊢[PRAAx] represents (argument A B D sign) Z C := point_rep A B D sign hD
  have rw : Γ ⊢[PRAAx] represents (argument (A+D) B D sign) W C := point_rep (A+D) B D sign hD
  have rk : Γ ⊢[PRAAx] represents (fraction one two) K C := half_rep D
  have r0 : Γ ⊢[PRAAx] represents (offset A B D sign) (sub Z K) C :=
    qsub_represents _ _ _ _ _ hc rz rk
  have r1 : Γ ⊢[PRAAx] represents (offset (A+D) B D sign) (sub W K) C :=
    qsub_represents _ _ _ _ _ hc rw rk
  have rc : Γ ⊢[PRAAx] represents (coefficient A B D sign) (add Z K) C :=
    qadd_represents _ _ _ _ _ hc rz rk
  have w0 := qmul_represents _ _ _ _ _ _ hc he r0 rl
  have w1 := qmul_represents _ _ _ _ _ _ hc he r1 rm
  have zl := GaussianRationalHorner.represents_rescale _ _ C E rz
  have zr := GaussianRationalHorner.represents_rescale _ _ C E rw
  have gl := rescale_to g G E C T rg (mul_comm _ _)
  have gr := rescale_to h H E C T rh (mul_comm _ _)
  have left : Γ ⊢[PRAAx] represents (rawCore A B D sign g l) (add (sub (scale C G) (mul (sub Z K) L)) (scale E Z)) T :=
    qadd_represents _ _ _ _ _ ht (qsub_represents _ _ _ _ _ ht gl w0) zl
  have right : Γ ⊢[PRAAx] represents (rawCore (A+D) B D sign h m) (add (sub (scale C H) (mul (sub W K) M)) (scale E W)) T :=
    qadd_represents _ _ _ _ _ ht (qsub_represents _ _ _ _ _ ht gr w1) zr
  have exactTerm : Γ ⊢[PRAAx] represents (rawDifference A B D sign l m)
      (sub (mul (add Z K) (sub M L)) (scale T oneCode)) T :=
    qsub_represents _ _ _ _ _ ht (qmul_represents _ _ _ _ _ _ hc he rc (qsub_represents _ _ _ _ _ he rm rl))
      (GaussianRationalReciprocal.qone_represents_scaled T)
  have lhs := qsub_represents _ _ _ _ _ ht (qsub_represents _ _ _ _ _ ht left right) exactTerm
  have rhs := rescale_to _ (sub L (sub H G)) E C T
    (qsub_represents _ _ _ _ _ he rl (qsub_represents _ _ _ _ _ he rh rg)) (mul_comm _ _)
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) ht (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;>
    simp only [Z,W,K,T,C,native,re_add,im_add,re_sub,im_sub,re_mul,im_mul,re_scale,im_scale,re_one,im_one,
      eval_re_code,eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring

theorem residual (A B D sign g h l m c : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qsub (qsub (rawRemainder A B D sign g l c) (rawRemainder (A+D) B D sign h m c))
      (rawDifference A B D sign l m) ≐ qsub l (qsub h g) :=
  (qsub_congr (cancel_constant _ _ c) (.eqRefl _)).eqTrans (core_residual A B D sign g h l m hD)

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingUnitDifferenceAlgebra
