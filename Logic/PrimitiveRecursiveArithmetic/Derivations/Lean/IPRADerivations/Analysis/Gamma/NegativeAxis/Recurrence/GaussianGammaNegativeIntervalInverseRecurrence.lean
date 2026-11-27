import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.CoefficientVariation.GaussianGammaNegativeIntervalDerivativeTarget

/-!
# The original C24 inverse recurrence and its derivative target

The negative Gamma name equals the actual C24 pole multiplier times
the original positive Gamma name at (1+a/b). The product-rule
expression formed with the finite reciprocal correction agrees with
the original negative Gamma times the shifted digamma.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseRecurrence

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaLocalPoleFormula (original_C24_margin)
open GaussianGammaLocalPoleGuards (terminal terminal_Gamma_domain)
open GaussianGammaNegativeCriticalCorrection (guard correction)
open GaussianGammaNegativeCriticalEndpoints (shifted_source)
open GaussianGammaNegativeIntervalNative (local_margin terminal_argument negative_regular)
open GaussianGammaPoleMultiplier (multiplier)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (distributive multiply_commutative multiply_associative)
open GaussianRationalHorner (qmul)
open GaussianStirlingGammaLogarithm (arg)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianEulerLogarithmicImproperName.nameF
local notation "GF" => GaussianGammaNegativeIntervalNative.data
local notation "GP" => GaussianStirlingGammaLogarithm.gammaData
local notation "DP" => GaussianGammaDigammaNative.derivativeData
local notation "SF" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "SD" => GaussianGammaNegativeCriticalEndpoints.nameData
local notation "TF" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "TD" => GaussianGammaNegativeIntervalDerivativeTarget.data

def inverse (a b N : PTm n) : PTm n := multiplier (arg a) b (succ N)
def liftedF : PR 2 := multiplyF constantF gammaF
def liftedData (a b N : PTm n) : PTm n := multiplyData constantF gammaF (inverse a b N) (GP (b+a) b)

def derivativeF : PR 2 := multiplyF constantF E
def derivativeData (a b N : PTm n) : PTm n := multiplyData constantF E (inverse a b N) (DP (b+a) b)
def correctionFactor (a b N : PTm n) : PTm n := qmul (inverse a b N) (correction a b N)
def correctionData (a b N : PTm n) : PTm n := multiplyData constantF gammaF (correctionFactor a b N) (GP (b+a) b)
def targetF : PR 2 := addF derivativeF liftedF
def targetData (a b N : PTm n) : PTm n := addData (derivativeData a b N) (correctionData a b N)

@[simp] theorem subst_inverse {k : ℕ} (σ : Fin n → PTm k) (a b N : PTm n) :
    Syn.subst σ (inverse a b N) = inverse (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  unfold inverse multiplier GaussianGammaPoleMultiplier.signedInverseFactorial
  simp [GaussianRationalMatrixFiniteSums.minusOne, Products.fact]

@[simp] theorem subst_liftedData {k : ℕ} (σ : Fin n → PTm k) (a b N : PTm n) :
    Syn.subst σ (liftedData a b N) = liftedData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [liftedData]

ipra_subst derivativeData

ipra_subst correctionFactor

ipra_subst correctionData

ipra_subst targetData

theorem lifted_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN liftedF (liftedData a b N) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source a b h))

theorem derivative_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN derivativeF (derivativeData a b N) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianGammaDigammaNative.derivative_regular _ _ (shifted_source a b h))

theorem correction_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN liftedF (correctionData a b N) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source a b h))

theorem target_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] pointCN targetF (targetData a b N) :=
  add_fast _ _ _ _ (derivative_regular a b N h) (correction_regular a b N h)

theorem original_inverse_product (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF liftedF (GF a b N) (liftedData a b N) := by
  let j := succ N
  let w := terminal (arg a) b j
  let x := gammaData w two b b
  let y := GP (b+a) b
  let C := inverse a b N
  have src := shifted_source a b h
  have hb := src.andE₂
  have hm := local_margin a b h
  have ht := terminal_Gamma_domain (arg a) b one a b j hb (le_refl one) hb hm.andE₁ hm.andE₂.andE₁
  have c24 := original_C24_margin (arg a) b one a b j hb (le_refl one) hb hm
  have e := terminal_argument (Γ := Γ) a b N
  have argEq := GaussianGammaInputProperness.original_Gamma_proper _ _ two b one b ht e
  have moved := GaussianGammaInputProperness.gamma_source_equal _ _ two b one b ht e
  have radiusEq := GaussianGammaRadiusOverlap.original_Gamma_overlap _ two (b+a) b one b one b moved
    (GaussianStirlingGammaLogarithm.gamma_source (b+a) b src)
  have productEq := multiply_cross constantF constantF gammaF gammaF C C x y
    (constant_regular C) (constant_regular C) (gamma_regular _ _ _ _ _ ht)
    (GaussianStirlingGammaLogarithm.gamma_regular _ _ src)
    (cross_refl _ _ (constant_regular C)) (cross_trans _ _ _ _ _ _ argEq radiusEq)
  exact cross_trans _ _ _ _ _ _ c24 productEq

private theorem derivative_row (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF liftedF GaussianGammaDigammaNative.nameF) derivativeF
      (multiplyData liftedF GaussianGammaDigammaNative.nameF (liftedData a b N) (GaussianGammaDigammaNative.data (b+a) b))
      (derivativeData a b N) := by
  let F := GaussianGammaDigammaNative.nameF
  let C := inverse a b N
  let w := GP (b+a) b
  let s := GaussianGammaDigammaNative.data (b+a) b
  have src := shifted_source a b h
  have hC := constant_regular (Γ := Γ) C
  have hw := GaussianStirlingGammaLogarithm.gamma_regular _ _ src
  have hs := GaussianGammaDigammaNative.name_regular _ _ src
  have assoc := multiply_associative constantF gammaF F C w s hC hw hs
  have bind := multiply_cross constantF constantF (multiplyF gammaF F) E C C
    (multiplyData gammaF F w s) (DP (b+a) b) hC hC (multiply_fast _ _ _ _ hw hs)
    (GaussianGammaDigammaNative.derivative_regular _ _ src) (cross_refl _ _ hC)
    (GaussianGammaDigammaNative.gamma_times_digamma _ _ src)
  exact cross_trans _ _ _ _ _ _ assoc bind

private theorem correction_row (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF liftedF constantF) liftedF
      (multiplyData liftedF constantF (liftedData a b N) (correction a b N))
      (correctionData a b N) := by
  let C := inverse a b N
  let w := GP (b+a) b
  let r := correction a b N
  have hC := constant_regular (Γ := Γ) C
  have hw := GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source a b h)
  have hr := constant_regular (Γ := Γ) r
  have assoc := multiply_associative constantF gammaF constantF C w r hC hw hr
  have turn := multiply_cross constantF constantF (multiplyF gammaF constantF) liftedF C C
    (multiplyData gammaF constantF w r) (multiplyData constantF gammaF r w) hC hC
    (multiply_fast _ _ _ _ hw hr) (multiply_fast _ _ _ _ hr hw)
    (cross_refl _ _ hC) (multiply_commutative _ _ _ _ hw hr)
  exact cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ turn (GaussianGammaEulerShift.merge_head gammaF C r w hw))

theorem target_cross (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent targetF TF (targetData a b N) (TD a b N) := by
  let F := GaussianGammaDigammaNative.nameF
  let x := liftedData a b N
  let s := GaussianGammaDigammaNative.data (b+a) b
  let r := correction a b N
  have hx := lifted_regular a b N h
  have hs := GaussianGammaDigammaNative.name_regular _ _ (shifted_source a b h)
  have hr := constant_regular (Γ := Γ) r
  have hS := GaussianGammaNegativeCriticalEndpoints.name_regular a b N h
  have lift := multiply_cross gammaF liftedF SF SF (GF a b N) x (SD a b N) (SD a b N)
    (negative_regular a b N h) hx hS hS (original_inverse_product a b N h) (cross_refl _ _ hS)
  have split := distributive liftedF F constantF x s r hx hs hr
  have both := GaussianNamedGammaHalfShift.add_cross (multiplyF liftedF F) derivativeF (multiplyF liftedF constantF) liftedF
    (multiplyData liftedF F x s) (derivativeData a b N) (multiplyData liftedF constantF x r) (correctionData a b N)
    (multiply_fast _ _ _ _ hx hs) (derivative_regular a b N h)
    (multiply_fast _ _ _ _ hx hr) (correction_regular a b N h)
    (derivative_row a b N h) (correction_row a b N h)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ lift (cross_trans _ _ _ _ _ _ split both))

theorem actual_original_negative_Gamma_inverse_recurrence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶ crossEquivalent gammaF liftedF (GF (var 0) (var 1) (var 2))
        (liftedData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_inverse_product _ _ _ Prf.hyp0))

theorem actual_original_negative_Gamma_inverse_derivative_target_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶ crossEquivalent targetF TF (targetData (var 0) (var 1) (var 2))
        (TD (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (target_cross _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseRecurrence
