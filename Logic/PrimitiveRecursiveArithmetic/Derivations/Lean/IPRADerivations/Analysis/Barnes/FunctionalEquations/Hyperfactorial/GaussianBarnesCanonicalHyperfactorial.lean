import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalValueZeros
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerCofinal
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Exponential.Names.GaussianRadiusExponentialName

/-!
# The analytic hyperfactorial on the positive rational axis

The original Euler logarithm of Gamma supplies the exponent
`(z-1) Log Gamma(z)`. At `z=A/B>0`, the original canonical Barnes value
is apart from zero. Its certified reciprocal gives a regular name for
`H(z)`, and multiplying it by the original Barnes value returns exactly
the named exponential.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorial

open_ipra
open ComplexLogarithmRemainder (bounded bounded_add bounded_mono bounded_neg bounded_scale normSq_one oneCode scale)
open GaussianRootAlgebra (sub)
open GaussianRationalHorner (ofGaussian)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one)
open GaussianNameReciprocal (apart nameData name_fast product_one_left)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def center (A B : PTm n) : PTm n := sub (scale A oneCode) (scale B oneCode)
def radius (A B : PTm n) : PTm n := A+B
def barnesData (A B : PTm n) : PTm n := GaussianBarnesCanonicalValue.data (center A B) (radius A B) B
def height (A B : PTm n) : PTm n := GaussianBarnesCanonicalValueZeros.height (center A B) (radius A B) B
def specialLogData (A B : PTm n) : PTm n :=
  GaussianLogGammaEulerCofinal.canonicalData A zero B zero
abbrev exponentF : PR 2 := multiplyF constantF GaussianLogGammaEulerCofinal.nameF
def exponentData (A B : PTm n) : PTm n :=
  multiplyData constantF GaussianLogGammaEulerCofinal.nameF (ofGaussian (center A B) B) (specialLogData A B)
def powerRadius (A B : PTm n) : PTm n := GaussianNameBounds.U exponentF (exponentData A B)
abbrev powerF : PR 2 := GaussianRadiusExponentialName.nameF exponentF
def powerData (A B : PTm n) : PTm n := GaussianRadiusExponentialName.data (powerRadius A B) (exponentData A B)
abbrev inverseF : PR 2 := GaussianNameReciprocal.nameF GaussianBarnesCanonicalValue.nameF
def inverseData (A B : PTm n) : PTm n := nameData (height A B) (barnesData A B)
abbrev nameF : PR 2 := multiplyF powerF inverseF
def data (A B : PTm n) : PTm n := multiplyData powerF inverseF (powerData A B) (inverseData A B)
abbrev productF : PR 2 := multiplyF nameF GaussianBarnesCanonicalValue.nameF
def productData (A B : PTm n) : PTm n :=
  multiplyData nameF GaussianBarnesCanonicalValue.nameF (data A B) (barnesData A B)

@[simp] theorem subst_center {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (center A B) = center (Syn.subst σ A) (Syn.subst σ B) := by simp [center]

@[simp] theorem subst_barnesData {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (barnesData A B) = barnesData (Syn.subst σ A) (Syn.subst σ B) := by simp [barnesData,radius]

@[simp] theorem subst_specialLogData {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (specialLogData A B) = specialLogData (Syn.subst σ A) (Syn.subst σ B) := by simp [specialLogData]

@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (exponentData A B) = exponentData (Syn.subst σ A) (Syn.subst σ B) := by simp [exponentData]

@[simp] theorem subst_powerData {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (powerData A B) = powerData (Syn.subst σ A) (Syn.subst σ B) := by simp [powerData,powerRadius]

theorem barnes_source (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source (center A B) (radius A B) B := by
  have oneBound : Γ ⊢[PRAAx] bounded (oneCode : PTm n) one :=
    le_congr normSq_one.eqSymm (one_mul one).eqSymm (le_refl one)
  have hscale (C : PTm n) : Γ ⊢[PRAAx] bounded (scale C oneCode) C :=
    le_congr (.eqRefl _) (by ipra_ring) (bounded_scale C oneBound)
  have centerBound : Γ ⊢[PRAAx] bounded (center A B) (radius A B) :=
    bounded_add (hscale A) (bounded_neg (hscale B))
  exact .andI hB (bounded_mono centerBound
    (le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (radius A B) hB)))

private theorem exclude_pole (A B k : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hk : Γ ⊢[PRAAx] le one k)
    (h : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (center A B) (GaussianGammaPoleZeros.poleNumerator B k)) :
    Γ ⊢[PRAAx] Fm.bot := by
  have he := GaussianRootAlgebra.equal_re h
  simp only [center,GaussianGammaPoleZeros.poleNumerator,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_neg,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,mul_one] at he
  have bad : Γ ⊢[PRAAx] A+B*k ≐ B := by
    apply deriveNat
    ipra_simps
    linear_combination he
  have bk : Γ ⊢[PRAAx] le B (B*k) :=
    le_congr (one_mul B) (mul_comm _ _) (mul_le_mul_right B hk)
  have ahead : Γ ⊢[PRAAx] lt B (A+B*k) :=
    le_congr (succ_eq_add_one B).eqSymm (add_comm (B*k) A) (LeanProofs.IPRA.Common.add_le_add bk hA)
  exact lt_irrefl _ _ (lt_congr (.eqRefl _) bad ahead)

theorem barnes_apart (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] apart GaussianBarnesCanonicalValue.nameF (height A B) (barnesData A B) := by
  have choices := GaussianBarnesCanonicalValueZeros.original_zero_or_apart
    (center A B) (radius A B) B (barnes_source A B hB)
  refine .orE choices ?_ Prf.hyp0
  exact .botE _ (exclude_pole A B _ hA.wk Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₂)

theorem barnes_regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN GaussianBarnesCanonicalValue.nameF (barnesData A B) :=
  GaussianBarnesCanonicalValue.regular _ _ _ (barnes_source A B hB)

theorem logarithm_source (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A B zero :=
  .andI (.andI hA (.orI₁ (.eqRefl _))) hB

theorem exponent_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN exponentF (exponentData A B) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (GaussianLogGammaEulerCofinal.canonical_regular A zero B zero (logarithm_source A B hA hB))

theorem power_input (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input exponentF (powerRadius A B) (exponentData A B) :=
  let h := exponent_regular A B hA hB
  .andI h (GaussianNameBounds.all_samples_bounded _ _ h)

theorem power_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN powerF (powerData A B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (power_input A B hA hB)

theorem inverse_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN inverseF (inverseData A B) :=
  name_fast _ _ _ (barnes_regular A B hB) (barnes_apart A B hA hB)

theorem regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  multiply_fast _ _ _ _ (power_regular A B hA hB) (inverse_regular A B hA hB)

theorem cleared_relation (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent productF powerF (productData A B) (powerData A B) := by
  let G := GaussianBarnesCanonicalValue.nameF
  let x := powerData A B
  let d := barnesData A B
  let y := inverseData A B
  let u := multiplyData inverseF G y d
  have hx := power_regular A B hA hB
  have hd := barnes_regular A B hB
  have hy := inverse_regular A B hA hB
  have hprod := multiply_fast inverseF G y d hy hd
  have assoc := multiply_associative powerF inverseF G x y d hx hy hd
  have one := product_one_left G (height A B) d hd (barnes_apart A B hA hB)
  have collapse := GaussianGammaAdjacentCutoff.multiply_cross powerF powerF (multiplyF inverseF G) oneF
    x x u x hx hx hprod (one_fast x) (cross_refl _ _ hx)
    (cross_trans _ _ _ _ _ _ one (GaussianBoundedInverseApartness.ones_equivalent d x))
  exact cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ collapse (multiply_one powerF x hx))

theorem actual_original_Barnes_hyperfactorial_cleared_relation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let A := var 0; let B := var 1
     le one A ⟶ le one B ⟶ crossEquivalent productF powerF (productData A B) (powerData A B)) :=
  closeUniv 2 (.impI (.impI (cleared_relation _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorial
