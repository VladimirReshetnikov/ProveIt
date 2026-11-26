import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmOffset
import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmRescale

/-!
# The exact centered inputs of normalized Euler logarithm rows

The offset of the normalized row is the original numerator of z, and
its denominator is the original denominator times the row index. This
binds the linear term to z/k without changing the signed coordinates.
When k is at least eight times the original disk radius, this very row
has the one-eighth offset certificate used by the local logarithm.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualDomain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code scale mul oneCode eval_re_code eval_im_code)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents
  qmul qmul_canonical qmul_represents canonical_unique represents_congr positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRightHalfPlaneLogarithmOffset (signedImag offset)
open GaussianRootAlgebra (equal equal_of_values normSq_equal re_mul im_mul re_scale im_scale re_one im_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def native (A B neg : PTm n) : PTm n := code (ZT.ofNat A) (signedImag B neg)
def source (A B D neg R : PTm n) : Fm PTm n :=
  GaussianRightHalfPlaneLogarithm.source A D neg ⋏ ComplexLogarithmRemainder.bounded (native A B neg) (R*D)
def rowOffset (A B D neg k : PTm n) : PTm n := offset (A+k*D) B (D*k) neg
def linearTerm (A B D neg k : PTm n) : PTm n := ofGaussian (native A B neg) (D*k)

@[simp] theorem subst_native {m : ℕ} (σ : Fin n → PTm m) (A B neg : PTm n) :
    Syn.subst σ (native A B neg) = native (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ neg) := by
  simp [native]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A B D neg R : PTm n) :
    (source A B D neg R).subst σ =
      source (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ R) := by
  simp [source,GaussianRightHalfPlaneLogarithm.source,ComplexLogarithmRemainder.bounded]

@[simp] theorem subst_rowOffset {m : ℕ} (σ : Fin n → PTm m) (A B D neg k : PTm n) :
    Syn.subst σ (rowOffset A B D neg k) = rowOffset (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ neg) (Syn.subst σ k) := by
  simp [rowOffset]

@[simp] theorem subst_linearTerm {m : ℕ} (σ : Fin n → PTm m) (A B D neg k : PTm n) :
    Syn.subst σ (linearTerm A B D neg k) =
      linearTerm (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ k) := by
  simp [linearTerm]

theorem centered_native (A B D neg k : PTm n) : Γ ⊢[PRAAx] equal (rowOffset A B D neg k) (native A B neg) := by
  apply equal_of_values
  · simp only [rowOffset,offset,native,eval_re_code,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    ring
  · simp only [rowOffset,offset,native,eval_im_code]

theorem native_admission (A B D neg ρ k : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (hb : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (native A B neg) ρ)
    (hk : Γ ⊢[PRAAx] le one k) (hlarge : Γ ⊢[PRAAx] le (num 8*ρ) (D*k)) :
    Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmOffset.source (A+k*D) B (D*k) neg ρ := by
  have hn : Γ ⊢[PRAAx] le one (A+k*D) := le_trans h.andE₁.andE₁ (le_add_right _ _)
  have hd := positive_product D k h.andE₂ hk
  have bound : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (rowOffset A B D neg k) ρ :=
    le_congr (normSq_equal (centered_native A B D neg k)).eqSymm (.eqRefl _) hb
  exact .andI (.andI (.andI hn h.andE₁.andE₂) hd) (.andI bound hlarge)

theorem admission (A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) (hlarge : Γ ⊢[PRAAx] le (num 8*R) k) :
    Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmOffset.source (A+k*D) B (D*k) neg (R*D) := by
  have width : Γ ⊢[PRAAx] le (num 8*(R*D)) (D*k) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl D) hlarge)
  exact native_admission A B D neg (R*D) k h.andE₁ h.andE₂ hk width

theorem linear_point (A B D neg k : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] ofGaussian (rowOffset A B D neg k) (D*k) ≐ linearTerm A B D neg k := by
  let z := native A B neg
  let w := rowOffset A B D neg k
  let d := D*k
  have hd := positive_product D k hD hk
  exact canonical_unique (ofGaussian w d) (ofGaussian z d) z d (ofGaussian_canonical w d hd)
    (ofGaussian_canonical z d hd) hd
    (represents_congr (.eqRefl _) (centered_native A B D neg k) (.eqRefl _) (ofGaussian_represents w d hd))
    (ofGaussian_represents z d hd)

theorem linear_product (A B D neg k : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qmul (GaussianLogGammaEulerHead.argument A B D neg) (fraction one k) ≐ linearTerm A B D neg k := by
  let z := native A B neg
  let q := GaussianLogGammaEulerHead.argument A B D neg
  let u : PTm n := scale one oneCode
  let d := D*k
  have hd := positive_product D k hD hk
  have unit : Γ ⊢[PRAAx] equal (mul z u) z := by
    apply equal_of_values <;>
      simp only [u,re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;>
      ipra_simps <;> ring
  have product := qmul_represents q (fraction one k) z u D k hD hk
    (ofGaussian_represents z D hD) (ofGaussian_represents u k hk)
  exact canonical_unique (qmul q (fraction one k)) (ofGaussian z d) z d
    (qmul_canonical _ _) (ofGaussian_canonical z d hd) hd
    (represents_congr (.eqRefl _) unit (.eqRefl _) product) (ofGaussian_represents z d hd)

theorem linear_bound (A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] bounded (linearTerm A B D neg k) R k := by
  let z := native A B neg
  let d := D*k
  have hd := positive_product D k h.andE₁.andE₂ hk
  apply bounded_of_cleared _ z d R k hd hk (ofGaussian_represents z d hd)
  exact le_congr (.eqRefl _) (by dsimp only [d]; ipra_ring) (le_mul_mono (le_refl (k*k)) h.andE₂)

theorem actual_normalized_Euler_row_center_admission_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        (le one (var 5) ⋏ le (num 8*var 4) (var 5)) ⟶
        (GaussianRightHalfPlaneLogarithmOffset.source (var 0+var 5*var 2) (var 1) (var 2*var 5) (var 3) (var 4*var 2) ⋏
          bounded (linearTerm (var 0) (var 1) (var 2) (var 3) (var 5)) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (.andI (admission _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (linear_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁))))

theorem actual_normalized_Euler_row_linear_point_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((le one (var 2) ⋏ le one (var 4)) ⟶
        (ofGaussian (rowOffset (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2*var 4) ≐
          linearTerm (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        (qmul (GaussianLogGammaEulerHead.argument (var 0) (var 1) (var 2) (var 3)) (fraction one (var 4)) ≐
          linearTerm (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.andI (linear_point _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (linear_product _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualDomain
