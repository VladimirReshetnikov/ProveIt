import IPRADerivations.Algebra.QuadraticPositiveScaling
import IPRADerivations.Analysis.RationalRepresentations

/-!
# Actual rational-coefficient clearing for one quadratic stage

A pair stores two ORIGINAL rational codes with independent positive
decoded denominators. The actual common-numerator pair and denominator
are computed and their representation is proved. Positive scaling
derives sign independence from both equivalent raw coefficient codes
and any legitimate positive-denominator representation.

The radicand is still a positive integer. Rational radicands, rational
pair arithmetic and iterated towers are not claimed by this kernel.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalClearing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalEq)
open QuadraticSignCertificates (first second encode equal first_value second_value)
open QuadraticPositiveScaling (scale scale_first scale_second cross_scale_sign)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def denominator (x : PTm n) : PTm n := denominatorOf (fstT x)*denominatorOf (sndT x)
def clear (x : PTm n) : PTm n := encode
  (numeratorOf (fstT x)*ZT.ofNat (denominatorOf (sndT x)))
  (numeratorOf (sndT x)*ZT.ofNat (denominatorOf (fstT x)))
def represents (x A D : PTm n) : Fm PTm n :=
  LeanProofs.IPRA.Analysis.RationalArithmetic.represents (fstT x) (first A) D ⋏
    LeanProofs.IPRA.Analysis.RationalArithmetic.represents (sndT x) (second A) D
def sameCoefficients (x y : PTm n) : Fm PTm n :=
  rationalEq (fstT x) (fstT y) ⋏ rationalEq (sndT x) (sndT y)
def sign (d x : PTm n) : PTm n := QuadraticSignCertificates.sign d (clear x)
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (denominator x) = denominator (Syn.subst σ x) := by simp [denominator]
@[simp] theorem subst_clear {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (clear x) = clear (Syn.subst σ x) := by simp [clear]
@[simp] theorem subst_represents {l : ℕ} (σ : Fin n → PTm l) (x A D : PTm n) :
    (represents x A D).subst σ = represents (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ D) := by simp [represents]
@[simp] theorem subst_sameCoefficients {l : ℕ} (σ : Fin n → PTm l) (x y : PTm n) :
    (sameCoefficients x y).subst σ = sameCoefficients (Syn.subst σ x) (Syn.subst σ y) := by simp [sameCoefficients]
@[simp] theorem subst_sign {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    Syn.subst σ (sign d x) = sign (Syn.subst σ d) (Syn.subst σ x) := by simp [sign]

theorem denominator_positive (x : PTm n) : Γ ⊢[PRAAx] le one (denominator x) :=
  LeanProofs.IPRA.Analysis.RationalArithmetic.product_denominator_positive (fstT x) (sndT x)
theorem clear_first (x : PTm n) : ZT.toZ Γ (first (clear x)) =
    ZT.toZ Γ (numeratorOf (fstT x))*𝔞(denominatorOf (sndT x)) := by
  rw [clear,first_value,ZT.toZ_mul,ZT.toZ_ofNat]
theorem clear_second (x : PTm n) : ZT.toZ Γ (second (clear x)) =
    ZT.toZ Γ (numeratorOf (sndT x))*𝔞(denominatorOf (fstT x)) := by
  rw [clear,second_value,ZT.toZ_mul,ZT.toZ_ofNat]
theorem clear_represents (x : PTm n) : Γ ⊢[PRAAx] represents x (clear x) (denominator x) := by
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  all_goals simp only [ZT.toZ_mul,ZT.toZ_ofNat,
    clear_first,clear_second,denominator,Q.mk_mul,map_mul]; ring

theorem scalar_representations_cross (q A B : PTm n) (a b : ZT n)
    (ha : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents q a A)
    (hb : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents q b B) : Γ ⊢[PRAAx]
    ZT.eq (a*ZT.ofNat B) (b*ZT.ofNat A) := by
  apply LeanProofs.IPRA.Analysis.RationalNormalForm.positive_integer_cancel (denominatorOf q) _ _ (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive q)
  apply ZT.derive
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at ea eb ⊢
  linear_combination 𝔞(B)*ea-𝔞(A)*eb
theorem representations_cross (x A D B E : PTm n)
    (ha : Γ ⊢[PRAAx] represents x A D) (hb : Γ ⊢[PRAAx] represents x B E) : Γ ⊢[PRAAx]
    equal (scale E A) (scale D B) := by
  apply QuadraticConeOrder.equal_of_values
  · have h := ZT.toZ_eq (scalar_representations_cross (fstT x) D E (first A) (first B) (.andE₁ ha) (.andE₁ hb))
    simp only [scale_first,ZT.toZ_mul,ZT.toZ_ofNat] at h ⊢
    linear_combination h
  · have h := ZT.toZ_eq (scalar_representations_cross (sndT x) D E (second A) (second B) (.andE₂ ha) (.andE₂ hb))
    simp only [scale_second,ZT.toZ_mul,ZT.toZ_ofNat] at h ⊢
    linear_combination h
theorem representation_sign (d x A D : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] represents x A D) : Γ ⊢[PRAAx]
    sign d x ≐ QuadraticSignCertificates.sign d A :=
  cross_scale_sign d D (denominator x) (clear x) A hd hD (denominator_positive x)
    (representations_cross x (clear x) (denominator x) A D (clear_represents x) h)

theorem equal_coefficient_cross (x y : PTm n) (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx]
    equal (scale (denominator y) (clear x)) (scale (denominator x) (clear y)) := by
  have ea := natEq (Prf.andE₁ h)
  have eb := natEq (Prf.andE₂ h)
  apply QuadraticConeOrder.equal_of_values
  · simp only [scale_first,clear_first,denominator,Q.mk_mul,map_mul]
    simp only [LeanProofs.IPRA.Analysis.RationalArgmin.left,Q.mk_add,Q.mk_mul,map_add,map_mul] at ea
    simp only [ZT.toZ]
    linear_combination 𝔞(denominatorOf (sndT x))*𝔞(denominatorOf (sndT y))*ea
  · simp only [scale_second,clear_second,denominator,Q.mk_mul,map_mul]
    simp only [LeanProofs.IPRA.Analysis.RationalArgmin.left,Q.mk_add,Q.mk_mul,map_add,map_mul] at eb
    simp only [ZT.toZ]
    linear_combination 𝔞(denominatorOf (fstT x))*𝔞(denominatorOf (fstT y))*eb
theorem sign_congr (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx] sign d x ≐ sign d y :=
  cross_scale_sign d (denominator y) (denominator x) (clear x) (clear y) hd
    (denominator_positive y) (denominator_positive x) (equal_coefficient_cross x y h)

def output (d x : PTm n) : PTm n := pairT (clear x) (pairT (denominator x) (sign d x))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d x : PTm n) : PTm n := ap2 outputF d x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    Syn.subst σ (output d x) = output (Syn.subst σ d) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d x : PTm n) :
    Syn.subst σ (run d x) = run (Syn.subst σ d) (Syn.subst σ x) := by simp [run]
theorem program_at (d x : PTm n) : Γ ⊢[PRAAx] run d x ≐ output d x := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,x]
theorem returned_clear (d x : PTm n) : Γ ⊢[PRAAx] fstT (run d x) ≐ clear x :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_denominator (d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d x)) ≐ denominator x :=
  (congrFst ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_sign (d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d x)) ≐ sign d x :=
  (congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_positive_denominator (d x : PTm n) : Γ ⊢[PRAAx] le one (fstT (sndT (run d x))) :=
  le_congr (.eqRefl _) (returned_denominator _ _).eqSymm (denominator_positive x)
theorem returned_represents (d x : PTm n) : Γ ⊢[PRAAx]
    represents x (fstT (run d x)) (fstT (sndT (run d x))) := by
  simpa only [subst_represents,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (represents (var 0) (var 1) (var 2) : Fm PTm 3)
      ![x,clear x,denominator x] ![x,fstT (run d x),fstT (sndT (run d x))]
      (fun i => by fin_cases i; exact .eqRefl _; exact (returned_clear _ _).eqSymm; exact (returned_denominator _ _).eqSymm)
      (by simpa only [subst_represents,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using clear_represents (Γ := Γ) x)

theorem actual_rational_quadratic_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (denominator (var 0)) ⋏ represents (var 0) (clear (var 0)) (denominator (var 0))) :=
  closeUniv 1 (.andI (denominator_positive _) (clear_represents _))
theorem actual_rational_representation_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 3) ⟶ represents (var 1) (var 2) (var 3) ⟶
      sign (var 0) (var 1) ≐ QuadraticSignCertificates.sign (var 0) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (representation_sign _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_coefficient_sign_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ sameCoefficients (var 1) (var 2) ⟶ sign (var 0) (var 1) ≐ sign (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (sign_congr _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_quadratic_clearing_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_rational_returned_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (fstT (sndT (run (var 0) (var 1)))) ⋏
      represents (var 1) (fstT (run (var 0) (var 1))) (fstT (sndT (run (var 0) (var 1))))) :=
  closeUniv 2 (.andI (returned_positive_denominator _ _) (returned_represents _ _))

end LeanProofs.IPRA.Algebra.QuadraticRationalClearing
