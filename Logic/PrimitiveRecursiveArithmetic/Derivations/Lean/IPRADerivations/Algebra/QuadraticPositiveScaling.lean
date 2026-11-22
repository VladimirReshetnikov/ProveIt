import IPRADerivations.Algebra.QuadraticIntegerEmbedding

/-!
# Positive denominator scaling for the actual integer quadratic sign

The original sign is unchanged on multiplying by an actual positive
integer. This is the denominator-clearing kernel needed for rational
ground coefficients. The scale is a computed coefficient operation;
all sign laws are derived from the existing finite certificates.
No rational or iterated-stage interpretation is assumed here.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticPositiveScaling

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open QuadraticSignCertificates (first second encode equal add negative multiply sign
  first_value second_value multiply_first multiply_second negative_first negative_second)
open QuadraticConeOrder (equal_of_values equal_symm add_first add_second sign_congr negative_product_right)
open QuadraticIntegerOrder (positive isZero isNegative positive_multiply positive_value_congr
  negative_positive positive_negative zero_multiply zero_value_congr)
open QuadraticIntegerEmbedding (integer integer_first integer_second negative_value_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scale (k x : PTm n) : PTm n := encode (ZT.ofNat k*first x) (ZT.ofNat k*second x)
@[simp] theorem subst_scale {l : ℕ} (σ : Fin n → PTm l) (k x : PTm n) :
    Syn.subst σ (scale k x) = scale (Syn.subst σ k) (Syn.subst σ x) := by simp [scale]
theorem scale_first (k x : PTm n) : ZT.toZ Γ (first (scale k x)) =
    Groth.ι (Q.mk Γ k)*ZT.toZ Γ (first x) := by rw [scale,first_value,ZT.toZ_mul,ZT.toZ_ofNat]
theorem scale_second (k x : PTm n) : ZT.toZ Γ (second (scale k x)) =
    Groth.ι (Q.mk Γ k)*ZT.toZ Γ (second x) := by rw [scale,second_value,ZT.toZ_mul,ZT.toZ_ofNat]
theorem scale_one (x : PTm n) : Γ ⊢[PRAAx] equal (scale one x) x := by
  apply equal_of_values <;> simp only [scale_first,scale_second,Q.mk_one,map_one,_root_.one_mul]
theorem scale_add (k x y : PTm n) : Γ ⊢[PRAAx] equal (scale k (add x y)) (add (scale k x) (scale k y)) := by
  apply equal_of_values <;> simp only [scale_first,scale_second,add_first,add_second] <;> ring
theorem scale_negative (k x : PTm n) : Γ ⊢[PRAAx] equal (scale k (negative x)) (negative (scale k x)) := by
  apply equal_of_values <;> simp only [scale_first,scale_second,negative_first,negative_second] <;> ring
theorem scale_composition (k l x : PTm n) : Γ ⊢[PRAAx] equal (scale k (scale l x)) (scale (k*l) x) := by
  apply equal_of_values <;> simp only [scale_first,scale_second,Q.mk_mul,map_mul] <;> ring
theorem scale_multiply (d k l x y : PTm n) : Γ ⊢[PRAAx]
    equal (scale (k*l) (multiply d x y)) (multiply d (scale k x) (scale l y)) := by
  apply equal_of_values <;> simp only [scale_first,scale_second,multiply_first,multiply_second,Q.mk_mul,map_mul] <;> ring
theorem scale_product (d k x : PTm n) : Γ ⊢[PRAAx]
    equal (scale k x) (multiply d (integer (ZT.ofNat k)) x) := by
  apply equal_of_values <;> simp only [scale_first,scale_second,multiply_first,multiply_second,
    integer_first,integer_second,ZT.toZ_ofNat] <;> ring
theorem product_commute (d x y : PTm n) : Γ ⊢[PRAAx] equal (multiply d x y) (multiply d y x) := by
  apply equal_of_values <;> simp only [multiply_first,multiply_second] <;> ring

theorem positive_factor_sign (d u x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hu : Γ ⊢[PRAAx] positive d u) : Γ ⊢[PRAAx] sign d (multiply d u x) ≐ sign d x := by
  refine .orE (QuadraticIntegerOrder.sign_trichotomy d x) ?_ ?_
  · exact (positive_multiply _ _ _ hd.wk hu.wk Prf.hyp0).eqTrans Prf.hyp0.eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · let Δ := isNegative d x :: (isNegative d x ⋎ isZero d x) :: Γ
      have hp : Δ ⊢[PRAAx] positive d (negative (multiply d u x)) :=
        positive_value_congr d (multiply d u (negative x)) (negative (multiply d u x)) hd.wk.wk
        (negative_product_right _ _ _) (positive_multiply _ _ _ hd.wk.wk hu.wk.wk (negative_positive _ _ hd.wk.wk Prf.hyp0))
      have hn : Δ ⊢[PRAAx] isNegative d (multiply d u x) :=
        negative_value_congr _ _ _ hd.wk.wk (QuadraticConeOrder.negative_negative (multiply d u x))
        (positive_negative _ _ hd.wk.wk hp)
      exact hn.eqTrans Prf.hyp0.eqSymm
    · exact (zero_value_congr _ _ _ hd.wk.wk (product_commute d x u) (zero_multiply _ _ _ hd.wk.wk Prf.hyp0)).eqTrans Prf.hyp0.eqSymm

theorem positive_natural (d k : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] positive d (integer (ZT.ofNat k)) := by
  apply QuadraticIntegerEmbedding.integer_positive _ _ hd
  apply zle_of_comb (Groth.ι (Q.mk Γ k)-1)
  · simp only [ZT.toZ_ofNat,Q.mk_one,map_one]
  · simpa only [sl_def,Q.mk_one,map_one] using nn_sl hk
theorem sign_scale (d k x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] sign d (scale k x) ≐ sign d x :=
  (sign_congr _ _ _ hd (scale_product d k x)).eqTrans
    (positive_factor_sign _ _ _ hd (positive_natural _ _ hd hk))
theorem cross_scale_sign (d A B x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] equal (scale A x) (scale B y)) : Γ ⊢[PRAAx] sign d x ≐ sign d y :=
  (sign_scale d A x hd hA).eqSymm.eqTrans ((sign_congr _ _ _ hd h).eqTrans (sign_scale d B y hd hB))
theorem positive_scale_iff (d k x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] Fm.iff (positive d (scale k x)) (positive d x) :=
  .andI (.impI ((sign_scale d k x hd hk).wk.eqSymm.eqTrans Prf.hyp0))
    (.impI ((sign_scale d k x hd hk).wk.eqTrans Prf.hyp0))
theorem zero_scale_iff (d k x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] Fm.iff (isZero d (scale k x)) (isZero d x) :=
  .andI (.impI ((sign_scale d k x hd hk).wk.eqSymm.eqTrans Prf.hyp0))
    (.impI ((sign_scale d k x hd hk).wk.eqTrans Prf.hyp0))

def output (d k x : PTm n) : PTm n := pairT (scale k x) (pairT (sign d (scale k x)) (sign d x))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (d k x : PTm n) : PTm n := ap3 outputF d k x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d k x : PTm n) :
    Syn.subst σ (output d k x) = output (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d k x : PTm n) :
    Syn.subst σ (run d k x) = run (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by simp [run]
theorem program_at (d k x : PTm n) : Γ ⊢[PRAAx] run d k x ≐ output d k x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![d,k,x]
theorem returned_scale (d k x : PTm n) : Γ ⊢[PRAAx] fstT (run d k x) ≐ scale k x :=
  (congrFst (program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_scaled_sign (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d k x)) ≐ sign d (scale k x) :=
  (congrFst ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_original_sign (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d k x)) ≐ sign d x :=
  (congrSnd ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_equal_signs (d k x : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] fstT (sndT (run d k x)) ≐ sndT (sndT (run d k x)) :=
  (returned_scaled_sign _ _ _).eqTrans ((sign_scale _ _ _ hd hk).eqTrans (returned_original_sign _ _ _).eqSymm)

theorem actual_positive_factor_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ positive (var 0) (var 1) ⟶ sign (var 0) (multiply (var 0) (var 1) (var 2)) ≐ sign (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (positive_factor_sign _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_positive_integer_scale_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶ sign (var 0) (scale (var 1) (var 2)) ≐ sign (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (sign_scale _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cross_scale_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ le one (var 1) ⟶ le one (var 2) ⟶ equal (scale (var 1) (var 3)) (scale (var 2) (var 4)) ⟶
      sign (var 0) (var 3) ≐ sign (var 0) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (cross_scale_sign _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_positive_scale_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶ Fm.iff (positive (var 0) (scale (var 1) (var 2))) (positive (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (positive_scale_iff _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_zero_scale_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶ Fm.iff (isZero (var 0) (scale (var 1) (var 2))) (isZero (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (zero_scale_iff _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_integer_scale_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_scale_signs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶ fstT (sndT (run (var 0) (var 1) (var 2))) ≐ sndT (sndT (run (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (returned_equal_signs _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticPositiveScaling
