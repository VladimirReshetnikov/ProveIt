import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootProduct

/-!
# Runtime Horner perturbation from actual coefficient errors

The coefficient-error step of finite-demand source04 `lem:product-stability`.
Lists use descending degree order. The leading coefficients agree, while
the remaining coefficients satisfy individually checked squared-norm bounds.
Every degree and prefix index is an internal numerical variable.

For rational points with denominator `D`, the cleared coefficient list has
ith entry `D^i C_i`. Its ordinary Horner evaluation at the integer numerator
is the homogeneous evaluation numerator. The bound below retains the exact
factor `N R^(N-1)`, with no rounding of the rational radius `R/D`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialPerturbation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im add mul scale zeroCode normSq bounded bounded_add bounded_mul bounded_scale bounded_mono)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (sub equal equal_of_values equal_re equal_im equal_of_code equal_trans equal_symm
    values_of_code re_add im_add re_mul im_mul re_sub im_sub re_scale im_scale re_zero im_zero normSq_equal)
open LeanProofs.IPRA.Analysis.GaussianRootProduct
  (padded padded_inside horner hornerF horner_zero horner_succ evaluate subst_horner subst_padded)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def residual (F G z k : PTm n) : PTm n := sub (horner G z k) (horner F z k)
def budget (D R δ k : PTm n) : PTm n := D*k*pw R (pred k)*δ

@[simp] theorem subst_residual {m : ℕ} (σ : Fin n → PTm m) (F G z k : PTm n) :
    Syn.subst σ (residual F G z k) = residual (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ z) (Syn.subst σ k) := by simp [residual]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (D R δ k : PTm n) :
    Syn.subst σ (budget D R δ k) = budget (Syn.subst σ D) (Syn.subst σ R)
      (Syn.subst σ δ) (Syn.subst σ k) := by simp [budget]

theorem power_positive (R k : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx] le one (pw R k) := by
  have h := AnalyticNumberTheory.Valuation.pw_pos' (Analysis.RationalIntegerNormalization.positive_form hR) k
  exact le_congr (.eqRefl _) h.eqSymm (zero_lt_succ _)

theorem budget_zero (D R δ : PTm n) : Γ ⊢[PRAAx] budget D R δ zero ≐ zero := by unfold budget; ipra_ring

theorem budget_succ (D R δ k : PTm n) : Γ ⊢[PRAAx]
    budget D R δ (succ k) ≐ D*succ k*pw R k*δ := by
  unfold budget
  exact congrMul (congrMul (.eqRefl _) (congrAp2 powF (pred_succ k) (.eqRefl _))) (.eqRefl _)

/-- The exact one-step domination, including prefix zero and zero error. -/
theorem budget_step (D R δ k : PTm n) (hDR : Γ ⊢[PRAAx] le D R)
    (_hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    le (budget D R δ k*R+pw D (succ k)*δ) (budget D R δ (succ k)) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have hk := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := k ≐ zero)
    have kb : (k ≐ zero) :: Γ ⊢[PRAAx] budget D R δ k ≐ zero := by
      apply deriveNat
      unfold budget
      ipra_simps
      rw [natEq hk]
      ipra_simps
      ring
    have p : (k ≐ zero) :: Γ ⊢[PRAAx] pw D (succ k) ≐ D :=
      (congrAp2 powF (congrSucc hk) (.eqRefl _)).eqTrans (pw_one D)
    have q : (k ≐ zero) :: Γ ⊢[PRAAx] budget D R δ (succ k) ≐ D*δ :=
      (budget_succ D R δ k).eqTrans (by
        have a := natEq hk
        have b := natEq ((congrAp2 powF hk (.eqRefl R)).eqTrans (pw_zero R))
        apply deriveNat; ipra_simps; rw [a,b]; ring)
    exact le_congr ((congrAdd (congrMul kb (.eqRefl _)) (congrMul p (.eqRefl _))).eqTrans
      ((congrAdd (zero_mul _) (.eqRefl _)).eqTrans (zero_add _))).eqSymm q.eqSymm (le_refl _)
  · have hk := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := k ≐ succ (pred k))
    have kp : (k ≐ succ (pred k)) :: Γ ⊢[PRAAx] pw R k ≐ pw R (pred k)*R :=
      (congrAp2 powF hk (.eqRefl _)).eqTrans (pw_succ _ _)
    have dp : (k ≐ succ (pred k)) :: Γ ⊢[PRAAx] le (pw D (succ k)) (D*pw R k) :=
      le_congr (pw_succ D k).eqSymm (mul_comm _ _)
        (mul_le_mul_right D (pw_le_pw k hDR.wk))
    have term := mul_le_mul_right δ dp
    have add := add_le_add_right (budget D R δ k*R) term
    have add' := le_congr (add_comm _ _) (add_comm _ _) add
    have endEq : (k ≐ succ (pred k)) :: Γ ⊢[PRAAx]
        budget D R δ k*R+(D*pw R k)*δ ≐ budget D R δ (succ k) := by
      have p := natEq kp
      have q := natEq (budget_succ (Γ := (k ≐ succ (pred k)) :: Γ) D R δ k)
      apply deriveNat; unfold budget at *; ipra_simps
      rw [p] at q ⊢
      linear_combination -q
    exact le_congr (.eqRefl _) endEq add'

theorem residual_succ (F G z k : PTm n) : Γ ⊢[PRAAx]
    equal (residual F G z (succ k))
      (add (mul (residual F G z k) z) (sub (padded G k) (padded F k))) := by
  have g := values_of_code (horner_succ (Γ := Γ) G z k)
  have f := values_of_code (horner_succ (Γ := Γ) F z k)
  apply equal_of_values
  · simp only [residual,re_sub,re_add,re_mul,im_sub]
    rw [g.1,f.1]
    simp only [re_add,re_mul]
    ring
  · simp only [residual,im_sub,im_add,re_sub,re_mul,im_mul]
    rw [g.2,f.2]
    simp only [im_add,im_mul]
    ring

def weightedErrors (F G N D δ : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    bounded (sub (entry (Syn.shift G) (succ (var 0))) (entry (Syn.shift F) (succ (var 0))))
      (pw (Syn.shift D) (succ (var 0))*Syn.shift δ))

@[simp] theorem subst_weightedErrors {m : ℕ} (σ : Fin n → PTm m) (F G N D δ : PTm n) :
    (weightedErrors F G N D δ).subst σ = weightedErrors (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ δ) := by
  simp [weightedErrors,Syn.subst_shift,Syn.shift_subst]

theorem weighted_error_at (F G N D δ j : PTm n)
    (h : Γ ⊢[PRAAx] weightedErrors F G N D δ) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] bounded (sub (entry G (succ j)) (entry F (succ j))) (pw D (succ j)*δ) := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶
      bounded (sub (entry G (succ j)) (entry F (succ j))) (pw D (succ j)*δ) := by
    simpa only [weightedErrors,Fm.subst_imp,subst_lt,ComplexLogarithmRemainder.subst_bounded,
      GaussianRootAlgebra.subst_sub,subst_entry,subst_ap2,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j h
  exact .impE rule hj

theorem residual_one (F G z : PTm n)
    (hF : Γ ⊢[PRAAx] le one (length F)) (hG : Γ ⊢[PRAAx] le one (length G))
    (hLead : Γ ⊢[PRAAx] equal (entry G zero) (entry F zero)) :
    Γ ⊢[PRAAx] equal (residual F G z one) zeroCode := by
  have step := residual_succ (Γ := Γ) F G z zero
  have g := values_of_code (horner_zero (Γ := Γ) G z)
  have f := values_of_code (horner_zero (Γ := Γ) F z)
  have pg := padded_inside (Γ := Γ) G zero hG
  have pf := padded_inside (Γ := Γ) F zero hF
  have er := equal_re step; have ei := equal_im step
  apply equal_of_values
  · simp only [residual,re_sub,re_zero]
    simp only [re_add,re_mul,residual,re_sub,im_sub] at er
    rw [g.1,g.2,f.1,f.2,re_zero,im_zero,equal_re pg,equal_re pf,equal_re hLead] at er
    linear_combination er
  · simp only [residual,im_sub,im_zero]
    simp only [im_add,im_mul,residual,re_sub,im_sub] at ei
    rw [g.1,g.2,f.1,f.2,re_zero,im_zero,equal_im pg,equal_im pf,equal_im hLead] at ei
    linear_combination ei

theorem sub_equal {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] equal a a')
    (hb : Γ ⊢[PRAAx] equal b b') : Γ ⊢[PRAAx] equal (sub a b) (sub a' b') := by
  apply equal_of_values
  · simp only [re_sub]; rw [equal_re ha,equal_re hb]
  · simp only [im_sub]; rw [equal_im ha,equal_im hb]

theorem bounded_of_equal {a b R : PTm n} (h : Γ ⊢[PRAAx] equal a b)
    (hb : Γ ⊢[PRAAx] bounded b R) : Γ ⊢[PRAAx] bounded a R :=
  le_congr (normSq_equal h).eqSymm (.eqRefl _) hb

def prefixBound (F G z N D R δ k : PTm n) : Fm PTm n :=
  le k N ⟶ bounded (residual F G z (succ k)) (budget D R δ k)

@[simp] theorem subst_prefixBound {m : ℕ} (σ : Fin n → PTm m) (F G z N D R δ k : PTm n) :
    (prefixBound F G z N D R δ k).subst σ = prefixBound (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ δ) (Syn.subst σ k) := by
  simp [prefixBound]

/-- The prefix proof uses only the actual coefficient comparisons. The
Horner recurrence and the entire evaluation bound are conclusions. -/
theorem weighted_horner_bound (F G z N D R δ k : PTm n)
    (hF : Γ ⊢[PRAAx] le (succ N) (length F)) (hG : Γ ⊢[PRAAx] le (succ N) (length G))
    (hLead : Γ ⊢[PRAAx] equal (entry G zero) (entry F zero))
    (hz : Γ ⊢[PRAAx] bounded z R) (hDR : Γ ⊢[PRAAx] le D R) (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] weightedErrors F G N D δ) : Γ ⊢[PRAAx] prefixBound F G z N D R δ k := by
  have all : Γ ⊢[PRAAx] .all (prefixBound (Syn.shift F) (Syn.shift G) (Syn.shift z)
      (Syn.shift N) (Syn.shift D) (Syn.shift R) (Syn.shift δ) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      have lead := residual_one (Γ := le zero N :: Γ) F G z
        (le_trans (zero_lt_succ N) hF.wk) (le_trans (zero_lt_succ N) hG.wk) hLead.wk
      have l := (normSq_equal lead).eqTrans ComplexLogarithmRemainder.normSq_zero
      have r := (congrMul (budget_zero (Γ := le zero N :: Γ) D R δ) (budget_zero D R δ)).eqTrans (zero_mul zero)
      exact le_congr l.eqSymm r.eqSymm (le_refl zero)
    · simp only [subst_prefixBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := prefixBound (Syn.shift F) (Syn.shift G) (Syn.shift z) (Syn.shift N)
        (Syn.shift D) (Syn.shift R) (Syn.shift δ) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
      have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
      have ih : Δ ⊢[PRAAx] bounded
          (residual (Syn.shift F) (Syn.shift G) (Syn.shift z) (succ (var 0)))
          (budget (Syn.shift D) (Syn.shift R) (Syn.shift δ) (var 0)) := .impE Prf.hyp1 bound
      have shapeF : Δ ⊢[PRAAx] le (succ (Syn.shift N)) (length (Syn.shift F)) := by
        simpa only [Δ,I,Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hF.shift.wk.wk
      have shapeG : Δ ⊢[PRAAx] le (succ (Syn.shift N)) (length (Syn.shift G)) := by
        simpa only [Δ,I,Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hG.shift.wk.wk
      have errors : Δ ⊢[PRAAx] weightedErrors (Syn.shift F) (Syn.shift G) (Syn.shift N)
          (Syn.shift D) (Syn.shift δ) := by
        simpa only [Δ,I,Fm.shift,subst_weightedErrors,Syn.shift] using hErrors.shift.wk.wk
      have point : Δ ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift R) := by
        simpa only [Δ,I,Fm.shift,ComplexLogarithmRemainder.subst_bounded,Syn.shift] using hz.shift.wk.wk
      have dr : Δ ⊢[PRAAx] le (Syn.shift D) (Syn.shift R) := by
        simpa only [Δ,I,Fm.shift,subst_le,Syn.shift] using hDR.shift.wk.wk
      have radius : Δ ⊢[PRAAx] le one (Syn.shift R) := by
        simpa only [Δ,I,Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hR.shift.wk.wk
      have coeff := weighted_error_at _ _ _ _ _ (var 0) errors Prf.hyp0
      have same := sub_equal
        (padded_inside (Syn.shift G) (succ (var 0)) (lt_of_le_of_lt Prf.hyp0 shapeG))
        (padded_inside (Syn.shift F) (succ (var 0)) (lt_of_le_of_lt Prf.hyp0 shapeF))
      have sum := bounded_add (bounded_mul ih point) (bounded_of_equal same coeff)
      exact bounded_of_equal (residual_succ _ _ _ _)
        (bounded_mono sum (budget_step _ _ _ _ dr radius))
  simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all

/-! The actual common-point-denominator coefficient transformation. -/

def clearData (C D : PTm n) : PTm n := pairT C D
def clearBody : PTm 2 := scale (pw (sndT (var 1)) (var 0)) (entry (fstT (var 1)) (var 0))
def clear (C D : PTm n) : PTm n := sequence clearBody (length C) (clearData C D)
def H (C z D k : PTm n) : PTm n := horner (clear C D) z k

@[simp] theorem subst_clearData {m : ℕ} (σ : Fin n → PTm m) (C D : PTm n) :
    Syn.subst σ (clearData C D) = clearData (Syn.subst σ C) (Syn.subst σ D) := by simp [clearData]
@[simp] theorem subst_clear {m : ℕ} (σ : Fin n → PTm m) (C D : PTm n) :
    Syn.subst σ (clear C D) = clear (Syn.subst σ C) (Syn.subst σ D) := by simp [clear]
@[simp] theorem subst_H {m : ℕ} (σ : Fin n → PTm m) (C z D k : PTm n) :
    Syn.subst σ (H C z D k) = H (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ k) := by simp [H]

theorem clear_body_at (C D i : PTm n) : Γ ⊢[PRAAx]
    inst2 clearBody i (clearData C D) ≐ scale (pw D i) (entry C i) := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (scale (pw (var 1) (var 2)) (entry (var 0) (var 2)) : PTm 3)
    (σ := ![fstT (clearData C D),sndT (clearData C D),i]) (σ' := ![C,D,i])
    (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa only [clearBody,inst2,ComplexLogarithmRemainder.subst_scale,subst_ap2,subst_entry,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using e

theorem clear_length (C D : PTm n) : Γ ⊢[PRAAx] length (clear C D) ≐ length C := sequence_length _ _ _
theorem clear_lookup (C D i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) :
    Γ ⊢[PRAAx] entry (clear C D) i ≐ scale (pw D i) (entry C i) :=
  (sequence_decode clearBody hi).eqTrans (clear_body_at C D i)

theorem H_zero (C z D : PTm n) : Γ ⊢[PRAAx] H C z D zero ≐ zeroCode := horner_zero _ _
theorem H_succ (C z D k : PTm n) (hk : Γ ⊢[PRAAx] lt k (length C)) : Γ ⊢[PRAAx]
    equal (H C z D (succ k)) (add (mul (H C z D k) z) (scale (pw D k) (entry C k))) := by
  have coeff := equal_trans
    (padded_inside (clear C D) k (lt_congr (.eqRefl _) (clear_length C D).eqSymm hk))
    (equal_of_code (clear_lookup C D k hk))
  exact equal_trans (equal_of_code (horner_succ _ _ _))
    (GaussianRootAlgebra.add_equal (GaussianRootAlgebra.equal_refl _) coeff)

theorem clear_leading (C D : PTm n) (hC : Γ ⊢[PRAAx] le one (length C)) :
    Γ ⊢[PRAAx] equal (entry (clear C D) zero) (entry C zero) := by
  have v := values_of_code (clear_lookup C D zero hC)
  have p := natEq (pw_zero (Γ := Γ) D)
  apply equal_of_values
  · rw [v.1,re_scale,p]; ipra_simps; ring
  · rw [v.2,im_scale,p]; ipra_simps; ring

theorem scale_sub (s a b : PTm n) : Γ ⊢[PRAAx]
    equal (sub (scale s a) (scale s b)) (scale s (sub a b)) := by
  apply equal_of_values <;> simp only [re_sub,im_sub,re_scale,im_scale] <;> ring

def coefficientErrors (F G N δ : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    bounded (sub (entry (Syn.shift G) (succ (var 0))) (entry (Syn.shift F) (succ (var 0)))) (Syn.shift δ))

@[simp] theorem subst_coefficientErrors {m : ℕ} (σ : Fin n → PTm m) (F G N δ : PTm n) :
    (coefficientErrors F G N δ).subst σ = coefficientErrors (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ N) (Syn.subst σ δ) := by simp [coefficientErrors,Syn.subst_shift,Syn.shift_subst]

theorem coefficient_error_at (F G N δ j : PTm n)
    (h : Γ ⊢[PRAAx] coefficientErrors F G N δ) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] bounded (sub (entry G (succ j)) (entry F (succ j))) δ := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ bounded (sub (entry G (succ j)) (entry F (succ j))) δ := by
    simpa only [coefficientErrors,Fm.subst_imp,subst_lt,ComplexLogarithmRemainder.subst_bounded,
      GaussianRootAlgebra.subst_sub,subst_entry,ConciseIPRA.PTm.subst_succ,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j h
  exact .impE rule hj

/-- Every weighted error is produced from an original coefficient bound
and the actual transformed lookup; it is not a caller-supplied residual. -/
theorem clear_errors (F G N D δ : PTm n)
    (hF : Γ ⊢[PRAAx] le (succ N) (length F)) (hG : Γ ⊢[PRAAx] le (succ N) (length G))
    (hErrors : Γ ⊢[PRAAx] coefficientErrors F G N δ) :
    Γ ⊢[PRAAx] weightedErrors (clear F D) (clear G D) N D δ := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have fshape : Δ ⊢[PRAAx] le (succ (Syn.shift N)) (length (Syn.shift F)) := by
    simpa only [Δ,Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hF.shift.wk
  have gshape : Δ ⊢[PRAAx] le (succ (Syn.shift N)) (length (Syn.shift G)) := by
    simpa only [Δ,Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hG.shift.wk
  have errors : Δ ⊢[PRAAx] coefficientErrors (Syn.shift F) (Syn.shift G) (Syn.shift N) (Syn.shift δ) := by
    simpa only [Δ,Fm.shift,subst_coefficientErrors,Syn.shift] using hErrors.shift.wk
  have frange : Δ ⊢[PRAAx] lt (succ (var 0)) (length (Syn.shift F)) :=
    lt_of_lt_of_le ((succ_monus_succ (succ (var 0)) (Syn.shift N)).eqTrans Prf.hyp0) fshape
  have grange : Δ ⊢[PRAAx] lt (succ (var 0)) (length (Syn.shift G)) :=
    lt_of_lt_of_le ((succ_monus_succ (succ (var 0)) (Syn.shift N)).eqTrans Prf.hyp0) gshape
  have same := equal_trans (sub_equal
    (equal_of_code (clear_lookup (Syn.shift G) (Syn.shift D) (succ (var 0)) grange))
    (equal_of_code (clear_lookup (Syn.shift F) (Syn.shift D) (succ (var 0)) frange))) (scale_sub _ _ _)
  have term := bounded_scale (pw (Syn.shift D) (succ (var 0)))
    (coefficient_error_at _ _ _ _ (var 0) errors Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_clear] using bounded_of_equal same term

/-- Cleared runtime evaluation bound with the exact rational-radius budget.
For coefficient denominator E and point denominator D, division by E D^N
gives `N (R/D)^(N-1) (δ/E)`. -/
theorem homogeneous_horner_bound (F G z N D R δ : PTm n)
    (hF : Γ ⊢[PRAAx] le (succ N) (length F)) (hG : Γ ⊢[PRAAx] le (succ N) (length G))
    (hLead : Γ ⊢[PRAAx] equal (entry G zero) (entry F zero))
    (hz : Γ ⊢[PRAAx] bounded z R) (hDR : Γ ⊢[PRAAx] le D R) (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors F G N δ) : Γ ⊢[PRAAx]
    bounded (sub (H G z D (succ N)) (H F z D (succ N))) (budget D R δ N) := by
  have leading := equal_trans (clear_leading G D (le_trans (zero_lt_succ N) hG))
    (equal_trans hLead (equal_symm (clear_leading F D (le_trans (zero_lt_succ N) hF))))
  exact .impE (weighted_horner_bound (clear F D) (clear G D) z N D R δ N
    (le_congr (.eqRefl _) (clear_length F D).eqSymm hF)
    (le_congr (.eqRefl _) (clear_length G D).eqSymm hG) leading hz hDR hR
    (clear_errors F G N D δ hF hG hErrors)) (le_refl N)

/-! Ordinary integer evaluation is a specialization with no coefficient
transform in its conclusion. -/

theorem one_power (k : PTm n) : Γ ⊢[PRAAx] pw one k ≐ one := by
  have all : Γ ⊢[PRAAx] .all (pw one (var 0) ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa using pw_zero (Γ := Γ) (one : PTm n)
    · simp only [Fm.subst_eq,subst_ap2,Syn.subst_var,Syn.repl_zero,
        ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]
      exact (pw_succ _ _).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul one))
  simpa using Prf.allE k all

theorem unit_weighted_errors (F G N δ : PTm n) (h : Γ ⊢[PRAAx] coefficientErrors F G N δ) :
    Γ ⊢[PRAAx] weightedErrors F G N one δ := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have errors : Δ ⊢[PRAAx] coefficientErrors (Syn.shift F) (Syn.shift G) (Syn.shift N) (Syn.shift δ) := by
    simpa only [Δ,Fm.shift,subst_coefficientErrors,Syn.shift] using h.shift.wk
  have term := coefficient_error_at _ _ _ _ (var 0) errors Prf.hyp0
  have radius : Δ ⊢[PRAAx] pw one (succ (var 0))*Syn.shift δ ≐ Syn.shift δ :=
    (congrMul (one_power _) (.eqRefl _)).eqTrans (one_mul _)
  simpa only [Δ,bounded,one,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    le_congr (.eqRefl _) (congrMul radius radius).eqSymm term

theorem integer_horner_bound (F G z N R δ : PTm n)
    (hF : Γ ⊢[PRAAx] le (succ N) (length F)) (hG : Γ ⊢[PRAAx] le (succ N) (length G))
    (hLead : Γ ⊢[PRAAx] equal (entry G zero) (entry F zero))
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors F G N δ) : Γ ⊢[PRAAx]
    bounded (residual F G z (succ N)) (N*pw R (pred N)*δ) := by
  have h := Prf.impE (weighted_horner_bound F G z N one R δ N hF hG hLead hz hR hR
    (unit_weighted_errors F G N δ hErrors)) (le_refl N)
  have r : Γ ⊢[PRAAx] budget one R δ N ≐ N*pw R (pred N)*δ := by unfold budget; ipra_ring
  exact le_congr (.eqRefl _) (congrMul r r) h

theorem evaluation_bound (F G z N R δ : PTm n)
    (hF : Γ ⊢[PRAAx] length F ≐ succ N) (hG : Γ ⊢[PRAAx] length G ≐ succ N)
    (hLead : Γ ⊢[PRAAx] equal (entry G zero) (entry F zero))
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors F G N δ) : Γ ⊢[PRAAx]
    bounded (sub (evaluate G z) (evaluate F z)) (N*pw R (pred N)*δ) := by
  have bound := integer_horner_bound F G z N R δ
    (le_congr (.eqRefl _) hF.eqSymm (le_refl _)) (le_congr (.eqRefl _) hG.eqSymm (le_refl _)) hLead hz hR hErrors
  have same := sub_equal
    (equal_of_code (congrAp3 hornerF hG (.eqRefl G) (.eqRefl z)))
    (equal_of_code (congrAp3 hornerF hF (.eqRefl F) (.eqRefl z)))
  exact bounded_of_equal same bound

/-- Actual runtime root products supply their own monicity and lengths. -/
theorem product_evaluation_bound (S T z N R δ : PTm n)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors (GaussianRootProduct.coefficients S N)
      (GaussianRootProduct.coefficients T N) N δ) : Γ ⊢[PRAAx]
    bounded (sub (evaluate (GaussianRootProduct.coefficients T N) z)
      (evaluate (GaussianRootProduct.coefficients S N) z)) (N*pw R (pred N)*δ) :=
  evaluation_bound _ _ _ _ _ _ (GaussianRootProduct.coefficients_length _ _)
    (GaussianRootProduct.coefficients_length _ _)
    (equal_trans (GaussianRootProduct.coefficients_monic T N)
      (equal_symm (GaussianRootProduct.coefficients_monic S N))) hz hR hErrors

/-- At an actual listed root the first product evaluation vanishes, so the
coefficient bound gives the second product's genuine evaluation bound. -/
theorem root_evaluation_bound (S T N j R δ : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hz : Γ ⊢[PRAAx] bounded (entry S j) R) (hR : Γ ⊢[PRAAx] le one R)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors (GaussianRootProduct.coefficients S N)
      (GaussianRootProduct.coefficients T N) N δ) : Γ ⊢[PRAAx]
    bounded (evaluate (GaussianRootProduct.coefficients T N) (entry S j)) (N*pw R (pred N)*δ) := by
  have zeroEval := GaussianRootProduct.listed_root_zero (Γ := Γ) S N j hj
  have bound := product_evaluation_bound S T (entry S j) N R δ hz hR hErrors
  have same : Γ ⊢[PRAAx] equal
      (sub (evaluate (GaussianRootProduct.coefficients T N) (entry S j))
        (evaluate (GaussianRootProduct.coefficients S N) (entry S j)))
      (evaluate (GaussianRootProduct.coefficients T N) (entry S j)) := by
    apply equal_of_values
    · simp only [re_sub]; rw [equal_re zeroEval,re_zero]; ring
    · simp only [im_sub]; rw [equal_im zeroEval,im_zero]; ring
  exact bounded_of_equal (equal_symm same) bound

/-! Fixed primitive recursive program metadata and closed numerical schemes. -/

def clearF : PR 2 := PTm.toPR (clear (var 0) (var 1))
def HF : PR 4 := PTm.toPR (H (var 0) (var 1) (var 2) (var 3))

theorem clear_at (C D : PTm n) : Γ ⊢[PRAAx] ap2 clearF C D ≐ clear C D := by
  simpa [clearF,ap2] using toPR_eq (Γ := Γ) (clear (var 0) (var 1) : PTm 2) ![C,D]
theorem H_at (C z D k : PTm n) : Γ ⊢[PRAAx]
    ConciseIPRA.PTm.app HF ![C,z,D,k] ≐ H C z D k := by
  simpa [HF] using toPR_eq (Γ := Γ) (H (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,z,D,k]

def homogeneousInput (F G z N D R δ : PTm n) : Fm PTm n :=
  le (succ N) (length F) ⋏ (le (succ N) (length G) ⋏
    (equal (entry G zero) (entry F zero) ⋏ (bounded z R ⋏
      (le D R ⋏ (le one R ⋏ coefficientErrors F G N δ)))))

theorem homogeneous_from_input (F G z N D R δ : PTm n)
    (h : Γ ⊢[PRAAx] homogeneousInput F G z N D R δ) : Γ ⊢[PRAAx]
    bounded (sub (H G z D (succ N)) (H F z D (succ N))) (budget D R δ N) :=
  homogeneous_horner_bound F G z N D R δ (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))))

theorem budget_one (D R δ : PTm n) : Γ ⊢[PRAAx] budget D R δ one ≐ D*δ :=
  (budget_succ D R δ zero).eqTrans (by
    have p := natEq (pw_zero (Γ := Γ) R)
    apply deriveNat; ipra_simps; rw [p]; ring)

theorem budget_zero_error (D R N : PTm n) : Γ ⊢[PRAAx] budget D R zero N ≐ zero := by
  unfold budget
  ipra_ring

theorem zero_error_norm (F G z N D R : PTm n)
    (h : Γ ⊢[PRAAx] homogeneousInput F G z N D R zero) : Γ ⊢[PRAAx]
    normSq (sub (H G z D (succ N)) (H F z D (succ N))) ≐ zero := by
  have bound := homogeneous_from_input F G z N D R zero h
  have r := (congrMul (budget_zero_error (Γ := Γ) D R N) (budget_zero_error D R N)).eqTrans (zero_mul zero)
  exact le_antisymm (le_congr (.eqRefl _) r bound) (zero_le _)

theorem homogeneous_perturbation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (homogeneousInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (sub (H (var 1) (var 2) (var 4) (succ (var 3)))
        (H (var 0) (var 2) (var 4) (succ (var 3)))) (budget (var 4) (var 5) (var 6) (var 3))) :=
  closeUniv 7 (.impI (homogeneous_from_input _ _ _ _ _ _ _ Prf.hyp0))

theorem zero_coefficient_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (homogeneousInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) zero ⟶
      normSq (sub (H (var 1) (var 2) (var 4) (succ (var 3)))
        (H (var 0) (var 2) (var 4) (succ (var 3)))) ≐ zero) :=
  closeUniv 6 (.impI (zero_error_norm _ _ _ _ _ _ Prf.hyp0))

theorem integer_product_perturbation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (bounded (var 2) (var 4) ⟶ le one (var 4) ⟶
      coefficientErrors (GaussianRootProduct.coefficients (var 0) (var 3))
        (GaussianRootProduct.coefficients (var 1) (var 3)) (var 3) (var 5) ⟶
      bounded (sub (evaluate (GaussianRootProduct.coefficients (var 1) (var 3)) (var 2))
        (evaluate (GaussianRootProduct.coefficients (var 0) (var 3)) (var 2)))
          (var 3*pw (var 4) (pred (var 3))*var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (product_evaluation_bound _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem listed_root_coefficient_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 3) (var 2) ⟶ bounded (entry (var 0) (var 3)) (var 4) ⟶ le one (var 4) ⟶
      coefficientErrors (GaussianRootProduct.coefficients (var 0) (var 2))
        (GaussianRootProduct.coefficients (var 1) (var 2)) (var 2) (var 5) ⟶
      bounded (evaluate (GaussianRootProduct.coefficients (var 1) (var 2)) (entry (var 0) (var 3)))
        (var 2*pw (var 4) (pred (var 2))*var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (root_evaluation_bound _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

theorem clearing_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 clearF (var 0) (var 1) ≐ clear (var 0) (var 1)) ⋏
      (length (clear (var 0) (var 1)) ≐ length (var 0))) :=
  closeUniv 2 (.andI (clear_at _ _) (clear_length _ _))

theorem homogeneous_evaluator_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ConciseIPRA.PTm.app HF ![var 0,var 1,var 2,var 3] ≐ H (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (H_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialPerturbation
