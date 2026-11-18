import IPRADerivations.Analysis.GaussianPolynomialPerturbation

/-!
# Actual constant coefficient scaling and homogeneous Horner linearity

Support for the rational finite product-stability theorem. A true sequence
program scales every coefficient by a numerical scalar. Its original lookup,
length, coefficient-error bound and runtime Horner linearity are proved.
No evaluated-polynomial identity is supplied as an input.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialScaling

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im scale normSq bounded)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_of_values equal_re equal_im equal_of_code equal_trans equal_symm values_of_code
    re_add im_add re_mul im_mul re_scale im_scale re_zero im_zero normSq_equal)
open LeanProofs.IPRA.Analysis.GaussianPolynomialPerturbation (H coefficientErrors)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def scaleBody : PTm 2 := scale (fstT (var 1)) (entry (sndT (var 1)) (var 0))
def scaled (C B : PTm n) : PTm n := sequence scaleBody (length C) (pairT B C)

@[simp] theorem subst_scaled {m : ℕ} (σ : Fin n → PTm m) (C B : PTm n) :
    Syn.subst σ (scaled C B) = scaled (Syn.subst σ C) (Syn.subst σ B) := by simp [scaled]

theorem scale_body_at (C B i : PTm n) : Γ ⊢[PRAAx]
    inst2 scaleBody i (pairT B C) ≐ scale B (entry C i) := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (scale (var 0) (entry (var 1) (var 2)) : PTm 3)
    (σ := ![fstT (pairT B C),sndT (pairT B C),i]) (σ' := ![B,C,i])
    (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa only [scaleBody,inst2,ComplexLogarithmRemainder.subst_scale,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using e

theorem scaled_length (C B : PTm n) : Γ ⊢[PRAAx] length (scaled C B) ≐ length C := sequence_length _ _ _
theorem scaled_lookup (C B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) :
    Γ ⊢[PRAAx] entry (scaled C B) i ≐ scale B (entry C i) :=
  (sequence_decode scaleBody hi).eqTrans (scale_body_at C B i)

theorem scale_equal (B : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] equal a b) : Γ ⊢[PRAAx] equal (scale B a) (scale B b) := by
  apply equal_of_values
  · simp only [re_scale]; rw [equal_re h]
  · simp only [im_scale]; rw [equal_im h]

theorem scale_scale (B E a : PTm n) : Γ ⊢[PRAAx] equal (scale B (scale E a)) (scale (B*E) a) := by
  apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring

theorem scaled_leading (F G B : PTm n)
    (hF : Γ ⊢[PRAAx] le one (length F)) (hG : Γ ⊢[PRAAx] le one (length G))
    (h : Γ ⊢[PRAAx] equal (entry G zero) (entry F zero)) :
    Γ ⊢[PRAAx] equal (entry (scaled G B) zero) (entry (scaled F B) zero) :=
  equal_trans (equal_of_code (scaled_lookup G B zero hG))
    (equal_trans (scale_equal B h) (equal_symm (equal_of_code (scaled_lookup F B zero hF))))

def prefixLaw (C B z D k : PTm n) : Fm PTm n := le k (length C) ⟶ equal (H (scaled C B) z D k) (scale B (H C z D k))

@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (C B z D k : PTm n) :
    (prefixLaw C B z D k).subst σ = prefixLaw (Syn.subst σ C) (Syn.subst σ B)
      (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ k) := by simp [prefixLaw]

theorem homogeneous_zero (C B z D : PTm n) : Γ ⊢[PRAAx]
    equal (H (scaled C B) z D zero) (scale B (H C z D zero)) := by
  have a := values_of_code (GaussianPolynomialPerturbation.H_zero (Γ := Γ) (scaled C B) z D)
  have b := values_of_code (GaussianPolynomialPerturbation.H_zero (Γ := Γ) C z D)
  apply equal_of_values
  · rw [a.1,re_scale,b.1,re_zero]; ring
  · rw [a.2,im_scale,b.2,im_zero]; ring

theorem homogeneous_step (C B z D k : PTm n) (hk : Γ ⊢[PRAAx] lt k (length C))
    (h : Γ ⊢[PRAAx] equal (H (scaled C B) z D k) (scale B (H C z D k))) : Γ ⊢[PRAAx]
    equal (H (scaled C B) z D (succ k)) (scale B (H C z D (succ k))) := by
  have s := GaussianPolynomialPerturbation.H_succ (Γ := Γ) (scaled C B) z D k
    (lt_congr (.eqRefl _) (scaled_length C B).eqSymm hk)
  have c := GaussianPolynomialPerturbation.H_succ (Γ := Γ) C z D k hk
  have sr := equal_re s; have si := equal_im s
  have cr := equal_re c; have ci := equal_im c
  have ir := equal_re h; have ii := equal_im h
  have lookup := values_of_code (scaled_lookup (Γ := Γ) C B k hk)
  have lr := lookup.1; have li := lookup.2
  simp only [re_add,im_add,re_mul,im_mul,re_scale,im_scale] at sr si cr ci ir ii lr li
  apply equal_of_values
  · simp only [re_scale]
    linear_combination sr-𝔞(B)*cr+ZT.toZ Γ (re z)*ir-ZT.toZ Γ (im z)*ii+𝔞(pw D k)*lr
  · simp only [im_scale]
    linear_combination si-𝔞(B)*ci+ZT.toZ Γ (im z)*ir+ZT.toZ Γ (re z)*ii+𝔞(pw D k)*li

/-- QF induction proves the actual runtime homogeneous evaluator linear. -/
theorem homogeneous_linearity (C B z D k : PTm n) (hk : Γ ⊢[PRAAx] le k (length C)) :
    Γ ⊢[PRAAx] equal (H (scaled C B) z D k) (scale B (H C z D k)) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift B) (Syn.shift z) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨trivial,trivial⟩⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (homogeneous_zero C B z D)
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := prefixLaw (Syn.shift C) (Syn.shift B) (Syn.shift z) (Syn.shift D) (var 0)
      let Δ := le (succ (var 0)) (length (Syn.shift C)) :: I :: Γ.map Fm.shift
      exact homogeneous_step _ _ _ _ _ (Prf.hyp0 (Ax := PRAAx) (Γ := I :: Γ.map Fm.shift))
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C B z D k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all
  exact .impE rule hk

def crossErrors (F G N A B E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    le ((Syn.shift B*Syn.shift B)*normSq (GaussianRootAlgebra.sub
      (entry (Syn.shift G) (succ (var 0))) (entry (Syn.shift F) (succ (var 0)))))
      ((Syn.shift A*Syn.shift A)*(Syn.shift E*Syn.shift E)))

@[simp] theorem subst_crossErrors {m : ℕ} (σ : Fin n → PTm m) (F G N A B E : PTm n) :
    (crossErrors F G N A B E).subst σ = crossErrors (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ E) := by simp [crossErrors,Syn.subst_shift,Syn.shift_subst]

theorem cross_error_at (F G N A B E j : PTm n) (h : Γ ⊢[PRAAx] crossErrors F G N A B E)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    le ((B*B)*normSq (GaussianRootAlgebra.sub (entry G (succ j)) (entry F (succ j)))) ((A*A)*(E*E)) := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶
      le ((B*B)*normSq (GaussianRootAlgebra.sub (entry G (succ j)) (entry F (succ j)))) ((A*A)*(E*E)) := by
    simpa only [crossErrors,Fm.subst_imp,subst_lt,subst_le,PTm.subst_mul,
      ComplexLogarithmRemainder.subst_normSq,GaussianRootAlgebra.subst_sub,subst_entry,
      ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j h
  exact .impE rule hj

/-- A rational tolerance is cleared by the actual coefficient program,
retaining B exactly instead of rounding A/B to an integer. -/
theorem scaled_coefficient_errors (F G N A B E : PTm n)
    (hF : Γ ⊢[PRAAx] le (succ N) (length F)) (hG : Γ ⊢[PRAAx] le (succ N) (length G))
    (h : Γ ⊢[PRAAx] crossErrors F G N A B E) : Γ ⊢[PRAAx]
    coefficientErrors (scaled F B) (scaled G B) N (A*E) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have fs : Δ ⊢[PRAAx] le (succ (Syn.shift N)) (length (Syn.shift F)) := by
    simpa only [Δ,Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hF.shift.wk
  have gs : Δ ⊢[PRAAx] le (succ (Syn.shift N)) (length (Syn.shift G)) := by
    simpa only [Δ,Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hG.shift.wk
  have errors : Δ ⊢[PRAAx] crossErrors (Syn.shift F) (Syn.shift G) (Syn.shift N)
      (Syn.shift A) (Syn.shift B) (Syn.shift E) := by
    simpa only [Δ,Fm.shift,subst_crossErrors,Syn.shift] using h.shift.wk
  have fi : Δ ⊢[PRAAx] lt (succ (var 0)) (length (Syn.shift F)) :=
    lt_of_lt_of_le ((succ_monus_succ (succ (var 0)) (Syn.shift N)).eqTrans Prf.hyp0) fs
  have gi : Δ ⊢[PRAAx] lt (succ (var 0)) (length (Syn.shift G)) :=
    lt_of_lt_of_le ((succ_monus_succ (succ (var 0)) (Syn.shift N)).eqTrans Prf.hyp0) gs
  have eq := equal_trans (GaussianPolynomialPerturbation.sub_equal
    (equal_of_code (scaled_lookup (Syn.shift G) (Syn.shift B) (succ (var 0)) gi))
    (equal_of_code (scaled_lookup (Syn.shift F) (Syn.shift B) (succ (var 0)) fi)))
      (GaussianPolynomialPerturbation.scale_sub _ _ _)
  have norm := (normSq_equal eq).eqTrans (ComplexLogarithmRemainder.normSq_scale _ _)
  have value := cross_error_at _ _ _ _ _ _ (var 0) errors Prf.hyp0
  have radius : Δ ⊢[PRAAx] (Syn.shift A*Syn.shift A)*(Syn.shift E*Syn.shift E) ≐
      (Syn.shift A*Syn.shift E)*(Syn.shift A*Syn.shift E) := by ipra_ring
  simpa only [Δ,bounded,Syn.shift,subst_scaled,PTm.subst_mul] using
    le_congr norm.eqSymm radius value

def scaledF : PR 2 := PTm.toPR (scaled (var 0) (var 1))
theorem scaled_at (C B : PTm n) : Γ ⊢[PRAAx] ap2 scaledF C B ≐ scaled C B := by
  simpa [scaledF,ap2] using toPR_eq (Γ := Γ) (scaled (var 0) (var 1) : PTm 2) ![C,B]

theorem coefficient_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 scaledF (var 0) (var 1) ≐ scaled (var 0) (var 1)) ⋏ (length (scaled (var 0) (var 1)) ≐ length (var 0))) :=
  closeUniv 2 (.andI (scaled_at _ _) (scaled_length _ _))

theorem homogeneous_linearity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (length (var 0)) ⟶ equal (H (scaled (var 0) (var 1)) (var 2) (var 3) (var 4))
      (scale (var 1) (H (var 0) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (homogeneous_linearity _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialScaling
