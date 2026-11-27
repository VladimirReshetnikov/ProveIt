import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerAlgebra

/-!
# Actual Gaussian-rational coefficient scaling

A numerical sequence program multiplies each original coefficient by an
arbitrary original Gaussian-rational scalar. A quantifier-free induction
proves literal Horner linearity, uniformly in the numerical list length,
prefix, point and independently normalized scalar denominators. No input
canonicality or supplied evaluator identity is needed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul horner evaluate canonical represents positive_product
    qadd_represents qmul_represents represents_congr canonical_unique)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qmul_congr rescale_to qmul_zero_right)
open LeanProofs.IPRA.Analysis.GaussianRationalL1
  (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry subst_entry sequence subst_sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Distributivity for the actual independently normalized product codes. -/
theorem qmul_add (a b c : PTm n) : Γ ⊢[PRAAx]
    qmul a (qadd b c) ≐ qadd (qmul a b) (qmul a c) := by
  let E := rawDen a*rawDen b*rawDen c
  have d : Γ ⊢[PRAAx] le one E := positive_product _ _
    (positive_product _ _ (raw_den_positive a) (raw_den_positive b)) (raw_den_positive c)
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen b*rawDen c) E
    (raw_represents (Γ := Γ) a) (by unfold E; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen a*rawDen c) E
    (raw_represents (Γ := Γ) b) (by unfold E; ipra_ring)
  have hc := rescale_to c (rawGaussian c) (rawDen c) (rawDen a*rawDen b) E
    (raw_represents (Γ := Γ) c) (by unfold E; ipra_ring)
  have left := qmul_represents _ _ _ _ _ _ d d ha (qadd_represents _ _ _ _ _ d hb hc)
  have right := qadd_represents _ _ _ _ _ (positive_product E E d d)
    (qmul_represents _ _ _ _ _ _ d d ha hb) (qmul_represents _ _ _ _ _ _ d d ha hc)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.qadd_canonical _ _) (positive_product E E d d) (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,
    GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add]; ring

def scaleBody : PTm 2 := qmul (fstT (var 1)) (entry (sndT (var 1)) (var 0))
def scaled (C s : PTm n) : PTm n := sequence scaleBody (length C) (pairT s C)

ipra_subst scaled

theorem scale_body_at (C s i : PTm n) : Γ ⊢[PRAAx]
    inst2 scaleBody i (pairT s C) ≐ qmul s (entry C i) := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (qmul (var 0) (entry (var 1) (var 2)) : PTm 3)
    (σ := ![fstT (pairT s C),sndT (pairT s C),i]) (σ' := ![s,C,i])
    (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa only [scaleBody,inst2,GaussianRationalHorner.subst_qmul,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using e

theorem scaled_length (C s : PTm n) : Γ ⊢[PRAAx] length (scaled C s) ≐ length C := sequence_length _ _ _

theorem scaled_lookup (C s i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) :
    Γ ⊢[PRAAx] entry (scaled C s) i ≐ qmul s (entry C i) :=
  (sequence_decode scaleBody hi).eqTrans (scale_body_at C s i)

theorem scaled_entry_canonical (C s i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) :
    Γ ⊢[PRAAx] canonical (entry (scaled C s) i) :=
  GaussianRationalHorner.canonical_congr (scaled_lookup C s i hi) (GaussianRationalHorner.qmul_canonical _ _)

def prefixLaw (C s z k : PTm n) : Fm PTm n := le k (length C) ⟶
  horner (scaled C s) z k ≐ qmul s (horner C z k)

ipra_subst prefixLaw

theorem prefix_zero (C s z : PTm n) : Γ ⊢[PRAAx]
    horner (scaled C s) z zero ≐ qmul s (horner C z zero) :=
  (GaussianRationalHorner.horner_zero _ _).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalHorner.horner_zero C z)).eqTrans (qmul_zero_right s)).eqSymm

theorem prefix_step (C s z k : PTm n) (hk : Γ ⊢[PRAAx] lt k (length C))
    (h : Γ ⊢[PRAAx] horner (scaled C s) z k ≐ qmul s (horner C z k)) : Γ ⊢[PRAAx]
    horner (scaled C s) z (succ k) ≐ qmul s (horner C z (succ k)) :=
  (GaussianRationalHorner.horner_succ _ _ _).eqTrans
    ((qadd_congr (qmul_congr h (.eqRefl _)) (scaled_lookup C s k hk)).eqTrans
      ((qadd_congr (GaussianReciprocalHorner.qmul_associative s (horner C z k) z) (.eqRefl _)).eqTrans
        ((qmul_add s (qmul (horner C z k) z) (entry C k)).eqSymm.eqTrans
          (qmul_congr (.eqRefl _) (GaussianRationalHorner.horner_succ C z k).eqSymm))))

/-- The prefix bound is internal to the QF induction invariant. -/
theorem horner_linearity (C s z k : PTm n) (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx]
    horner (scaled C s) z k ≐ qmul s (horner C z k) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift s) (Syn.shift z) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_prefixLaw]
    · exact .impI (prefix_zero C s z)
    · refine .impI ?_
      let I := prefixLaw (Syn.shift C) (Syn.shift s) (Syn.shift z) (var 0)
      exact prefix_step _ _ _ _ (Prf.hyp0 (Ax := PRAAx) (Γ := I :: Γ.map Fm.shift))
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C s z k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem evaluation_linearity (C s z : PTm n) : Γ ⊢[PRAAx]
    evaluate (scaled C s) z ≐ qmul s (evaluate C z) :=
  (congrAp3 GaussianRationalHorner.hornerF (scaled_length C s) (.eqRefl _) (.eqRefl _)).eqTrans
    (horner_linearity C s z (length C) (le_refl _))

def scaledF : PR 2 := PTm.toPR (scaled (var 0) (var 1))
theorem program_at (C s : PTm n) : Γ ⊢[PRAAx] ap2 scaledF C s ≐ scaled C s := by
  simpa [scaledF,ap2] using toPR_eq (Γ := Γ) (scaled (var 0) (var 1) : PTm 2) ![C,s]

theorem rational_coefficient_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 scaledF (var 0) (var 1) ≐ scaled (var 0) (var 1)) ⋏
      length (scaled (var 0) (var 1)) ≐ length (var 0)) :=
  closeUniv 2 (.andI (program_at _ _) (scaled_length _ _))

theorem rational_horner_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (length (var 0)) ⟶
      horner (scaled (var 0) (var 1)) (var 2) (var 3) ≐ qmul (var 1) (horner (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (horner_linearity _ _ _ _ Prf.hyp0))

theorem rational_evaluation_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (scaled (var 0) (var 1)) (var 2) ≐ qmul (var 1) (evaluate (var 0) (var 2))) :=
  closeUniv 3 (evaluation_linearity _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling
