import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianOffDominantTerms
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSumAlgebra

/-!
# Actual ascending power expansion of the rational Horner evaluator

An actual sequence contains coefficient i times the actual rational power
delta^i, in ascending degree order. Guarded QF induction conserves the
remaining original Horner prefix times delta^m plus the accumulated terms.
It proves literal equality of the two normalized evaluator outputs from
the original list length alone. The degree, point, list and prefix counter
are numerical; input codes need not be canonical, and degree zero is included.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPowerExpansion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qadd qmul horner hornerF evaluate canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Analysis.GaussianOffDominantTerms (term subst_term term_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (C N delta : PTm n) : PTm n := pairT C (pairT N delta)
def termBody : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def terms (C N delta : PTm n) : PTm n := sequence termBody (succ N) (data C N delta)
def partialSum (C N delta m : PTm n) : PTm n := horner (terms C N delta) qone m
def remaining (N m : PTm n) : PTm n := monus (succ N) m
def conservationLeft (C N delta m : PTm n) : PTm n :=
  qadd (qmul (horner C delta (remaining N m)) (power delta m)) (partialSum C N delta m)
def conservationLaw (C N delta m : PTm n) : Fm PTm n :=
  le m (succ N) ⟶ conservationLeft C N delta m ≐ evaluate C delta

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (C N delta : PTm n) :
    Syn.subst σ (data C N delta) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) := by simp [data]
@[simp] theorem subst_terms {l : ℕ} (σ : Fin n → PTm l) (C N delta : PTm n) :
    Syn.subst σ (terms C N delta) = terms (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) := by simp [terms]
@[simp] theorem subst_prefix {l : ℕ} (σ : Fin n → PTm l) (C N delta m : PTm n) :
    Syn.subst σ (partialSum C N delta m) = partialSum (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) (Syn.subst σ m) := by simp [partialSum]
@[simp] theorem subst_remaining {l : ℕ} (σ : Fin n → PTm l) (N m : PTm n) :
    Syn.subst σ (remaining N m) = remaining (Syn.subst σ N) (Syn.subst σ m) := by simp [remaining]
@[simp] theorem subst_conservationLeft {l : ℕ} (σ : Fin n → PTm l) (C N delta m : PTm n) :
    Syn.subst σ (conservationLeft C N delta m) = conservationLeft (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ delta) (Syn.subst σ m) := by simp [conservationLeft]
@[simp] theorem subst_conservationLaw {l : ℕ} (σ : Fin n → PTm l) (C N delta m : PTm n) :
    (conservationLaw C N delta m).subst σ = conservationLaw (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ delta) (Syn.subst σ m) := by simp [conservationLaw]

theorem term_body_at (C N delta i : PTm n) : Γ ⊢[PRAAx]
    inst2 termBody i (data C N delta) ≐ term C N delta i := by
  simp only [termBody,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail := snd_pair (Γ := Γ) C (pairT N delta)
  exact term_congr (fst_pair _ _) ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrSnd tail).eqTrans (snd_pair _ _)) (.eqRefl _)

theorem terms_length (C N delta : PTm n) : Γ ⊢[PRAAx] length (terms C N delta) ≐ succ N := sequence_length _ _ _

theorem terms_lookup (C N delta i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (terms C N delta) i ≐ term C N delta i :=
  (sequence_decode termBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans (term_body_at C N delta i)

theorem prefix_zero (C N delta : PTm n) : Γ ⊢[PRAAx] partialSum C N delta zero ≐ GaussianRationalHorner.qzero :=
  GaussianRationalHorner.horner_zero _ _

theorem prefix_canonical (C N delta m : PTm n) : Γ ⊢[PRAAx] canonical (partialSum C N delta m) :=
  GaussianRationalHorner.horner_canonical _ _ _

theorem prefix_succ (C N delta m : PTm n) (hm : Γ ⊢[PRAAx] le m N) : Γ ⊢[PRAAx]
    partialSum C N delta (succ m) ≐ qadd (partialSum C N delta m) (term C N delta m) :=
  (GaussianRationalHorner.horner_succ _ _ _).eqTrans
    (qadd_congr (GaussianReciprocalHorner.qmul_one_right _ (prefix_canonical C N delta m))
      (terms_lookup C N delta m hm))

theorem remaining_zero (N : PTm n) : Γ ⊢[PRAAx] remaining N zero ≐ succ N := monus_zero _
theorem remaining_succ (N m : PTm n) : Γ ⊢[PRAAx] remaining N (succ m) ≐ monus N m := succ_monus_succ _ _

theorem remaining_before (N m : PTm n) (hm : Γ ⊢[PRAAx] le m N) : Γ ⊢[PRAAx]
    remaining N m ≐ succ (monus N m) := by
  have e : Γ ⊢[PRAAx] succ N ≐ succ (monus N m)+m :=
    (congrSucc (eq_add_of_le hm)).eqTrans (by ipra_ring)
  exact (congrMonus e (.eqRefl m)).eqTrans (add_monus _ _)

theorem conservation_zero (C N delta : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    conservationLeft C N delta zero ≐ evaluate C delta := by
  have h : Γ ⊢[PRAAx] horner C delta (remaining N zero) ≐ evaluate C delta :=
    congrAp3 hornerF ((remaining_zero N).eqTrans hLen.eqSymm) (.eqRefl _) (.eqRefl _)
  have product := (qmul_congr h (GaussianRationalReciprocal.power_zero delta)).eqTrans
    (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _))
  exact (qadd_congr product (prefix_zero C N delta)).eqTrans
    (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.horner_canonical _ _ _))

/-- The actual Horner step and actual power step exchange one original
coefficient with the next ascending term. No power expansion is a premise. -/
theorem conservation_step (C N delta m : PTm n) (hm : Γ ⊢[PRAAx] le m N)
    (hIH : Γ ⊢[PRAAx] conservationLeft C N delta m ≐ evaluate C delta) : Γ ⊢[PRAAx]
    conservationLeft C N delta (succ m) ≐ evaluate C delta := by
  have oldH : Γ ⊢[PRAAx] horner C delta (remaining N m) ≐
      qadd (qmul (horner C delta (monus N m)) delta) (GaussianBalancedRadiusSyntax.coefficient C N m) :=
    (congrAp3 hornerF (remaining_before N m hm) (.eqRefl _) (.eqRefl _)).eqTrans
      (GaussianRationalHorner.horner_succ C delta (monus N m))
  have oldExchange := (qadd_congr (qmul_congr oldH (.eqRefl _)) (.eqRefl _)).eqTrans
    (GaussianRationalSumAlgebra.horner_sum_exchange (horner C delta (monus N m)) delta
      (GaussianBalancedRadiusSyntax.coefficient C N m) (power delta m) (partialSum C N delta m))
  have newExchange : Γ ⊢[PRAAx] conservationLeft C N delta (succ m) ≐
      qadd (qmul (horner C delta (monus N m)) (qmul (power delta m) delta))
        (qadd (partialSum C N delta m) (term C N delta m)) :=
    qadd_congr (qmul_congr (congrAp3 hornerF (remaining_succ N m) (.eqRefl _) (.eqRefl _))
      (GaussianRationalReciprocal.power_succ delta m)) (prefix_succ C N delta m hm)
  exact newExchange.eqTrans (oldExchange.eqSymm.eqTrans hIH)

/-- Genuine guarded QF induction; the original list shape is used at the
base, and each successor reads the actual original coefficient and power. -/
theorem conservation (C N delta m : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] le m (succ N)) : Γ ⊢[PRAAx]
    conservationLeft C N delta m ≐ evaluate C delta := by
  have all : Γ ⊢[PRAAx] .all (conservationLaw (Syn.shift C) (Syn.shift N) (Syn.shift delta) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_conservationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (conservation_zero C N delta hLen).wk
    · simp only [subst_conservationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := conservationLaw (Syn.shift C) (Syn.shift N) (Syn.shift delta) (var 0)
      let Δ := le (succ (var 0)) (succ (Syn.shift N))::I::Γ.map Fm.shift
      have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact conservation_step _ _ _ _ bound
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] conservationLaw C N delta m := by
    simpa only [subst_conservationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m
  exact .impE rule hm

/-- Actual ascending power expansion at every internal degree, including
degree zero and arbitrary raw coefficient/point codes. -/
theorem power_expansion (C N delta : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate C delta ≐ evaluate (terms C N delta) qone := by
  have full := conservation C N delta (succ N) hLen (le_refl _)
  have first : Γ ⊢[PRAAx] qmul (horner C delta (remaining N (succ N))) (power delta (succ N)) ≐ GaussianRationalHorner.qzero :=
    (qmul_congr ((congrAp3 hornerF (monus_self (succ N)) (.eqRefl _) (.eqRefl _)).eqTrans
      (GaussianRationalHorner.horner_zero C delta)) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_left _)
  have final : Γ ⊢[PRAAx] conservationLeft C N delta (succ N) ≐ partialSum C N delta (succ N) :=
    (qadd_congr first (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qzero_add _ (prefix_canonical _ _ _ _))
  exact full.eqSymm.eqTrans (final.eqTrans (congrAp3 hornerF (terms_length C N delta).eqSymm (.eqRefl _) (.eqRefl _)))

/-! Actual PR3 output carries the generated ascending list and both
literal evaluator outputs. Its numerical fields are derived by decoding. -/
def output (C N delta : PTm n) : PTm n := pairT (terms C N delta)
  (pairT (evaluate C delta) (evaluate (terms C N delta) qone))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N delta : PTm n) : PTm n := ap3 outputF C N delta

@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N delta : PTm n) :
    Syn.subst σ (output C N delta) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N delta : PTm n) :
    Syn.subst σ (run C N delta) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) := by simp [run]

theorem program_at (C N delta : PTm n) : Γ ⊢[PRAAx] run C N delta ≐ output C N delta := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,delta]

theorem returned_terms (C N delta : PTm n) : Γ ⊢[PRAAx] fstT (run C N delta) ≐ terms C N delta :=
  (congrFst (program_at C N delta)).eqTrans (fst_pair _ _)
theorem returned_original (C N delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N delta)) ≐ evaluate C delta :=
  (congrFst ((congrSnd (program_at C N delta)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_expansion (C N delta : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run C N delta)) ≐ evaluate (terms C N delta) qone :=
  (congrSnd ((congrSnd (program_at C N delta)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_equal (C N delta : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    fstT (sndT (run C N delta)) ≐ sndT (sndT (run C N delta)) :=
  (returned_original C N delta).eqTrans ((power_expansion C N delta hLen).eqTrans (returned_expansion C N delta).eqSymm)

theorem actual_power_terms_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (terms (var 0) (var 1) (var 2)) ≐ succ (var 1)) := closeUniv 3 (terms_length _ _ _)

theorem actual_power_term_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ entry (terms (var 0) (var 1) (var 2)) (var 3) ≐ term (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (terms_lookup _ _ _ _ Prf.hyp0))

theorem actual_horner_conservation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (succ (var 1)) ⟶
      conservationLeft (var 0) (var 1) (var 2) (var 3) ≐ evaluate (var 0) (var 2)) :=
  closeUniv 4 (.impI (.impI (conservation _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_horner_power_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶
      evaluate (var 0) (var 2) ≐ evaluate (terms (var 0) (var 1) (var 2)) qone) :=
  closeUniv 3 (.impI (power_expansion _ _ _ Prf.hyp0))

theorem actual_power_expansion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2) ⋏
      (fstT (run (var 0) (var 1) (var 2)) ≐ terms (var 0) (var 1) (var 2) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2))) ≐ evaluate (var 0) (var 2) ⋏
          sndT (sndT (run (var 0) (var 1) (var 2))) ≐ evaluate (terms (var 0) (var 1) (var 2)) qone))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_terms _ _ _)
    (.andI (returned_original _ _ _) (returned_expansion _ _ _))))

theorem returned_power_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2))) ≐ sndT (sndT (run (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (returned_equal _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalPowerExpansion
