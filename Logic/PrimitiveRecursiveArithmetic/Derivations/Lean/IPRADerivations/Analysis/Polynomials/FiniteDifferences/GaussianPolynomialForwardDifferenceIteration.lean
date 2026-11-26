import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifference
import IPRADerivations.Analysis.Exponential.ExponentialSeries

/-!
# Iterated Gaussian polynomial forward differences at encoded order

The actual primitive recursion shrinks the coefficient buffer at each
step. A factorial-weighted invariant of its leading entry equates the
terminal constant with the exact scaled original leading coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceIteration

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Analysis.Products (fact)
open GaussianPolynomialForwardDifference (difference difference_length)
open GaussianRationalHorner (qmul evaluate)
open GaussianRationalNaturalScale (natScale natScale_congr natScale_multiply natScale_product)
open GaussianRationalReciprocal (power power_zero power_succ)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalTranslationStages (remaining remaining_step remaining_positive)
open GaussianTranslatedNonconstant (recode recode_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stageStep : PTm 5 := difference (var 1) (remaining (var 3) (var 0)) (var 4)
def stageF : PR 4 := recDef (var 0 : PTm 3) stageStep
def stage (C N h j : PTm n) : PTm n := PTm.app stageF ![j,C,N,h]

@[simp] theorem subst_stage {l : ℕ} (σ : Fin n → PTm l) (C N h j : PTm n) :
    Syn.subst σ (stage C N h j) = stage (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ j) := by
  simp only [stage,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem stage_zero (C N h : PTm n) : Γ ⊢[PRAAx] stage C N h zero ≐ C := by
  have raw := rec_zero (Γ := Γ) (var 0 : PTm 3) stageStep ![C,N,h]
  have e : (Fin.cases zero ![C,N,h] : Fin 4 → PTm n) = ![zero,C,N,h] := by funext i; fin_cases i <;> rfl
  rw [e] at raw
  simpa only [stage,stageF,Syn.subst_var,Matrix.cons_val_zero] using raw

theorem stage_succ (C N h j : PTm n) : Γ ⊢[PRAAx]
    stage C N h (succ j) ≐ difference (stage C N h j) (remaining N j) h := by
  have raw := rec_succ (Γ := Γ) (var 0 : PTm 3) stageStep j ![C,N,h]
  have a : (Fin.cases (succ j) ![C,N,h] : Fin 4 → PTm n) = ![succ j,C,N,h] := by funext i; fin_cases i <;> rfl
  have b : (Fin.cases j (Fin.cases (PTm.app stageF (Fin.cases j ![C,N,h])) ![C,N,h]) : Fin 5 → PTm n) =
      ![j,stage C N h j,C,N,h] := by funext i; fin_cases i <;> rfl
  unfold stageF at b
  rw [a,b] at raw
  simpa only [stage,stageF,stageStep,GaussianPolynomialForwardDifference.subst_difference,
    GaussianRationalTranslationStages.subst_remaining,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using raw

theorem stage_index_congr (C N h : PTm n) {j k : PTm n} (hk : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] stage C N h j ≐ stage C N h k := by
  apply congrApp
  intro i
  fin_cases i
  · exact hk
  · exact .eqRefl _
  · exact .eqRefl _
  · exact .eqRefl _

theorem stage_length (C N h j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] length (stage C N h j) ≐ succ (remaining N j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have eq : (j ≐ zero)::Γ ⊢[PRAAx] j ≐ zero := Prf.hyp0
    exact (congrFst (stage_index_congr C N h eq)).eqTrans ((congrFst (stage_zero C N h)).eqTrans
      (hC.wk.eqTrans (congrSucc ((congrMonus (.eqRefl _) eq).eqTrans (monus_zero N))).eqSymm))
  · have eq : (j ≐ succ (pred j))::Γ ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have active := le_congr eq (.eqRefl _) hj.wk
    exact (congrFst (stage_index_congr C N h eq)).eqTrans
      ((congrFst (stage_succ C N h (pred j))).eqTrans
        ((difference_length _ _ _).eqTrans ((remaining_step N (pred j) active).eqTrans
          (congrSucc (congrMonus (.eqRefl _) eq.eqSymm)))))

def weightedHead (C N h j : PTm n) : PTm n :=
  natScale (fact (remaining N j)) (entry (stage C N h j) zero)

def target (C N h j : PTm n) : PTm n :=
  natScale (fact N) (qmul (entry C zero) (power h j))

private theorem fact_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] fact a ≐ fact b :=
  congrAp2 factF h (.eqRefl zero)

private theorem scale_recode (s a : PTm n) : Γ ⊢[PRAAx] natScale s (recode a) ≐ natScale s a :=
  (GaussianRationalNaturalScale.natScale_as_product s (recode a)).eqTrans
    ((GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqTrans
      (GaussianRationalNaturalScale.natScale_as_product s a).eqSymm)

private theorem head_zero (C N h : PTm n) : Γ ⊢[PRAAx] weightedHead C N h zero ≐ target C N h zero := by
  let a := entry C zero
  have eq : Γ ⊢[PRAAx] qmul a (power h zero) ≐ recode a :=
    (qmul_congr (.eqRefl _) (power_zero h)).eqTrans
      ((GaussianRationalSyntheticCoefficientValues.qmul_recode_left a _).eqSymm.eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (recode_canonical a)))
  exact (natScale_congr (fact_congr (monus_zero N)) (entry_congr (stage_zero C N h) (.eqRefl _))).eqTrans
    ((scale_recode (fact N) a).eqSymm.eqTrans (natScale_congr (.eqRefl _) eq.eqSymm))

private theorem weighted_step (C N h j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    weightedHead C N h (succ j) ≐ qmul (weightedHead C N h j) h := by
  let a := entry (stage C N h j) zero
  let m := remaining N j
  let t := remaining N (succ j)
  have hs : Γ ⊢[PRAAx] fact m ≐ fact t*m :=
    (fact_congr (remaining_step N j hj)).eqTrans
      ((ExponentialSeries.fact_succ' t).eqTrans (congrMul (.eqRefl _) (remaining_step N j hj).eqSymm))
  have lead := (entry_congr (stage_succ C N h j) (.eqRefl _)).eqTrans
    (GaussianPolynomialForwardDifference.leading (stage C N h j) m h
      (stage_length C N h j hC (le_trans (le_succ_self _) hj)) (remaining_positive N j hj))
  exact (natScale_congr (.eqRefl _) lead).eqTrans
    ((natScale_multiply (fact t) m (qmul a h)).eqTrans
      ((natScale_congr hs.eqSymm (GaussianRationalPowerAlgebra.qmul_commutative a h)).eqTrans
        ((natScale_product (fact m) h a).eqSymm.eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))))

private theorem target_step (C N h j : PTm n) :
    Γ ⊢[PRAAx] target C N h (succ j) ≐ qmul (target C N h j) h := by
  let a := entry C zero
  let b := power h j
  exact (natScale_congr (.eqRefl _) (qmul_congr (.eqRefl _) (power_succ h j))).eqTrans
    ((natScale_congr (.eqRefl _) ((GaussianReciprocalHorner.qmul_associative a b h).eqSymm.eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative _ _))).eqTrans
      ((natScale_product (fact N) h (qmul a b)).eqSymm.eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

private def leadingLaw (C N h j : PTm n) : Fm PTm n :=
  le j N ⟶ weightedHead C N h j ≐ target C N h j

@[simp] private theorem subst_leadingLaw {l : ℕ} (σ : Fin n → PTm l) (C N h j : PTm n) :
    (leadingLaw C N h j).subst σ = leadingLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ j) := by
  simp [leadingLaw,weightedHead,target,fact]

theorem weighted_leading (C N h j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] weightedHead C N h j ≐ target C N h j := by
  have all : Γ ⊢[PRAAx] .all (leadingLaw (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_leadingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (head_zero C N h).wk
    · simp only [subst_leadingLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let A := le (succ (var 0)) (Syn.shift N)
      let I := leadingLaw (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0)
      let Δ := A :: I :: Γ.map Fm.shift
      have shape : Δ ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
        simpa [Δ,Fm.shift,Syn.shift] using hC.shift.wk.wk
      have next : Δ ⊢[PRAAx] A := Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] I) (le_trans (le_succ_self _) next)
      exact (weighted_step (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0) shape next).eqTrans
        ((qmul_congr ih (.eqRefl _)).eqTrans (target_step _ _ _ _).eqSymm)
  have rule : Γ ⊢[PRAAx] leadingLaw C N h j := by
    simpa only [subst_leadingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem terminal_evaluation (C N h x : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] evaluate (stage C N h N) x ≐ target C N h N := by
  let P := stage C N h N
  have len : Γ ⊢[PRAAx] length P ≐ one :=
    (stage_length C N h N hC (le_refl _)).eqTrans (congrSucc (monus_self N))
  have e : Γ ⊢[PRAAx] weightedHead C N h N ≐ recode (entry P zero) :=
    (natScale_congr ((fact_congr (monus_self N)).eqTrans ExponentialSeries.fact_zero') (.eqRefl _)).eqTrans
      (GaussianRationalNaturalScale.natScale_one _)
  exact (GaussianRationalSyntheticCoefficientValues.singleton_evaluation P x len).eqSymm.eqTrans
    (e.eqSymm.eqTrans (weighted_leading C N h N hC (le_refl _)))

theorem actual_Gaussian_iterated_polynomial_forward_difference_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      evaluate (stage (var 0) (var 1) (var 2) (var 1)) (var 3) ≐
        natScale (fact (var 1)) (qmul (entry (var 0) zero) (power (var 2) (var 1)))) :=
  closeUniv 4 (.impI (terminal_evaluation _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceIteration
