import IPRADerivations.Analysis.RationalArithmetic.Spans.RationalMaximalMinors

/-!
# The actual least free column of a proper maximum minor

A bounded complementary filter examines the original column-mask digits.
Its count plus the selected count equals the original column dimension.
At proper rank the first retained complementary index is the actual
least column outside the selected minor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMinorFreeColumn

open_ipra
open RationalSubtupleSpan (bit bitBody bit_body_at)
open RationalSelectedMinors (count subst_count)
open RationalMaximalMinors (bestColumn rank best_valid)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (sel sel_spec rank_succ rank_zero rank_lt_of_kept)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def complementBody : PTm 2 := monus one (bit (var 1) (var 0))
def missingCount (d C : PTm n) : PTm n := Foundations.FilteredEnumeration.rank complementBody d C
def firstMissing (d C : PTm n) : PTm n := sel complementBody zero d C
def free (P d : PTm n) : PTm n := firstMissing d (bestColumn P d)

ipra_subst missingCount [Foundations.FilteredEnumeration.rank]
ipra_subst firstMissing
ipra_subst free

theorem complement_at (i C : PTm n) : inst2 complementBody i C = monus one (bit C i) := by
  simp [complementBody,inst2,one]

theorem bit_cases (i C : PTm n) : Γ ⊢[PRAAx] (bit C i ≐ zero) ⋎ (bit C i ≐ one) := by
  have h : Γ ⊢[PRAAx] lt (bit C i) two :=
    AnalyticNumberTheory.Multiplicative.rem_lt' (pos_of_eq_succ (.eqRefl two)) (quo C (pw two i))
  refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans h)) ?_ (.orI₂ Prf.hyp0)
  exact .orI₁ (le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) (zero_le _))

private alias signum_congr := Common.congrSg

theorem complementary_indicator (i C : PTm n) : Γ ⊢[PRAAx]
    Signum.sg (inst2 bitBody i C) + Signum.sg (inst2 complementBody i C) ≐ one := by
  rw [bit_body_at,complement_at]
  refine .orE (bit_cases i C) ?_ ?_
  · exact (congrAdd ((signum_congr Prf.hyp0).eqTrans Signum.sg_zero)
      ((signum_congr ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_zero one))).eqTrans (Signum.sg_succ zero))).eqTrans
      (zero_add one)
  · exact (congrAdd ((signum_congr Prf.hyp0).eqTrans (Signum.sg_succ zero))
      ((signum_congr ((congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_self one))).eqTrans Signum.sg_zero)).eqTrans
      (add_zero one)

theorem complementary_count (d C : PTm n) : Γ ⊢[PRAAx] count d C + missingCount d C ≐ d := by
  have all : Γ ⊢[PRAAx] .all (count (var 0) (Syn.shift C) + missingCount (var 0) (Syn.shift C) ≐ var 0) := by
    ipra_qfind [subst_count, subst_missingCount]
    · exact (congrAdd (rank_zero bitBody C) (rank_zero complementBody C)).eqTrans (zero_add zero)
    · let i : PTm (n+1) := var 0
      let c := Syn.shift C
      let Δ := (count i c + missingCount i c ≐ i) :: Γ.map Fm.shift
      have fold : Δ ⊢[PRAAx] count (succ i) c + missingCount (succ i) c ≐
          (count i c + missingCount i c) + (Signum.sg (inst2 bitBody i c) + Signum.sg (inst2 complementBody i c)) :=
        (congrAdd (rank_succ bitBody i c) (rank_succ complementBody i c)).eqTrans (by
          unfold count missingCount Foundations.FilteredEnumerationCode.count
          ipra_ring)
      exact fold.eqTrans ((congrAdd Prf.hyp0 (complementary_indicator i c)).eqTrans (succ_eq_add_one _).eqSymm)
  simpa only [Fm.subst_eq,PTm.subst_add,subst_count,subst_missingCount,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE d

theorem kept_in_complement (i C : PTm n) (h : Γ ⊢[PRAAx] bit C i ≐ zero) :
    Γ ⊢[PRAAx] neg (inst2 complementBody i C ≐ zero) := by
  rw [complement_at]
  exact .impI (succ_ne_zero (((congrMonus (.eqRefl one) h.wk).eqTrans (monus_zero one)).eqSymm.eqTrans Prf.hyp0))

theorem complement_is_missing (i C : PTm n) (h : Γ ⊢[PRAAx] neg (inst2 complementBody i C ≐ zero)) :
    Γ ⊢[PRAAx] bit C i ≐ zero := by
  refine .orE (bit_cases i C) Prf.hyp0 ?_
  exact .botE _ (.impE h.wk (by rw [complement_at]; exact (congrMonus (.eqRefl one) Prf.hyp0).eqTrans (monus_self one)))

theorem first_missing_spec (d C : PTm n) (h : Γ ⊢[PRAAx] lt (count d C) d) :
    Γ ⊢[PRAAx] lt (firstMissing d C) d ⋏
      (bit C (firstMissing d C) ≐ zero ⋏ missingCount (firstMissing d C) C ≐ zero) := by
  have first := le_congr (succ_eq_add_one _) (complementary_count d C).eqSymm h
  have positive : Γ ⊢[PRAAx] lt zero (missingCount d C) :=
    le_of_add_le_add_right (le_congr (add_comm _ _) (add_comm _ _) first)
  have spec := sel_spec complementBody (r := zero) (P := d) (p := C) positive
  exact .andI (.andE₁ spec) (.andI (complement_is_missing _ _ (.andE₁ (.andE₂ spec))) (.andE₂ (.andE₂ spec)))

theorem earlier_selected (d C i : PTm n) (h : Γ ⊢[PRAAx] lt (count d C) d)
    (hi : Γ ⊢[PRAAx] lt i (firstMissing d C)) : Γ ⊢[PRAAx] bit C i ≐ one := by
  have spec := first_missing_spec d C h
  refine .orE (bit_cases i C) ?_ Prf.hyp0
  have earlier := rank_lt_of_kept complementBody (kept_in_complement i C Prf.hyp0) hi.wk
  exact lt_zero_absurd _ (lt_congr (.eqRefl _) (Prf.andE₂ (.andE₂ spec)).wk earlier)

theorem free_column_spec (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) :
    Γ ⊢[PRAAx] lt (free P d) d ⋏ bit (bestColumn P d) (free P d) ≐ zero := by
  have countProper := lt_congr (Prf.andE₁ (best_valid P d)) (.eqRefl _) h
  have spec := first_missing_spec d (bestColumn P d) countProper
  exact .andI (.andE₁ spec) (.andE₁ (.andE₂ spec))

theorem free_least (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (free P d)) :
    Γ ⊢[PRAAx] bit (bestColumn P d) i ≐ one :=
  earlier_selected d (bestColumn P d) i (lt_congr (Prf.andE₁ (best_valid P d)) (.eqRefl _) h) hi

theorem actual_complementary_column_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (count (var 0) (var 1) + missingCount (var 0) (var 1) ≐ var 0) :=
  closeUniv 2 (complementary_count _ _)

theorem actual_maximum_minor_free_column_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (free (var 0) (var 1)) (var 1) ⋏
      bit (bestColumn (var 0) (var 1)) (free (var 0) (var 1)) ≐ zero) :=
  closeUniv 2 (.impI (free_column_spec (var 0) (var 1) Prf.hyp0))

theorem actual_maximum_minor_free_column_least_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (free (var 0) (var 1)) ⟶
      bit (bestColumn (var 0) (var 1)) (var 2) ≐ one) :=
  closeUniv 3 (.impI (.impI (free_least (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalMinorFreeColumn
