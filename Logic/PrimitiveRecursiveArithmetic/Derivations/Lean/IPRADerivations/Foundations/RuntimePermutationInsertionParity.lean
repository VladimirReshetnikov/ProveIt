import IPRADerivations.Foundations.RuntimePermutationInsertion
import IPRADerivations.Foundations.BoundedSyntaxBackwardInduction
import IPRADerivations.Core.LinearCombination

/-!
# Exact inversion counts for the actual maximum-label insertion

The original insertedWord program is retained. Appending the maximum has
no new inversions; moving it one position left adds exactly one. Genuine
bounded backward induction gives the exact numerical count and parity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RuntimePermutationInsertionParity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RuntimePermutationWords (digit inversionBit inversions parity rowPrefix inversionPrefix horizon)
open RuntimePermutationInsertion (insertedWord inserted_digit recovered_skip recovered_at recovered_off compressed)
open RuntimePermutationDeletion (slot slot_before slot_after slot_bound recovered)
open RuntimeAdjacentPermutationSwap (digit_congr different_of_lt different_symm inversion_congr)
open Syn
open BoundedSyntax
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem inserted_skip_digit (m p d i : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    digit (succ m) (insertedWord m p d) (slot p i) ≐ digit m d i :=
  (inserted_digit m p d (slot p i) hp (slot_bound m p i hi)).eqTrans (recovered_skip m p d i)

theorem appended_digit (m d i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    digit (succ m) (insertedWord m m d) i ≐ digit m d i :=
  (digit_congr (.eqRefl _) (.eqRefl _) (slot_before m i hi).eqSymm).eqTrans (inserted_skip_digit m m d i (le_refl _) hi)
theorem appended_maximum (m d : PTm n) : Γ ⊢[PRAAx] digit (succ m) (insertedWord m m d) m ≐ m :=
  (inserted_digit m m d m (le_refl _) (le_refl _)).eqTrans (recovered_at m m d m (.eqRefl _))

/-- Inversion bits transport through actual digit equations even when the
numerical bases differ. No permutation or code-horizon law is needed. -/
theorem inversion_digits (m q w v i j : PTm n)
    (hi : Γ ⊢[PRAAx] digit m w i ≐ digit q v i) (hj : Γ ⊢[PRAAx] digit m w j ≐ digit q v j) : Γ ⊢[PRAAx]
    inversionBit m w i j ≐ inversionBit q v i j := by
  apply RuntimeAdjacentPermutationSwap.bits_equal _ _ (RuntimePermutationWords.inversion_cases _ _ _ _) (RuntimePermutationWords.inversion_cases _ _ _ _)
  refine .iffI (.impI ?_) (.impI ?_)
  · have h : (inversionBit m w i j ≐ one) :: Γ ⊢[PRAAx] lt i j ⋏ lt (digit m w j) (digit m w i) :=
      (RuntimePermutationWords.inversion_reflection (Γ := Γ) m w i j).wk.iffMp Prf.hyp0
    exact (RuntimePermutationWords.inversion_reflection q v i j).wk.iffMpr
      (.andI (.andE₁ h) (lt_congr hj.wk hi.wk (.andE₂ h)))
  · have h : (inversionBit q v i j ≐ one) :: Γ ⊢[PRAAx] lt i j ⋏ lt (digit q v j) (digit q v i) :=
      (RuntimePermutationWords.inversion_reflection (Γ := Γ) q v i j).wk.iffMp Prf.hyp0
    exact (RuntimePermutationWords.inversion_reflection m w i j).wk.iffMpr
      (.andI (.andE₁ h) (lt_congr hj.wk.eqSymm hi.wk.eqSymm (.andE₂ h)))

theorem appended_inversion (m d i j : PTm n) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    inversionBit (succ m) (insertedWord m m d) i j ≐ inversionBit m d i j :=
  inversion_digits _ _ _ _ _ _ (appended_digit m d i hi) (appended_digit m d j hj)

theorem appended_last_column (m d i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    inversionBit (succ m) (insertedWord m m d) i m ≐ zero := by
  refine .orE (RuntimePermutationWords.inversion_cases _ _ _ _) Prf.hyp0 ?_
  have h : (inversionBit (succ m) (insertedWord m m d) i m ≐ one) :: Γ ⊢[PRAAx]
      lt i m ⋏ lt (digit (succ m) (insertedWord m m d) m) (digit (succ m) (insertedWord m m d) i) :=
    (RuntimePermutationWords.inversion_reflection (Γ := Γ) (succ m) (insertedWord m m d) i m).wk.iffMp Prf.hyp0
  have bad : (inversionBit (succ m) (insertedWord m m d) i m ≐ one) :: Γ ⊢[PRAAx] lt m (digit m d i) :=
    lt_congr (appended_maximum m d) (appended_digit m d i hi.wk) (.andE₂ h)
  exact le_lt_absurd _ (le_of_lt (RuntimePermutationWords.digit_bound m d i hi.wk)) bad

theorem appended_last_row_bit (m d j : PTm n) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx]
    inversionBit (succ m) (insertedWord m m d) m j ≐ zero :=
  RuntimeAdjacentPermutationSwap.inversion_zero_position _ _ _ _ ((succ_monus_succ j m).eqSymm.eqTrans hj)

theorem appended_row (m d i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    rowPrefix (succ m) (insertedWord m m d) i (succ m) ≐ rowPrefix m d i m := by
  have sumBridge : Γ ⊢[PRAAx] rowPrefix (succ m) (insertedWord m m d) i m ≐ rowPrefix m d i m := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have hi' : Δ ⊢[PRAAx] lt (Syn.shift i) (Syn.shift m) := by simpa only [Δ,Fm.shift,subst_lt,Syn.shift] using hi.shift.wk
    have out : Δ ⊢[PRAAx]
        inst2 RuntimePermutationWords.inversionColumn (var 0) (pairT (Syn.shift i)
          (RuntimePermutationWords.data (succ (Syn.shift m)) (insertedWord (Syn.shift m) (Syn.shift m) (Syn.shift d)))) ≐
        inst2 RuntimePermutationWords.inversionColumn (var 0) (pairT (Syn.shift i) (RuntimePermutationWords.data (Syn.shift m) (Syn.shift d))) :=
      (RuntimePermutationWords.inversion_column_at _ _ _ _).eqTrans
        ((appended_inversion _ _ _ _ hi' Prf.hyp0).eqTrans (RuntimePermutationWords.inversion_column_at _ _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,subst_pairT,RuntimePermutationWords.subst_data,RuntimePermutationInsertion.subst_insertedWord,ConciseIPRA.PTm.subst_succ] using out
  exact (RuntimePermutationWords.row_succ _ _ _ _).eqTrans
    ((congrAdd sumBridge (appended_last_column m d i hi)).eqTrans (add_zero _))

theorem appended_last_row (m d : PTm n) : Γ ⊢[PRAAx] rowPrefix (succ m) (insertedWord m m d) m (succ m) ≐ zero := by
  apply sum_zero_of_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift
  have out : Δ ⊢[PRAAx] inst2 RuntimePermutationWords.inversionColumn (var 0)
      (pairT (Syn.shift m) (RuntimePermutationWords.data (succ (Syn.shift m)) (insertedWord (Syn.shift m) (Syn.shift m) (Syn.shift d)))) ≐ zero :=
    (RuntimePermutationWords.inversion_column_at _ _ _ _).eqTrans (appended_last_row_bit _ _ _ Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_pairT,RuntimePermutationWords.subst_data,RuntimePermutationInsertion.subst_insertedWord,ConciseIPRA.PTm.subst_succ] using out

/-- The terminal insertion is proved from the two genuine original finite sums. -/
theorem appended_inversions (m d : PTm n) : Γ ⊢[PRAAx] inversions (succ m) (insertedWord m m d) ≐ inversions m d := by
  have sumBridge : Γ ⊢[PRAAx] inversionPrefix (succ m) (insertedWord m m d) m ≐ inversionPrefix m d m := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have out : Δ ⊢[PRAAx]
        inst2 RuntimePermutationWords.inversionRow (var 0) (RuntimePermutationWords.data (succ (Syn.shift m))
          (insertedWord (Syn.shift m) (Syn.shift m) (Syn.shift d))) ≐
        inst2 RuntimePermutationWords.inversionRow (var 0) (RuntimePermutationWords.data (Syn.shift m) (Syn.shift d)) :=
      (RuntimePermutationWords.inversion_row_at _ _ _).eqTrans
        ((appended_row _ _ _ Prf.hyp0).eqTrans (RuntimePermutationWords.inversion_row_at _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,RuntimePermutationWords.subst_data,RuntimePermutationInsertion.subst_insertedWord,ConciseIPRA.PTm.subst_succ] using out
  exact (RuntimePermutationWords.inversion_prefix_succ _ _ _).eqTrans
    ((congrAdd sumBridge (appended_last_row m d)).eqTrans (add_zero _))

theorem inserted_here (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    digit (succ m) (insertedWord m p d) p ≐ m :=
  (inserted_digit m p d p hp hp).eqTrans (recovered_at m p d p (.eqRefl _))
theorem inserted_before (m p d i : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hi : Γ ⊢[PRAAx] lt i p) : Γ ⊢[PRAAx]
    digit (succ m) (insertedWord m p d) i ≐ digit m d i :=
  (digit_congr (.eqRefl _) (.eqRefl _) (slot_before p i hi).eqSymm).eqTrans
    (inserted_skip_digit m p d i hp (lt_of_lt_of_le hi ((succ_monus_succ p m).eqSymm.eqTrans hp)))
theorem inserted_after (m p d i : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hi : Γ ⊢[PRAAx] le p i)
    (him : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] digit (succ m) (insertedWord m p d) (succ i) ≐ digit m d i :=
  (digit_congr (.eqRefl _) (.eqRefl _) (slot_after p i hi).eqSymm).eqTrans (inserted_skip_digit m p d i hp him)

theorem compressed_move (p k : PTm n) (hne : Γ ⊢[PRAAx] neg (k ≐ p)) : Γ ⊢[PRAAx]
    compressed p k ≐ compressed (succ p) k := by
  refine .orE (lt_or_le k p) ?_ ?_
  · have below : lt k p :: Γ ⊢[PRAAx] lt k (succ p) := lt_of_lt_of_le Prf.hyp0 (le_succ_self _)
    exact (GuardedTotalization.sel_one (AnalyticNumberTheory.Totatives.sg_lt Prf.hyp0)).eqTrans
      (GuardedTotalization.sel_one (AnalyticNumberTheory.Totatives.sg_lt below)).eqSymm
  · have above : le p k :: Γ ⊢[PRAAx] le (succ p) k := by
      refine .orE (lt_or_eq_of_le Prf.hyp0) Prf.hyp0 ?_
      exact .botE _ (.impE hne.wk.wk Prf.hyp0.eqSymm)
    exact (GuardedTotalization.sel_zero (AnalyticNumberTheory.Totatives.sg_le Prf.hyp0)).eqTrans
      (GuardedTotalization.sel_zero (AnalyticNumberTheory.Totatives.sg_le above)).eqSymm

theorem moving_digit (m p d k : PTm n) (hp : Γ ⊢[PRAAx] lt p m) (hk : Γ ⊢[PRAAx] lt k (succ m)) : Γ ⊢[PRAAx]
    digit (succ m) (RuntimeAdjacentPermutationSwap.swapWord (succ m) (insertedWord m p d) p) k ≐
      digit (succ m) (insertedWord m (succ p) d) k := by
  have oldP : Γ ⊢[PRAAx] lt p (succ m) := lt_of_lt_of_le hp (le_succ_self m)
  have nextP : Γ ⊢[PRAAx] lt (succ p) (succ m) := (succ_monus_succ (succ p) m).eqTrans hp
  have vals := RuntimeAdjacentPermutationSwap.new_pair_values (Γ := Γ) (succ m) (insertedWord m p d) p nextP
  refine .orE (eq_or_ne k p) ?_ ?_
  · exact (digit_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      ((Prf.andE₁ vals).wk.eqTrans ((inserted_after m p d p oldP.wk (le_refl _) hp.wk).eqTrans
        ((inserted_before m (succ p) d p nextP.wk (le_refl _)).eqSymm.eqTrans
          (digit_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))))
  · refine .orE (eq_or_ne k (succ p)) ?_ ?_
    · exact (digit_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
        ((Prf.andE₂ vals).wk.wk.eqTrans ((inserted_here m p d oldP.wk.wk).eqTrans
          ((inserted_here m (succ p) d nextP.wk.wk).eqSymm.eqTrans
            (digit_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))))
    · exact (RuntimeAdjacentPermutationSwap.swapped_digit (succ m) (insertedWord m p d) p k nextP.wk.wk hk.wk.wk).eqTrans
        ((digit_congr (.eqRefl _) (.eqRefl _) (RuntimeAdjacentPermutationSwap.tau_other p k Prf.hyp1 Prf.hyp0)).eqTrans
          ((inserted_digit m p d k oldP.wk.wk hk.wk.wk).eqTrans
            ((recovered_off m p d k Prf.hyp1).eqTrans
              ((digit_congr (.eqRefl _) (.eqRefl _) (compressed_move p k Prf.hyp1)).eqTrans
                ((recovered_off m (succ p) d k Prf.hyp0).eqSymm.eqTrans
                  (inserted_digit m (succ p) d k nextP.wk.wk hk.wk.wk).eqSymm)))))

/-- This is equality of the actual bounded encoded words, not just of an
external permutation interpretation. The original codec guards are derived. -/
theorem moving_word (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p m) : Γ ⊢[PRAAx]
    RuntimeAdjacentPermutationSwap.swapWord (succ m) (insertedWord m p d) p ≐ insertedWord m (succ p) d := by
  have nextP : Γ ⊢[PRAAx] lt (succ p) (succ m) := (succ_monus_succ (succ p) m).eqTrans hp
  apply RuntimePermutationWords.word_unique (succ m) _ _ (RuntimeAdjacentPermutationSwap.swapped_bound _ _ _ nextP)
    (RuntimePermutationInsertion.inserted_word_bound _ _ _ nextP)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift
  have ps : Δ ⊢[PRAAx] lt (Syn.shift p) (Syn.shift m) := by simpa only [Δ,Fm.shift,subst_lt,Syn.shift] using hp.shift.wk
  have out := (RuntimePermutationWords.word_lookup (Γ := Δ) _ _ _ Prf.hyp0).eqTrans
    ((moving_digit (Syn.shift m) (Syn.shift p) (Syn.shift d) (var 0) ps Prf.hyp0).eqTrans
      (RuntimePermutationWords.word_lookup _ _ _ Prf.hyp0).eqSymm)
  simpa only [Δ,Syn.shift,RuntimePermutationWords.subst_word,RuntimeAdjacentPermutationSwap.subst_swapWord,
    RuntimePermutationInsertion.subst_insertedWord,ConciseIPRA.PTm.subst_succ] using out

theorem moving_inversions (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p m) : Γ ⊢[PRAAx]
    inversions (succ m) (insertedWord m p d) ≐ inversions (succ m) (insertedWord m (succ p) d)+one := by
  have oldP : Γ ⊢[PRAAx] lt p (succ m) := lt_of_lt_of_le hp (le_succ_self m)
  have nextP : Γ ⊢[PRAAx] lt (succ p) (succ m) := (succ_monus_succ (succ p) m).eqTrans hp
  have down : Γ ⊢[PRAAx] lt (digit (succ m) (insertedWord m p d) (succ p)) (digit (succ m) (insertedWord m p d) p) :=
    lt_congr (inserted_after m p d p oldP (le_refl _) hp).eqSymm (inserted_here m p d oldP).eqSymm (RuntimePermutationWords.digit_bound m d p hp)
  have oldOne := RuntimeAdjacentPermutationSwap.old_pair_one (Γ := Γ) _ _ _ down
  have newZero : Γ ⊢[PRAAx] inversionBit (succ m) (RuntimeAdjacentPermutationSwap.swapWord (succ m) (insertedWord m p d) p) p (succ p) ≐ zero := by
    refine .orE (RuntimePermutationWords.inversion_cases _ _ _ _) Prf.hyp0 ?_
    have up := RuntimeAdjacentPermutationSwap.new_pair_lt (succ m) (insertedWord m p d) p nextP.wk Prf.hyp0
    exact le_lt_absurd _ (le_of_lt down.wk) up
  have balance := RuntimeAdjacentPermutationSwap.inversion_balance (Γ := Γ) (succ m) (insertedWord m p d) p nextP
  have count := RuntimeWordSorting.inversions_congr (Γ := Γ) (.eqRefl (succ m)) (moving_word m p d hp)
  exact ((congrAdd count oldOne).eqSymm.eqTrans
    (balance.eqTrans ((congrAdd (.eqRefl _) newZero).eqTrans (add_zero _)))).eqSymm

def countBalance (m p d : PTm n) : Fm PTm n := inversions (succ m) (insertedWord m p d)+p ≐ inversions m d+m
def countSyntax (m p d : PTm n) : BFm n := .eq (inversions (succ m) (insertedWord m p d)+p) (inversions m d+m)
@[simp] theorem subst_countBalance {j : ℕ} (σ : Fin n → PTm j) (m p d : PTm n) :
    (countBalance m p d).subst σ = countBalance (Syn.subst σ m) (Syn.subst σ p) (Syn.subst σ d) := by simp [countBalance]
theorem count_formula (m p d : PTm n) : BoundedSyntax.formula (countSyntax m p d) = countBalance m p d := rfl

theorem balance_backward (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p m) (hn : Γ ⊢[PRAAx] countBalance m (succ p) d) :
    Γ ⊢[PRAAx] countBalance m p d := by
  ipra_lc natEq (moving_inversions m p d hp)+natEq hn

/-- The only new induction is the existing Boolean-compiled bounded
backward induction, with its terminal and local premises discharged here. -/
theorem all_count_balances (m p d : PTm n) (hp : Γ ⊢[PRAAx] le p m) : Γ ⊢[PRAAx] countBalance m p d := by
  let S := countSyntax (Syn.shift m) (var 0) (Syn.shift d)
  have terminal : Γ ⊢[PRAAx] (BoundedSyntax.formula S).subst (Syn.inst m) := by
    have base : Γ ⊢[PRAAx] countBalance m m d := congrAdd (appended_inversions (Γ := Γ) m d) (.eqRefl m)
    simpa only [S,count_formula,subst_countBalance,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using base
  have step : Γ ⊢[PRAAx] BoundedSyntaxBackwardInduction.localStep S m := by
    simp only [BoundedSyntaxBackwardInduction.localStep,S,count_formula,subst_countBalance,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
    exact .allI (.impI (.impI (balance_backward _ _ _ Prf.hyp1 Prf.hyp0)))
  simpa only [S,count_formula,subst_countBalance,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    BoundedSyntaxBackwardInduction.backward_induction_at S m p terminal step hp

/-- Exact insertion contribution. It is valid even for repeated smaller
digits: all decoded smaller labels are strictly below the inserted maximum. -/
theorem inserted_inversions (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    inversions (succ m) (insertedWord m p d) ≐ inversions m d+monus m p := by
  have pm : Γ ⊢[PRAAx] le p m := (succ_monus_succ p m).eqSymm.eqTrans hp
  ipra_lc natEq (all_count_balances m p d pm)+natEq (eq_add_of_le pm)

theorem inserted_parity (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    parity (succ m) (insertedWord m p d) ≐ par (inversions m d+monus m p) := congrAp1 parF (inserted_inversions m p d hp)
theorem inserted_parity_add (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    parity (succ m) (insertedWord m p d) ≐ par (parity m d+par (monus m p)) :=
  (inserted_parity m p d hp).eqTrans (par_add _ _)

/-- The literal last-row cofactor exponent m+p has the same parity. -/
theorem inserted_parity_plus (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    parity (succ m) (insertedWord m p d) ≐ par (inversions m d+(m+p)) := by
  have pm : Γ ⊢[PRAAx] le p m := (succ_monus_succ p m).eqSymm.eqTrans hp
  have exponent : Γ ⊢[PRAAx] inversions m d+(m+p) ≐ (inversions m d+monus m p)+two*p := by
    ipra_lc natEq (eq_add_of_le pm)
  exact (inserted_parity m p d hp).eqTrans ((congrAp1 parF exponent).eqTrans (par_add_two _ _)).eqSymm

theorem inserted_parity_plus_add (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    parity (succ m) (insertedWord m p d) ≐ par (parity m d+par (m+p)) :=
  (inserted_parity_plus m p d hp).eqTrans (par_add _ _)

/-- The actual numerical insertion, inversion count and parity are returned
by one fixed PR3 program. The position and word are original runtime data. -/
def output (m p d : PTm n) : PTm n := pairT (insertedWord m p d)
  (pairT (inversions (succ m) (insertedWord m p d)) (parity (succ m) (insertedWord m p d)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (m p d : PTm n) : PTm n := ap3 outputF m p d

@[simp] theorem subst_output {j : ℕ} (σ : Fin n → PTm j) (m p d : PTm n) :
    Syn.subst σ (output m p d) = output (Syn.subst σ m) (Syn.subst σ p) (Syn.subst σ d) := by simp [output]

theorem program_at (m p d : PTm n) : Γ ⊢[PRAAx] run m p d ≐ output m p d := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![m,p,d]

theorem returned_word (m p d : PTm n) : Γ ⊢[PRAAx] fstT (run m p d) ≐ insertedWord m p d :=
  (congrFst (program_at m p d)).eqTrans (fst_pair _ _)
theorem returned_counts (m p d : PTm n) : Γ ⊢[PRAAx] sndT (run m p d) ≐
    pairT (inversions (succ m) (insertedWord m p d)) (parity (succ m) (insertedWord m p d)) :=
  (congrSnd (program_at m p d)).eqTrans (snd_pair _ _)
theorem returned_inversions (m p d : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run m p d)) ≐
    inversions (succ m) (insertedWord m p d) :=
  (congrFst (returned_counts m p d)).eqTrans (fst_pair _ _)
theorem returned_parity (m p d : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run m p d)) ≐
    parity (succ m) (insertedWord m p d) :=
  (congrSnd (returned_counts m p d)).eqTrans (snd_pair _ _)
theorem returned_count_exact (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    fstT (sndT (run m p d)) ≐ inversions m d+monus m p :=
  (returned_inversions m p d).eqTrans (inserted_inversions m p d hp)
theorem returned_parity_cofactor (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    sndT (sndT (run m p d)) ≐ par (parity m d+par (m+p)) :=
  (returned_parity m p d).eqTrans (inserted_parity_plus_add m p d hp)

theorem actual_appended_inversions_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (inversions (succ (var 0)) (insertedWord (var 0) (var 0) (var 1)) ≐ inversions (var 0) (var 1)) :=
  closeUniv 2 (appended_inversions _ _)
theorem actual_insertion_adjacent_word_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶
      RuntimeAdjacentPermutationSwap.swapWord (succ (var 0)) (insertedWord (var 0) (var 1) (var 2)) (var 1) ≐
        insertedWord (var 0) (succ (var 1)) (var 2)) :=
  closeUniv 3 (.impI (moving_word _ _ _ Prf.hyp0))
theorem actual_insertion_adjacent_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶
      inversions (succ (var 0)) (insertedWord (var 0) (var 1) (var 2)) ≐
        inversions (succ (var 0)) (insertedWord (var 0) (succ (var 1)) (var 2))+one) :=
  closeUniv 3 (.impI (moving_inversions _ _ _ Prf.hyp0))
theorem actual_inserted_inversions_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶
      inversions (succ (var 0)) (insertedWord (var 0) (var 1) (var 2)) ≐
        inversions (var 0) (var 2)+monus (var 0) (var 1)) :=
  closeUniv 3 (.impI (inserted_inversions _ _ _ Prf.hyp0))
theorem actual_inserted_parity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶
      parity (succ (var 0)) (insertedWord (var 0) (var 1) (var 2)) ≐
        par (inversions (var 0) (var 2)+monus (var 0) (var 1))) :=
  closeUniv 3 (.impI (inserted_parity _ _ _ Prf.hyp0))
theorem actual_inserted_cofactor_parity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶
      parity (succ (var 0)) (insertedWord (var 0) (var 1) (var 2)) ≐
        par (inversions (var 0) (var 2)+(var 0+var 1))) :=
  closeUniv 3 (.impI (inserted_parity_plus _ _ _ Prf.hyp0))
theorem actual_inserted_cofactor_parity_add_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶
      parity (succ (var 0)) (insertedWord (var 0) (var 1) (var 2)) ≐
        par (parity (var 0) (var 2)+par (var 0+var 1))) :=
  closeUniv 3 (.impI (inserted_parity_plus_add _ _ _ Prf.hyp0))
theorem actual_inserted_parity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)
theorem actual_returned_insertion_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2))) ≐ inversions (var 0) (var 2)+monus (var 0) (var 1)) :=
  closeUniv 3 (.impI (returned_count_exact _ _ _ Prf.hyp0))
theorem actual_returned_insertion_parity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶
      sndT (sndT (run (var 0) (var 1) (var 2))) ≐ par (parity (var 0) (var 2)+par (var 0+var 1))) :=
  closeUniv 3 (.impI (returned_parity_cofactor _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Foundations.RuntimePermutationInsertionParity
