import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.GaussianRationalSeparatedDeflation
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalReconstruction
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Monic.GaussianMonicResidualRadius
import IPRADerivations.AnalyticNumberTheory.PowerCleared

/-!
# The product from separated rational root samples

Starting at the monic constant after the final synthetic division, the
evaluation discrepancy against the actual backwards product accumulates
the finite stage remainders. The resulting explicit bound needs only
a residual estimate and separation for rational root samples.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSeparatedReconstruction

open_ipra
open GaussianCoefficientNameBounds (bounded_radius_mono bounded_radius_mono_same)
open GaussianRationalFiniteRoots (stage remaining stage_succ stage_zero stage_length stage_head stage_index_congr
  remaining_step head evaluate_congr)
open GaussianRationalHorner (evaluate qzero qmul qadd)
open GaussianRationalMetric (qsub qnegative bounded distanceBounded)
open GaussianRationalReciprocal (qone bounded_product bounded_sum bound_congr)
open GaussianRationalReconstruction (suffix suffix_final suffix_zero suffix_length suffix_step singleton_evaluation
  suffix_canonical reconstruct_index_congr product product_evaluation)
open GaussianRationalSeparatedDeflation (budget laterResiduals separation later_at stage_residuals)
open GaussianRationalSyntheticDivision (division_evaluation qsub_congr qadd_congr qmul_congr qone_canonical)
open GaussianRationalSumAlgebra (qadd_swap_tail)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def differencesBounded (R y B : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift R)) ⟶
    bounded (qsub (Syn.shift y) (entry (Syn.shift R) (var 0))) (Syn.shift B) one)

ipra_subst differencesBounded [one, Syn.subst_shift, Syn.shift_subst]

theorem difference_at (R y B i : PTm n) (h : Γ ⊢[PRAAx] differencesBounded R y B)
    (hi : Γ ⊢[PRAAx] lt i (length R)) :
    Γ ⊢[PRAAx] bounded (qsub y (entry R i)) B one := by
  have rule : Γ ⊢[PRAAx] lt i (length R) ⟶ bounded (qsub y (entry R i)) B one := by
    simpa [differencesBounded,one] using h.allE i
  exact .impE rule hi

private theorem subtract_after_add (a b c : PTm n) :
    Γ ⊢[PRAAx] qsub (qadd a b) c ≐ qadd (qsub a c) b :=
  qadd_swap_tail a b (qnegative c)

private theorem stage_evaluation (C N R y j : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    evaluate (stage C N R j) y ≐
      qadd (qmul (qsub y (entry R j)) (evaluate (stage C N R (succ j)) y))
        (evaluate (stage C N R j) (entry R j)) :=
  (division_evaluation _ _ _ _ (stage_length C N R j hC (le_of_lt hj))).eqTrans
    (qadd_congr (qmul_congr (.eqRefl _) (evaluate_congr (stage_succ C N R j).eqSymm (.eqRefl _))) (.eqRefl _))

private theorem suffix_evaluation_step (R N y j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] evaluate (suffix R N j) y ≐
      qmul (qsub y (entry R j)) (evaluate (suffix R N (succ j)) y) :=
  (evaluate_congr (suffix_step R N j hj) (.eqRefl _)).eqTrans
    (GaussianRationalLinearProduct.linear_evaluation _ _ _ _
      ((suffix_length R N (succ j)).eqTrans (remaining_step N j hj).eqSymm) (suffix_canonical R N (succ j)))

def discrepancy (C N R y j : PTm n) : PTm n :=
  qsub (evaluate (stage C N R j) y) (evaluate (suffix R N j) y)

ipra_subst discrepancy [suffix]

private theorem discrepancy_index_congr (C N R y : PTm n) {i j : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] discrepancy C N R y i ≐ discrepancy C N R y j :=
  qsub_congr (evaluate_congr (stage_index_congr _ _ _ h) (.eqRefl _))
    (evaluate_congr (reconstruct_index_congr _ _ (congrMonus (.eqRefl _) h)) (.eqRefl _))

private theorem discrepancy_step (C N R y j : PTm n) (hc : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] discrepancy C N R y j ≐
      qadd (qmul (qsub y (entry R j)) (discrepancy C N R y (succ j))) (evaluate (stage C N R j) (entry R j)) :=
  (qsub_congr (stage_evaluation C N R y j hc hj) (suffix_evaluation_step R N y j hj)).eqTrans
    ((subtract_after_add _ _ _).eqTrans
      (qadd_congr (GaussianRationalRoundedPower.multiplication_difference _ _ _) (.eqRefl _)))

private theorem terminal_discrepancy (C N R y : PTm n) (hc : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx] discrepancy C N R y N ≐ qzero := by
  have hLen := (stage_length C N R N hc (le_refl _)).eqTrans (congrSucc (monus_self N))
  have hHead : Γ ⊢[PRAAx] head C ≐ qone :=
    (GaussianTranslatedNonconstant.recode_congr hm).eqTrans (GaussianTranslatedNonconstant.recode_eq _ qone_canonical)
  have a := (GaussianRationalSyntheticCoefficientValues.singleton_evaluation _ y hLen).eqSymm.eqTrans
    ((stage_head C N R N (le_refl _)).eqTrans hHead)
  have b : Γ ⊢[PRAAx] evaluate (suffix R N N) y ≐ qone :=
    (evaluate_congr (suffix_final R N) (.eqRefl y)).eqTrans (singleton_evaluation y)
  exact (qsub_congr a b).eqTrans (GaussianCoefficientNormOrder.qsub_self _)

private theorem budget_mono (E D i N : PTm n) (hd : Γ ⊢[PRAAx] le one D)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] le (budget E D i) (budget E D N) :=
  le_mul_mono (le_refl _) (AnalyticNumberTheory.PowerCleared.pw_le_exp
    (RationalIntegerNormalization.positive_form
      (GaussianRationalHorner.positive_product _ _ (le_succ_self one) hd)) hi)

def errorNumerator (E D N B k : PTm n) : PTm n := budget E D N*pw (B+one) k

ipra_subst errorNumerator [one]

private theorem error_growth (E D N B k : PTm n) :
    Γ ⊢[PRAAx] le (B*errorNumerator E D N B k+budget E D N) (errorNumerator E D N B (succ k)) := by
  let F := budget E D N
  let p := pw (B+one) k
  have hP : Γ ⊢[PRAAx] le one p := GaussianFactorBudget.power_positive _ _
    (le_add_left one B)
  have hF : Γ ⊢[PRAAx] le F (F*p) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl F) hP)
  have sum := add_le_add_right (B*errorNumerator E D N B k) hF
  have e : Γ ⊢[PRAAx] errorNumerator E D N B (succ k) ≐
      B*errorNumerator E D N B k+F*p :=
    (congrMul (.eqRefl _) (pw_succ _ _)).eqTrans (by dsimp only [errorNumerator,F,p]; ipra_ring)
  exact le_congr (.eqRefl _) e.eqSymm (le_congr (by ipra_ring) (by ipra_ring) sum)

def errorLaw (C N R E K D B y k : PTm n) : Fm PTm n := le k N ⟶
  bounded (discrepancy C N R y (remaining N k)) (errorNumerator E D N B k) K

ipra_subst errorLaw

private theorem error_succ (C N R E K D B y k : PTm n)
    (hc : Γ ⊢[PRAAx] length C ≐ succ N) (hl : Γ ⊢[PRAAx] length R ≐ N)
    (hk : Γ ⊢[PRAAx] le one K) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] laterResiduals C R zero E K) (hs : Γ ⊢[PRAAx] separation R D)
    (hy : Γ ⊢[PRAAx] differencesBounded R y B) (step : Γ ⊢[PRAAx] lt k N)
    (prev : Γ ⊢[PRAAx] errorLaw C N R E K D B y k) :
    Γ ⊢[PRAAx] bounded (discrepancy C N R y (remaining N (succ k))) (errorNumerator E D N B (succ k)) K := by
  let j := remaining N (succ k)
  let d := qsub y (entry R j)
  let v := evaluate (stage C N R j) (entry R j)
  let F := budget E D N
  have hj : Γ ⊢[PRAAx] lt j N := le_of_eq_add (d := k) (AnalyticNumberTheory.Totatives.split_lt step)
  have inList : Γ ⊢[PRAAx] lt j (length R) := lt_congr (.eqRefl _) hl.eqSymm hj
  have hb := difference_at R y B j hy inList
  have hRemainder := later_at _ _ _ _ _ _
    (stage_residuals C N R E K D j hc hk hd hr hs (le_of_lt hj)) inList (le_refl _)
  have hRemainder' : Γ ⊢[PRAAx] bounded v F K := bounded_radius_mono_same hk (budget_mono E D j N hd (le_of_lt hj)) hRemainder
  have hPrev := bound_congr (discrepancy_index_congr C N R y (remaining_step N k step)) (.eqRefl _) (.eqRefl _)
    (Prf.impE prev (le_of_lt step))
  have hProd := bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] one*K ≐ K)
    (bounded_product d _ _ _ _ _ (le_refl _) hk hb hPrev)
  have sum := bounded_sum _ _ _ _ _ _ hk hk hProd hRemainder'
  have eq := discrepancy_step C N R y j hc hj
  exact bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ hk hk) hk
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (error_growth E D N B k) (le_refl (K*K)))) sum)

theorem reconstruction_distance (C N R E K D B y : PTm n)
    (hc : Γ ⊢[PRAAx] length C ≐ succ N) (hl : Γ ⊢[PRAAx] length R ≐ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hk : Γ ⊢[PRAAx] le one K) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] laterResiduals C R zero E K) (hs : Γ ⊢[PRAAx] separation R D)
    (hy : Γ ⊢[PRAAx] differencesBounded R y B) :
    Γ ⊢[PRAAx] distanceBounded (evaluate C y) (product R N y) (errorNumerator E D N B N) K := by
  have hc' : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have hl' : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift R) ≐ Syn.shift N := by simpa [Fm.shift,Syn.shift] using hl.shift
  have hk' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift,Syn.shift,one] using hk.shift
  have hd' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift,one] using hd.shift
  have hr' : Γ.map Fm.shift ⊢[PRAAx] laterResiduals (Syn.shift C) (Syn.shift R) zero (Syn.shift E) (Syn.shift K) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  have hs' : Γ.map Fm.shift ⊢[PRAAx] separation (Syn.shift R) (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have hy' : Γ.map Fm.shift ⊢[PRAAx] differencesBounded (Syn.shift R) (Syn.shift y) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hy.shift
  have all : Γ ⊢[PRAAx] .all (errorLaw (Syn.shift C) (Syn.shift N) (Syn.shift R) (Syn.shift E)
      (Syn.shift K) (Syn.shift D) (Syn.shift B) (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, ?_⟩ ?_ ?_
    · exact le_QF _ _
    · simp only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have zeroError := (discrepancy_index_congr C N R y (monus_zero N)).eqTrans (terminal_discrepancy C N R y hc hm)
      exact .impI (bound_congr zeroError.eqSymm (.eqRefl _) (.eqRefl _)
        (GaussianMonicResidualRadius.zero_bounded _ _ hk)).wk
    · simp only [subst_errorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (error_succ _ _ _ _ _ _ _ _ _ hc'.wk.wk hl'.wk.wk hk'.wk.wk hd'.wk.wk hr'.wk.wk
        hs'.wk.wk hy'.wk.wk Prf.hyp0 Prf.hyp1)
  have rule : Γ ⊢[PRAAx] errorLaw C N R E K D B y N := by
    simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  have final := bound_congr (discrepancy_index_congr C N R y (monus_self N)) (.eqRefl _) (.eqRefl _)
    (Prf.impE rule (le_refl _))
  exact bound_congr (qsub_congr (evaluate_congr (stage_zero C N R) (.eqRefl _))
    ((evaluate_congr (suffix_zero R N) (.eqRefl _)).eqTrans (product_evaluation R N y))) (.eqRefl _) (.eqRefl _) final

theorem actual_reconstruction_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (((length (var 0) ≐ succ (var 1)) ⋏ ((length (var 2) ≐ var 1) ⋏ (entry (var 0) zero ≐ qone))) ⟶
      ((le one (var 4) ⋏ le one (var 5)) ⋏ (laterResiduals (var 0) (var 2) zero (var 3) (var 4) ⋏
        (separation (var 2) (var 5) ⋏ differencesBounded (var 2) (var 7) (var 6)))) ⟶
      distanceBounded (evaluate (var 0) (var 7)) (product (var 2) (var 1) (var 7))
        (errorNumerator (var 3) (var 5) (var 1) (var 6) (var 1)) (var 4)) :=
  closeUniv 8 (.impI (.impI (reconstruction_distance _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianRationalSeparatedReconstruction
