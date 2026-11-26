import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantScalarOrder
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantSyntax
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianBalancedRadiusSearch
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantScaleArithmetic
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual least dominant coefficient at every balanced-radius scale

A fixed PR2 evaluator negates the actual rational squared scores. The
inclusive least-argmin scan over 0,...,N-1 therefore returns a positive
coefficient index. Rational ties, rather than raw code equality, determine
the least winner. Positivity follows from the actual balanced-radius
witness, and scale monotonicity follows from genuine score comparisons.
No dominance, positive maximum, monotonicity or scan success is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantSelector

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (score)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE rationalEq selected)
open LeanProofs.IPRA.Analysis.RationalValueBounds (negate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (C N E j h : PTm n) : PTm n := pairT C (pairT N (pairT E (pairT j h)))
def negativeScore (C N E j h r : PTm n) : PTm n := negate (score C N E j h (succ r))
def negativeBody : PTm 2 := negativeScore (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1)))))
  (sndT (sndT (sndT (sndT (var 1))))) (var 0)
def negativeScoreF : PR 2 := PTm.toPR negativeBody
def winner (C N E j h : PTm n) : PTm n := succ (selected negativeScoreF (pred N) (data C N E j h))
def index (C N h : PTm n) : PTm n := winner C N (GaussianBalancedRadiusHeight.E C N)
  (GaussianBalancedRadiusSearch.radiusIndex C N) h
def indexData (C N : PTm n) : PTm n := pairT C N
def indexBody : PTm 2 := index (fstT (var 1)) (sndT (var 1)) (var 0)
def indexF : PR 2 := PTm.toPR indexBody

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (C N E j h : PTm n) :
    Syn.subst σ (data C N E j h) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ E) (Syn.subst σ j) (Syn.subst σ h) := by simp [data]
@[simp] theorem subst_negativeScore {m : ℕ} (σ : Fin n → PTm m) (C N E j h r : PTm n) :
    Syn.subst σ (negativeScore C N E j h r) = negativeScore (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ E) (Syn.subst σ j) (Syn.subst σ h) (Syn.subst σ r) := by simp [negativeScore]
@[simp] theorem subst_winner {m : ℕ} (σ : Fin n → PTm m) (C N E j h : PTm n) :
    Syn.subst σ (winner C N E j h) = winner (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ E) (Syn.subst σ j) (Syn.subst σ h) := by simp [winner]
@[simp] theorem subst_index {m : ℕ} (σ : Fin n → PTm m) (C N h : PTm n) :
    Syn.subst σ (index C N h) = index (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ h) := by simp [index]
@[simp] theorem subst_indexData {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (indexData C N) = indexData (Syn.subst σ C) (Syn.subst σ N) := by simp [indexData]

theorem norm_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq q ≐ GaussianRationalMetric.qnormSq r :=
  RationalAlgebra.add_congr (RationalAlgebra.multiply_congr (congrFst h) (congrFst h))
    (RationalAlgebra.multiply_congr (congrSnd h) (congrSnd h))

theorem score_congr {C C' N N' E E' j j' h h' i i' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hN : Γ ⊢[PRAAx] N ≐ N') (hE : Γ ⊢[PRAAx] E ≐ E')
    (hj : Γ ⊢[PRAAx] j ≐ j') (hh : Γ ⊢[PRAAx] h ≐ h') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    score C N E j h i ≐ score C' N' E' j' h' i' :=
  RationalAlgebra.multiply_congr
    (norm_congr (Foundations.SequenceComposition.entry_congr hC (congrMonus hN hi)))
    (RationalNonnegativePowers.fraction_congr
      (congrAp2 powF (congrMul (.eqRefl _) hi) (congrAp2 powF hj (.eqRefl _)))
      (congrAp2 powF (congrMul (.eqRefl _) hi)
        (congrAp2 powF (congrAdd hE (congrMul (.eqRefl _) hh)) (.eqRefl _))))

theorem score_index_congr (C N E j h : PTm n) {i k : PTm n} (hik : Γ ⊢[PRAAx] i ≐ k) : Γ ⊢[PRAAx]
    score C N E j h i ≐ score C N E j h k :=
  score_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) hik

theorem negative_score_at (C N E j h r : PTm n) : Γ ⊢[PRAAx]
    ap2 negativeScoreF r (data C N E j h) ≐ negate (score C N E j h (succ r)) := by
  have t1 : Γ ⊢[PRAAx] sndT (data C N E j h) ≐ pairT N (pairT E (pairT j h)) := snd_pair _ _
  have t2 := (congrSnd t1).eqTrans (snd_pair _ _)
  have t3 := (congrSnd t2).eqTrans (snd_pair _ _)
  have fields : Γ ⊢[PRAAx]
      negativeScore (fstT (data C N E j h)) (fstT (sndT (data C N E j h)))
        (fstT (sndT (sndT (data C N E j h)))) (fstT (sndT (sndT (sndT (data C N E j h)))))
        (sndT (sndT (sndT (sndT (data C N E j h))))) r ≐ negativeScore C N E j h r :=
    RationalValueBounds.negate_congr (score_congr (fst_pair _ _)
      ((congrFst t1).eqTrans (fst_pair _ _)) ((congrFst t2).eqTrans (fst_pair _ _))
      ((congrFst t3).eqTrans (fst_pair _ _)) ((congrSnd t3).eqTrans (snd_pair _ _)) (.eqRefl _))
  have shape : Syn.subst ![r,data C N E j h] negativeBody =
      negativeScore (fstT (data C N E j h)) (fstT (sndT (data C N E j h)))
        (fstT (sndT (sndT (data C N E j h)))) (fstT (sndT (sndT (sndT (data C N E j h)))))
        (sndT (sndT (sndT (sndT (data C N E j h))))) r := by
    simp only [negativeBody,subst_negativeScore,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  have program := toPR_eq (Γ := Γ) negativeBody ![r,data C N E j h]
  rw [shape] at program
  exact program.eqTrans fields

theorem negative_score_at_degree (C N E j h i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    ap2 negativeScoreF (pred i) (data C N E j h) ≐ negate (score C N E j h i) :=
  (negative_score_at C N E j h (pred i)).eqTrans (RationalValueBounds.negate_congr
    (score_index_congr C N E j h (RationalIntegerNormalization.positive_form hi).eqSymm))

theorem winner_bounds (C N E j h : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (winner C N E j h) ⋏ le (winner C N E j h) N :=
  .andI (zero_lt_succ _) (le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form hN).eqSymm
    ((succ_monus_succ _ _).eqTrans (RationalArgmin.selected_spec negativeScoreF (pred N) (data C N E j h))))

theorem winner_maximal (C N E j h i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    rationalLE (score C N E j h i) (score C N E j h (winner C N E j h)) := by
  have range : Γ ⊢[PRAAx] le (pred i) (pred N) := (succ_monus_succ _ _).eqSymm.eqTrans
    (le_congr (RationalIntegerNormalization.positive_form hi) (RationalIntegerNormalization.positive_form hN) hiN)
  have least := RationalArgmin.selected_minimal negativeScoreF (pred N) (pred i) (data C N E j h) range
  have negative := RationalArgmin.rationalLE_congr (negative_score_at C N E j h _)
    (negative_score_at_degree C N E j h i hi) least
  exact GaussianDominantScalarOrder.unnegate_le _ _ negative

/-- Ties are equality of rational values, without canonical input guards. -/
theorem winner_least (C N E j h i : PTm n) (hi : Γ ⊢[PRAAx] le one i)
    (hTie : Γ ⊢[PRAAx] rationalEq (score C N E j h i) (score C N E j h (winner C N E j h))) : Γ ⊢[PRAAx]
    le (winner C N E j h) i := by
  have negative := GaussianDominantScalarOrder.negate_eq _ _ hTie
  have actual := RationalArgmin.rationalEq_congr (negative_score_at_degree C N E j h i hi).eqSymm
    (negative_score_at C N E j h _).eqSymm negative
  have bound := RationalArgmin.selected_least negativeScoreF (pred N) (pred i) (data C N E j h) actual
  exact le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form hi).eqSymm ((succ_monus_succ _ _).eqTrans bound)

/-- A genuine positive candidate forces the actual selected coefficient's
numerator positive. Only actual per-candidate value representations enter. -/
theorem winner_positive_from_candidate (C N E j h i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N)
    (hni : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N i)) : Γ ⊢[PRAAx]
    le one (GaussianBalancedRadiusSyntax.numerator C N (winner C N E j h)) := by
  have positive := GaussianDominantScalarOrder.positive_from_comparison
    (score C N E j h i) (score C N E j h (winner C N E j h))
    (GaussianDominantSyntax.numerator C N j i) (GaussianDominantSyntax.numerator C N j (winner C N E j h))
    (GaussianDominantSyntax.denominator C N E h i) (GaussianDominantSyntax.denominator C N E h (winner C N E j h))
    (GaussianDominantSyntax.denominator_positive _ _ _ _ _)
    (GaussianDominantSyntax.numerator_positive C N j i hni)
    (GaussianDominantSyntax.score_represents _ _ _ _ _ _) (GaussianDominantSyntax.score_represents _ _ _ _ _ _)
    (winner_maximal C N E j h i hN hi hiN)
  exact GaussianDominantScalarOrder.factor_positive_left _ _ positive

theorem index_congr (C N : PTm n) {h l : PTm n} (hl : Γ ⊢[PRAAx] h ≐ l) : Γ ⊢[PRAAx]
    index C N h ≐ index C N l := by
  ipra_congr (index (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl C, .eqRefl N, hl]

theorem index_at (C N h : PTm n) : Γ ⊢[PRAAx] ap2 indexF h (indexData C N) ≐ index C N h := by
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (index (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (indexData C N),sndT (indexData C N),h]) (σ' := ![C,N,h])
    (fun i => by fin_cases i; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  exact (toPR_eq indexBody ![h,indexData C N]).eqTrans (by
    simpa only [indexBody,subst_index,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using fields)

theorem index_bounds (C N h : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N) : Γ ⊢[PRAAx]
    le one (index C N h) ⋏ le (index C N h) N :=
  winner_bounds _ _ _ _ _ (Prf.andE₁ (Prf.andE₂ hInput))

theorem index_maximal (C N h i : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    rationalLE (score C N (GaussianBalancedRadiusHeight.E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) h i)
      (score C N (GaussianBalancedRadiusHeight.E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) h (index C N h)) :=
  winner_maximal _ _ _ _ _ _ (Prf.andE₁ (Prf.andE₂ hInput)) hi hiN

/-- The positive candidate is the actual failed coefficient already
returned by the balanced-radius search; no maximum-positivity is assumed. -/
theorem index_positive (C N h : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N) : Γ ⊢[PRAAx]
    le one (GaussianBalancedRadiusSyntax.numerator C N (index C N h)) := by
  have witness := GaussianBalancedRadiusSearch.witness_spec C N hInput
  exact winner_positive_from_candidate _ _ _ _ _ _ (Prf.andE₁ (Prf.andE₂ hInput))
    (Prf.andE₁ witness) (Prf.andE₁ (Prf.andE₂ witness)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ witness)))

/-- A larger next winner contradicts the genuine strict scale drop and
both actual maximality comparisons. No monotonicity contract is supplied. -/
theorem index_monotone_step (C N h : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N) : Γ ⊢[PRAAx]
    le (index C N (succ h)) (index C N h) := by
  have oldBounds := index_bounds C N h hInput
  have nextBounds := index_bounds C N (succ h) hInput
  have old := index_maximal C N h (index C N (succ h)) hInput (Prf.andE₁ nextBounds) (Prf.andE₂ nextBounds)
  have next := index_maximal C N (succ h) (index C N h) hInput (Prf.andE₁ oldBounds) (Prf.andE₂ oldBounds)
  refine .orE (lt_or_le (index C N h) (index C N (succ h))) ?_ Prf.hyp0
  have drop := GaussianDominantScaleArithmetic.score_drop C N (GaussianBalancedRadiusHeight.E C N)
    (GaussianBalancedRadiusSearch.radiusIndex C N) h (index C N (succ h)) (index C N h)
    old.wk Prf.hyp0 (index_positive C N h hInput).wk
  exact .botE _ (.impE drop next.wk)

theorem index_offset (C N h r : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N) : Γ ⊢[PRAAx]
    le (index C N (h+r)) (index C N h) := by
  have inputShift : Γ.map Fm.shift ⊢[PRAAx] GaussianBalancedRadiusSyntax.input (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianBalancedRadiusSyntax.subst_input,Syn.shift] using hInput.shift
  have all : Γ ⊢[PRAAx] .all (le (index (Syn.shift C) (Syn.shift N) (Syn.shift h+var 0))
      (index (Syn.shift C) (Syn.shift N) (Syn.shift h))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le,subst_index,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact le_congr (index_congr C N (add_zero h)).eqSymm (.eqRefl _) (le_refl _)
    · simp only [subst_le,subst_index,PTm.subst_add,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let I := le (index (Syn.shift C) (Syn.shift N) (Syn.shift h+var 0)) (index (Syn.shift C) (Syn.shift N) (Syn.shift h))
      have step : I :: Γ.map Fm.shift ⊢[PRAAx] le
          (index (Syn.shift C) (Syn.shift N) (succ (Syn.shift h+var 0)))
          (index (Syn.shift C) (Syn.shift N) (Syn.shift h+var 0)) :=
        index_monotone_step (Syn.shift C) (Syn.shift N) (Syn.shift h+var 0) inputShift.wk
      exact le_trans (le_congr (index_congr _ _ (add_succ _ _).eqSymm) (.eqRefl _) step) Prf.hyp0
  simpa only [subst_le,subst_index,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem index_monotone (C N h l : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N)
    (hl : Γ ⊢[PRAAx] le h l) : Γ ⊢[PRAAx] le (index C N l) (index C N h) :=
  le_congr (index_congr C N (eq_add_of_le hl).eqSymm) (.eqRefl _) (index_offset C N h (monus l h) hInput)

theorem winner_one (C E j h : PTm n) : Γ ⊢[PRAAx] winner C one E j h ≐ one := by
  have bounds := winner_bounds (Γ := Γ) C one E j h (le_refl one)
  exact le_antisymm (Prf.andE₂ bounds) (Prf.andE₁ bounds)

theorem index_least (C N h i : PTm n) (hi : Γ ⊢[PRAAx] le one i)
    (hTie : Γ ⊢[PRAAx] rationalEq
      (score C N (GaussianBalancedRadiusHeight.E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) h i)
      (score C N (GaussianBalancedRadiusHeight.E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) h (index C N h))) : Γ ⊢[PRAAx]
    le (index C N h) i := winner_least _ _ _ _ _ _ hi hTie

/-! Closed numerical endpoints and literal PR evaluator metadata. -/
theorem dominant_winner_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶
      (le one (winner (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
       le (winner (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1))) :=
  closeUniv 5 (.impI (winner_bounds _ _ _ _ _ Prf.hyp0))

theorem dominant_winner_maximal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ le one (var 5) ⟶ le (var 5) (var 1) ⟶
      rationalLE (score (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (score (var 0) (var 1) (var 2) (var 3) (var 4) (winner (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 6 (.impI (.impI (.impI (winner_maximal _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem dominant_winner_least_tie_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶ rationalEq (score (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (score (var 0) (var 1) (var 2) (var 3) (var 4) (winner (var 0) (var 1) (var 2) (var 3) (var 4))) ⟶
      le (winner (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (winner_least _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem dominant_singleton_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (winner (var 0) one (var 1) (var 2) (var 3) ≐ one) := closeUniv 4 (winner_one _ _ _ _)

theorem computed_dominant_index_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianBalancedRadiusSyntax.input (var 0) (var 1) ⟶
      ((le one (index (var 0) (var 1) (var 2)) ⋏ le (index (var 0) (var 1) (var 2)) (var 1)) ⋏
       (le one (GaussianBalancedRadiusSyntax.numerator (var 0) (var 1) (index (var 0) (var 1) (var 2))) ⋏
        le (index (var 0) (var 1) (succ (var 2))) (index (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.andI (index_bounds _ _ _ Prf.hyp0)
    (.andI (index_positive _ _ _ Prf.hyp0) (index_monotone_step _ _ _ Prf.hyp0))))

theorem computed_dominant_maximal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianBalancedRadiusSyntax.input (var 0) (var 1) ⟶ le one (var 3) ⟶ le (var 3) (var 1) ⟶
      rationalLE (score (var 0) (var 1) (GaussianBalancedRadiusHeight.E (var 0) (var 1))
        (GaussianBalancedRadiusSearch.radiusIndex (var 0) (var 1)) (var 2) (var 3))
        (score (var 0) (var 1) (GaussianBalancedRadiusHeight.E (var 0) (var 1))
          (GaussianBalancedRadiusSearch.radiusIndex (var 0) (var 1)) (var 2) (index (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (.impI (.impI (index_maximal _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem computed_dominant_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianBalancedRadiusSyntax.input (var 0) (var 1) ⟶ le (var 2) (var 3) ⟶
      le (index (var 0) (var 1) (var 3)) (index (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (index_monotone _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem dominant_negative_evaluator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (ap2 negativeScoreF (var 5) (data (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
      negate (score (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)))) :=
  closeUniv 6 (negative_score_at _ _ _ _ _ _)

theorem computed_dominant_index_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 indexF (var 2) (indexData (var 0) (var 1)) ≐ index (var 0) (var 1) (var 2)) :=
  closeUniv 3 (index_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianDominantSelector
