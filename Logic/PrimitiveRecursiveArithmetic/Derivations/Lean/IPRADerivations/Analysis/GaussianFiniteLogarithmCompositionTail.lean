import IPRADerivations.Analysis.GaussianFiniteLogarithmBellIdentification
import IPRADerivations.Analysis.GaussianRationalPowerExpansion
import IPRADerivations.Analysis.GaussianCoefficientNameBounds
import IPRADerivations.Analysis.GaussianMonicResidualRadius

/-!
# An actual finite tail on the original C4 half disk

The original stored finite composition has the exact coefficients 1+X
through the numerical cutoff h. Its remaining high Horner prefix times
w^(h+1) is the actual residual. A budget computed from the SAME stored
coefficients bounds this tail on the original Euclidean half disk.
The budget depends on d,K; a uniform auxiliary-radius majorant and the
analytic C4 passage remain separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmCompositionTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul qzero horner hornerF evaluate)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (power bound_congr bounded_product bounded_sum)
open GaussianRationalPowerExpansion (partialSum conservationLeft remaining)
open GaussianFiniteLogarithmPolynomial (composition)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientF : PR 3 := PTm.toPR (entry (var 2) (var 0))
def budget (C : PTm n) : PTm n := GaussianCoefficientNameBounds.ceilM coefficientF (length C) C
@[simp] theorem subst_budget {l : ℕ} (σ : Fin n → PTm l) (C : PTm n) :
    Syn.subst σ (budget C) = budget (Syn.subst σ C) := by simp [budget]

theorem coefficient_at (C i : PTm n) : Γ ⊢[PRAAx] ap3 coefficientF i zero C ≐ entry C i := by
  simpa [coefficientF,ap3] using toPR_eq (Γ := Γ) (entry (var 2) (var 0) : PTm 3) ![i,zero,C]

theorem coefficient_bound (C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) :
    Γ ⊢[PRAAx] bounded (entry C i) (budget C) one :=
  bound_congr (coefficient_at C i) (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.initial_coefficient_bound coefficientF i (length C) C hi)

def prefixBound (C w k : PTm n) : Fm PTm n :=
  le k (length C) ⟶ bounded (horner C w k) (two*budget C) one
@[simp] theorem subst_prefixBound {l : ℕ} (σ : Fin n → PTm l) (C w k : PTm n) :
    (prefixBound C w k).subst σ = prefixBound (Syn.subst σ C) (Syn.subst σ w) (Syn.subst σ k) := by
  simp [prefixBound]

theorem prefix_step (C w k : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two)
    (hk : Γ ⊢[PRAAx] le (succ k) (length C))
    (ih : Γ ⊢[PRAAx] bounded (horner C w k) (two*budget C) one) :
    Γ ⊢[PRAAx] bounded (horner C w (succ k)) (two*budget C) one := by
  have prod := bounded_product _ _ _ _ _ _ (le_refl (one : PTm n)) (le_succ_self one) ih hw
  have reduced : Γ ⊢[PRAAx] bounded (qmul (horner C w k) w) (budget C) one :=
    GaussianMonicResidualRadius.bounded_cancel _ _ _ two (le_refl _) (le_succ_self one)
      (bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) prod)
  exact bound_congr (GaussianRationalHorner.horner_succ C w k).eqSymm (by ipra_ring) (by ipra_ring)
    (bounded_sum _ _ _ _ _ _ (le_refl _) (le_refl _) reduced (coefficient_bound C k hk))

/-- A genuine guarded QF induction reads every actual original coefficient.
The original half-disk keeps its Euclidean radius, without an L1 enlargement. -/
theorem prefix_bound (C w k : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two)
    (hk : Γ ⊢[PRAAx] le k (length C)) :
    Γ ⊢[PRAAx] bounded (horner C w k) (two*budget C) one := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) one two := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Syn.shift] using hw.shift
  have all : Γ ⊢[PRAAx] .all (prefixBound (Syn.shift C) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (bound_congr (GaussianRationalHorner.horner_zero C w).eqSymm (.eqRefl _) (.eqRefl _)
        (GaussianMonicResidualRadius.zero_bounded _ one (le_refl _))).wk
    · simp only [subst_prefixBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact prefix_step _ _ _ shifted.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixBound C w k := by
    simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

def highPart (C N h w : PTm n) : PTm n :=
  qmul (horner C w (monus N h)) (power w (succ h))
@[simp] theorem subst_highPart {l : ℕ} (σ : Fin n → PTm l) (C N h w : PTm n) :
    Syn.subst σ (highPart C N h w) = highPart (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ w) := by
  simp [highPart]

theorem high_part_bound (C N h w : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hw : Γ ⊢[PRAAx] bounded w one two) :
    Γ ⊢[PRAAx] bounded (highPart C N h w) (budget C) (pw two h) := by
  have pos := GaussianFactorBudget.power_positive (Γ := Γ) two h (le_succ_self one)
  have posNext := GaussianFactorBudget.power_positive (Γ := Γ) two (succ h) (le_succ_self one)
  have hpref := prefix_bound C w (monus N h) hw
    (le_trans (GaussianMonicResidualRadius.monus_le_left N h)
      (le_congr (.eqRefl _) hLen.eqSymm (le_succ_self N)))
  have pow := GaussianRationalReciprocal.bounded_power w one two (succ h) (le_succ_self one) hw
  have prod := bounded_product _ _ _ _ _ _ (le_refl _) posNext hpref pow
  have numerator : Γ ⊢[PRAAx] (two*budget C)*pw one (succ h) ≐ budget C*two := by
    exact (congrMul (.eqRefl _) (GaussianPolynomialPerturbation.one_power (succ h))).eqTrans (by ipra_ring)
  have denominator : Γ ⊢[PRAAx] one*pw two (succ h) ≐ pw two h*two :=
    (one_mul _).eqTrans (pw_succ two h)
  exact GaussianMonicResidualRadius.bounded_cancel _ _ _ two pos (le_succ_self one)
    (bound_congr (.eqRefl _) numerator denominator prod)

/-- The high part is extracted from the actual original Horner evaluator,
not supplied as a formal power-series identity. -/
theorem tail_identity (C N h w : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hh : Γ ⊢[PRAAx] le h N) : Γ ⊢[PRAAx]
    qsub (evaluate C w) (partialSum C N w (succ h)) ≐ highPart C N h w := by
  have split := GaussianRationalPowerExpansion.conservation C N w (succ h) hLen
    (le_congr (succ_eq_add_one h).eqSymm (succ_eq_add_one N).eqSymm (add_le_add_right one hh))
  have form : Γ ⊢[PRAAx] conservationLeft C N w (succ h) ≐
      qadd (highPart C N h w) (partialSum C N w (succ h)) :=
    qadd_congr (qmul_congr (congrAp3 hornerF (GaussianRationalPowerExpansion.remaining_succ N h)
      (.eqRefl _) (.eqRefl _)) (.eqRefl _)) (.eqRefl _)
  exact (GaussianRationalSyntheticDivision.qsub_congr (split.eqSymm.eqTrans form) (.eqRefl _)).eqTrans
    (GaussianReciprocalHorner.qsub_add_cancel _ _ (GaussianRationalHorner.qmul_canonical _ _))

theorem truncation_error (C N h w : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hh : Γ ⊢[PRAAx] le h N) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C w) (partialSum C N w (succ h)) (budget C) (pw two h) :=
  bound_congr (tail_identity C N h w hLen hh).eqSymm (.eqRefl _) (.eqRefl _)
    (high_part_bound C N h w hLen hw)


theorem cutoff_degree (d K h : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K) : Γ ⊢[PRAAx] le h (K*d) :=
  le_trans hK (le_congr (by ipra_ring) (.eqRefl _)
    (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl K) (le_trans h1 hd)))

theorem composition_term_low (d K w e : PTm n) (h1 : Γ ⊢[PRAAx] le one d)
    (hK1 : Γ ⊢[PRAAx] le one K) (he : Γ ⊢[PRAAx] le e one) : Γ ⊢[PRAAx]
    GaussianOffDominantTerms.term (composition d K) (K*d) w e ≐ qmul qone (power w e) :=
  qmul_congr
    ((GaussianRationalLowCoefficientConvolution.exponent_inside _ _ e
      (le_trans he (cutoff_degree d K one (le_refl _) h1 hK1))).eqSymm.eqTrans
      (GaussianFiniteLogarithmBellIdentification.composition_low d K e (le_trans he h1) (le_trans he hK1) he))
    (.eqRefl _)

theorem composition_term_high (d K h w e : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K)
    (he : Γ ⊢[PRAAx] le e h) (h2 : Γ ⊢[PRAAx] le two e) : Γ ⊢[PRAAx]
    GaussianOffDominantTerms.term (composition d K) (K*d) w e ≐ qzero :=
  (qmul_congr
    ((GaussianRationalLowCoefficientConvolution.exponent_inside _ _ e
      (le_trans he (cutoff_degree d K h h1 hd hK))).eqSymm.eqTrans
      (GaussianFiniteLogarithmBellIdentification.composition_high d K e (le_trans he hd) (le_trans he hK) h2))
    (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)

def linearValue (w : PTm n) : PTm n := qadd qone w
@[simp] theorem subst_linearValue {l : ℕ} (σ : Fin n → PTm l) (w : PTm n) :
    Syn.subst σ (linearValue w) = linearValue (Syn.subst σ w) := by simp [linearValue]

theorem first_two (d K w : PTm n) (hd : Γ ⊢[PRAAx] le one d) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    partialSum (composition d K) (K*d) w two ≐ linearValue w := by
  have hN := cutoff_degree d K one (le_refl _) hd hK
  have t0 := (composition_term_low d K w zero hd hK (zero_le one)).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalReciprocal.power_zero w)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right qone GaussianRationalSyntheticDivision.qone_canonical))
  have p1 := (GaussianRationalPowerExpansion.prefix_succ (composition d K) (K*d) w zero (zero_le _)).eqTrans
    ((qadd_congr (GaussianRationalPowerExpansion.prefix_zero _ _ _) t0).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add qone GaussianRationalSyntheticDivision.qone_canonical))
  have t1 := (composition_term_low d K w one hd hK (le_refl _)).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      ((GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalReciprocal.power_canonical w one)).eqTrans
        ((GaussianRationalReciprocal.power_succ w zero).eqTrans
          (qmul_congr (GaussianRationalReciprocal.power_zero w) (.eqRefl _)))))
  have p2 := (GaussianRationalPowerExpansion.prefix_succ (composition d K) (K*d) w one hN).eqTrans
    (qadd_congr p1 t1)
  exact p2.eqTrans ((qadd_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
    ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
      ((GaussianRationalSumAlgebra.contextual_unit w qone).eqTrans
        (GaussianReciprocalHorner.qadd_commutative _ _))))

def lowSumLaw (d K h w m : PTm n) : Fm PTm n := le one m ⟶ le m h ⟶
  partialSum (composition d K) (K*d) w (succ m) ≐ linearValue w
@[simp] theorem subst_lowSumLaw {l : ℕ} (σ : Fin n → PTm l) (d K h w m : PTm n) :
    (lowSumLaw d K h w m).subst σ = lowSumLaw (Syn.subst σ d) (Syn.subst σ K)
      (Syn.subst σ h) (Syn.subst σ w) (Syn.subst σ m) := by simp [lowSumLaw]

theorem low_sum_step (d K h w m : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K)
    (hm : Γ ⊢[PRAAx] le (succ m) h) (ih : Γ ⊢[PRAAx] lowSumLaw d K h w m) :
    Γ ⊢[PRAAx] partialSum (composition d K) (K*d) w (succ (succ m)) ≐ linearValue w := by
  refine .orE (zero_or_succ m) ?_ ?_
  · have idx : ((m ≐ zero) :: Γ) ⊢[PRAAx] succ (succ m) ≐ two := congrSucc (congrSucc Prf.hyp0)
    exact (congrAp3 hornerF idx (.eqRefl _) (.eqRefl _)).eqTrans
      (first_two d K w (le_trans h1.wk hd.wk) (le_trans h1.wk hK.wk))
  · have m1 : ((m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] le one m :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_of_eq_add (d := pred m) (by ipra_ring))
    have sumOld : ((m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] partialSum (composition d K) (K*d) w (succ m) ≐ linearValue w :=
      .impE (.impE ih.wk m1) (le_trans (le_succ_self m) hm.wk)
    have t0 := composition_term_high d K h w (succ m) h1.wk hd.wk hK.wk hm.wk
      (le_congr (succ_eq_add_one one).eqSymm (succ_eq_add_one m).eqSymm (add_le_add_right one m1))
    exact (GaussianRationalPowerExpansion.prefix_succ _ _ _ (succ m)
      (le_trans hm.wk (cutoff_degree d K h h1.wk hd.wk hK.wk))).eqTrans
      ((qadd_congr sumOld t0).eqTrans (GaussianReciprocalHorner.qadd_zero_right _
        (GaussianRationalHorner.qadd_canonical _ _)))

/-- Exact Bell identification kills the entire actual low tail above degree
one, through the ORIGINAL minimum cutoff, without any infinite sum. -/
theorem low_sum (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K) : Γ ⊢[PRAAx]
    partialSum (composition d K) (K*d) w (succ h) ≐ linearValue w := by
  have h1s : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift h) := by simpa [Fm.shift,Syn.shift] using h1.shift
  have hds : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift h) (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have hKs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift h) (Syn.shift K) := by simpa [Fm.shift,Syn.shift] using hK.shift
  have all : Γ ⊢[PRAAx] .all (lowSumLaw (Syn.shift d) (Syn.shift K) (Syn.shift h) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_lowSumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI (.impI ?_)
      exact .botE _ (lt_irrefl zero .bot Prf.hyp1)
    · simp only [subst_lowSumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (.impI (low_sum_step _ _ _ _ _ h1s.wk.wk.wk hds.wk.wk.wk hKs.wk.wk.wk Prf.hyp0 Prf.hyp0.wk.wk))
  have rule : Γ ⊢[PRAAx] lowSumLaw d K h w h := by
    simpa only [subst_lowSumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE h
  exact .impE (.impE rule h1) (le_refl _)

/-- A finite C4 estimate with a budget computed from its literal stored
coefficients. This stage-dependent budget is not a convergence modulus. -/
theorem composition_error (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K)
    (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (composition d K) w) (linearValue w) (budget (composition d K)) (pw two h) := by
  exact bound_congr (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (low_sum d K h w h1 hd hK))
    (.eqRefl _) (.eqRefl _)
    (truncation_error _ _ h w (GaussianRationalPolynomialExponential.polynomial_length _ _ _)
      (cutoff_degree d K h h1 hd hK) hw)


theorem composition_residual (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K) : Γ ⊢[PRAAx]
    qsub (evaluate (composition d K) w) (linearValue w) ≐ highPart (composition d K) (K*d) h w :=
  (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (low_sum d K h w h1 hd hK).eqSymm).eqTrans
    (tail_identity _ _ h w (GaussianRationalPolynomialExponential.polynomial_length _ _ _)
      (cutoff_degree d K h h1 hd hK))

/-! Actual PR4 returned data keeps the original composition, its internally
computed coefficient budget, the dyadic denominator, the high part and
literal evaluator residual together. None of these is an input law. -/
def output (d K h w : PTm n) : PTm n := pairT (composition d K)
  (pairT (budget (composition d K)) (pairT (pw two h)
    (pairT (highPart (composition d K) (K*d) h w)
      (qsub (evaluate (composition d K) w) (linearValue w)))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (d K h w : PTm n) : PTm n := app outputF ![d,K,h,w]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d K h w : PTm n) :
    Syn.subst σ (output d K h w) = output (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ h) (Syn.subst σ w) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d K h w : PTm n) :
    Syn.subst σ (run d K h w) = run (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ h) (Syn.subst σ w) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (d K h w : PTm n) : Γ ⊢[PRAAx] run d K h w ≐ output d K h w := by
  simpa [run,outputF] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![d,K,h,w]
theorem returned_composition (d K h w : PTm n) : Γ ⊢[PRAAx]
    fstT (run d K h w) ≐ composition d K :=
  (congrFst (program_at d K h w)).eqTrans (fst_pair _ _)
theorem returned_tail (d K h w : PTm n) : Γ ⊢[PRAAx] sndT (run d K h w) ≐
    pairT (budget (composition d K)) (pairT (pw two h)
      (pairT (highPart (composition d K) (K*d) h w)
        (qsub (evaluate (composition d K) w) (linearValue w)))) :=
  (congrSnd (program_at d K h w)).eqTrans (snd_pair _ _)
theorem returned_budget (d K h w : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run d K h w)) ≐ budget (composition d K) :=
  (congrFst (returned_tail d K h w)).eqTrans (fst_pair _ _)
theorem returned_rest (d K h w : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d K h w)) ≐
    pairT (pw two h) (pairT (highPart (composition d K) (K*d) h w)
      (qsub (evaluate (composition d K) w) (linearValue w))) :=
  (congrSnd (returned_tail d K h w)).eqTrans (snd_pair _ _)
theorem returned_denominator (d K h w : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run d K h w))) ≐ pw two h :=
  (congrFst (returned_rest d K h w)).eqTrans (fst_pair _ _)
theorem returned_pair (d K h w : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d K h w))) ≐
    pairT (highPart (composition d K) (K*d) h w)
      (qsub (evaluate (composition d K) w) (linearValue w)) :=
  (congrSnd (returned_rest d K h w)).eqTrans (snd_pair _ _)
theorem returned_high (d K h w : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run d K h w)))) ≐ highPart (composition d K) (K*d) h w :=
  (congrFst (returned_pair d K h w)).eqTrans (fst_pair _ _)
theorem returned_residual (d K h w : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run d K h w)))) ≐ qsub (evaluate (composition d K) w) (linearValue w) :=
  (congrSnd (returned_pair d K h w)).eqTrans (snd_pair _ _)
theorem returned_error (d K h w : PTm n) (h1 : Γ ⊢[PRAAx] le one h)
    (hd : Γ ⊢[PRAAx] le h d) (hK : Γ ⊢[PRAAx] le h K)
    (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    bounded (sndT (sndT (sndT (sndT (run d K h w)))))
      (fstT (sndT (run d K h w))) (fstT (sndT (sndT (run d K h w)))) :=
  bound_congr (returned_residual d K h w).eqSymm (returned_budget d K h w).eqSymm
    (returned_denominator d K h w).eqSymm (composition_error d K h w h1 hd hK hw)

theorem computed_coefficient_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (length (var 0)) ⟶ bounded (entry (var 0) (var 1)) (budget (var 0)) one) :=
  closeUniv 2 (.impI (coefficient_bound _ _ Prf.hyp0))
theorem half_disk_prefix_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bounded (var 1) one two ⟶ le (var 2) (length (var 0)) ⟶
      bounded (horner (var 0) (var 1) (var 2)) (two*budget (var 0)) one) :=
  closeUniv 3 (.impI (.impI (prefix_bound _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_truncation_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le (var 2) (var 1) ⟶ bounded (var 3) one two ⟶
      distanceBounded (evaluate (var 0) (var 3)) (partialSum (var 0) (var 1) (var 3) (succ (var 2)))
        (budget (var 0)) (pw two (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (truncation_error _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem finite_composition_low_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      partialSum (composition (var 0) (var 1)) (var 1*var 0) (var 3) (succ (var 2)) ≐ linearValue (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (low_sum _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem finite_composition_residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      qsub (evaluate (composition (var 0) (var 1)) (var 3)) (linearValue (var 3)) ≐
        highPart (composition (var 0) (var 1)) (var 1*var 0) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (composition_residual _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem finite_composition_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ bounded (var 3) one two ⟶
      distanceBounded (evaluate (composition (var 0) (var 1)) (var 3)) (linearValue (var 3))
        (budget (composition (var 0) (var 1))) (pw two (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (composition_error _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_tail_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem returned_tail_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶ bounded (var 3) one two ⟶
      bounded (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (returned_error _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmCompositionTail
