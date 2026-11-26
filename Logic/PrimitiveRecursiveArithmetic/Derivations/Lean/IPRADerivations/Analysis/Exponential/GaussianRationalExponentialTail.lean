import IPRADerivations.Analysis.Exponential.GaussianFiniteExponentialWeightedNorm
import IPRADerivations.Analysis.Exponential.ExponentialTail
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual Gaussian finite exponential and its scalar tail

The tail sums the SAME original factorial-weighted scalar body at
indices N+i. A genuine QF invariant binds its Euclidean norm to the
existing cleared natural majorant tsum(N,B,k)/(N+k)!. The checked
native exponential tail then bounds actual finite cutoff differences.
No completed exponential or supplied summand/output law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalExponentialTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul canonical positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (power bound_congr bounded_product bounded_sum)
open GaussianRationalPolynomialExponential (inverseFactorial factorial_positive scalarBody scalarSum)
open GaussianRationalFiniteSum (sum sum_canonical)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (q N : PTm n) : PTm n := pairT N q
def shiftedBody : PTm 2 := inst2 scalarBody (fstT (var 1)+var 0) (sndT (var 1))
def tail (q N k : PTm n) : PTm n := sum shiftedBody k (data q N)
def scalarPrefix (q N : PTm n) : PTm n := sum scalarBody N q
def tailNumerator (N B k : PTm n) : PTm n := ExponentialTail.tsum N B k
def tailDenominator (N k : PTm n) : PTm n := fact (N+k)
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (q N : PTm n) :
    Syn.subst σ (data q N) = data (Syn.subst σ q) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_tail {l : ℕ} (σ : Fin n → PTm l) (q N k : PTm n) :
    Syn.subst σ (tail q N k) = tail (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ k) := by simp [tail]
@[simp] theorem subst_scalarPrefix {l : ℕ} (σ : Fin n → PTm l) (q N : PTm n) :
    Syn.subst σ (scalarPrefix q N) = scalarPrefix (Syn.subst σ q) (Syn.subst σ N) := by simp [scalarPrefix]
@[simp] theorem subst_tailNumerator {l : ℕ} (σ : Fin n → PTm l) (N B k : PTm n) :
    Syn.subst σ (tailNumerator N B k) = tailNumerator (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [tailNumerator,ExponentialTail.tsum]
@[simp] theorem subst_tailDenominator {l : ℕ} (σ : Fin n → PTm l) (N k : PTm n) :
    Syn.subst σ (tailDenominator N k) = tailDenominator (Syn.subst σ N) (Syn.subst σ k) := by simp [tailDenominator,fact]

theorem body_at (q N i : PTm n) : Γ ⊢[PRAAx]
    inst2 shiftedBody i (data q N) ≐ qmul (inverseFactorial (N+i)) (power q (N+i)) := by
  have e : inst2 shiftedBody i (data q N) =
      qmul (inverseFactorial (fstT (data q N)+i)) (power (sndT (data q N)) (fstT (data q N)+i)) := by
    simp [shiftedBody,scalarBody,inst2]
  rw [e]
  have hN : Γ ⊢[PRAAx] fstT (data q N)+i ≐ N+i := congrAdd (fst_pair N q) (.eqRefl i)
  have inv : Γ ⊢[PRAAx] inverseFactorial (fstT (data q N)+i) ≐ inverseFactorial (N+i) := by
    ipra_congr (inverseFactorial (var 0) : PTm 1) with [hN]
  exact qmul_congr inv (congrAp2 GaussianRationalReciprocal.powerF hN (snd_pair N q))

theorem tail_zero (q N : PTm n) : Γ ⊢[PRAAx] tail q N zero ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _
theorem tail_canonical (q N k : PTm n) : Γ ⊢[PRAAx] canonical (tail q N k) := sum_canonical _ _ _
theorem tail_succ (q N k : PTm n) : Γ ⊢[PRAAx] tail q N (succ k) ≐
    qadd (tail q N k) (qmul (inverseFactorial (N+k)) (power q (N+k))) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (body_at q N k))

theorem term_bound (q B e : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    bounded (qmul (inverseFactorial e) (power q e)) (pw B e) (fact e) := by
  have inv : Γ ⊢[PRAAx] bounded (inverseFactorial e) one (fact e) :=
    GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (factorial_positive e)
      (RationalArgmin.rationalLE_congr (GaussianFiniteExponentialWeightedNorm.inverse_factorial_norm e).eqSymm
        (.eqRefl _) (RationalArgmin.reflexive _))
  have pwr : Γ ⊢[PRAAx] bounded (power q e) (pw B e) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (GaussianPolynomialPerturbation.one_power e)
      (GaussianRationalReciprocal.bounded_power q B one e (le_refl _) hq)
  exact bound_congr (.eqRefl _) (one_mul _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (factorial_positive e) (le_refl _) inv pwr)

def boundLaw (q N B k : PTm n) : Fm PTm n := bounded (tail q N k) (tailNumerator N B k) (tailDenominator N k)
@[simp] theorem subst_boundLaw {l : ℕ} (σ : Fin n → PTm l) (q N B k : PTm n) :
    (boundLaw q N B k).subst σ = boundLaw (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [boundLaw]

theorem bound_zero (q N B : PTm n) : Γ ⊢[PRAAx] boundLaw q N B zero :=
  bound_congr (tail_zero q N).eqSymm (ExponentialTail.tsum_zero N B).eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero _ (factorial_positive _))

theorem bound_step (q N B k : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one)
    (ih : Γ ⊢[PRAAx] boundLaw q N B k) : Γ ⊢[PRAAx] boundLaw q N B (succ k) := by
  have pos := factorial_positive (Γ := Γ) (N+k)
  have nextPos := factorial_positive (Γ := Γ) (N+succ k)
  have combined := bounded_sum _ _ _ _ _ _ pos pos ih (term_bound q B (N+k) hq)
  have radius : Γ ⊢[PRAAx] le
      ((tailNumerator N B k*fact (N+k)+pw B (N+k)*fact (N+k))*tailDenominator N (succ k))
      (tailNumerator N B (succ k)*(fact (N+k)*fact (N+k))) := by
    have t := natEq (ExponentialTail.tsum_succ (Γ := Γ) N B k)
    have f := natEq ((congrAp2 factF (add_succ (Γ := Γ) N k) (.eqRefl zero)).eqTrans (fact_succ (N+k) zero))
    refine le_of_eq_add (d := zero) ?_
    apply deriveNat; unfold tailNumerator tailDenominator; ipra_simps; rw [t,f]; ring
  exact bound_congr (tail_succ q N k).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ pos pos) nextPos radius combined)

/-- The actual finite sum, not an externally supplied majorant relation,
is bounded by the original cleared exponential-tail program. -/
theorem tail_bound (q N B k : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    boundLaw q N B k := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift q) (Syn.shift B) one := by
    simpa [Fm.shift,Syn.shift] using hq.shift
  have all : Γ ⊢[PRAAx] .all (boundLaw (Syn.shift q) (Syn.shift N) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using bound_zero q N B
    · simp only [subst_boundLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact bound_step (Syn.shift q) (Syn.shift N) (Syn.shift B) (var 0) hs.wk Prf.hyp0
  simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

def cutoff (B p : PTm n) : PTm n := ExponentialTail.Nt B p
def precisionDenominator (p : PTm n) : PTm n := pw two (p+num 3)
@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (B p : PTm n) :
    Syn.subst σ (cutoff B p) = cutoff (Syn.subst σ B) (Syn.subst σ p) := by simp [cutoff,ExponentialTail.Nt]
@[simp] theorem subst_precisionDenominator {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (precisionDenominator p) = precisionDenominator (Syn.subst σ p) := by simp [precisionDenominator]

theorem precision_positive (p : PTm n) : Γ ⊢[PRAAx] le one (precisionDenominator p) :=
  GaussianFactorBudget.power_positive _ _ (le_succ_self one)

theorem dyadic_tail_bound (q B p k : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    bounded (tail q (cutoff B p) k) one (precisionDenominator p) := by
  have radius : Γ ⊢[PRAAx] le (tailNumerator (cutoff B p) B k*precisionDenominator p)
      (one*tailDenominator (cutoff B p) k) :=
    le_congr (congrMul (.eqRefl _) (congrAp2 powF (by ipra_ring) (.eqRefl _))) (one_mul _).eqSymm
      (ExponentialTail.exp_tail B p k)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (factorial_positive _)
    (precision_positive p) radius (tail_bound q (cutoff B p) B k hq)

theorem prefix_succ (q N : PTm n) : Γ ⊢[PRAAx] scalarPrefix q (succ N) ≐
    qadd (scalarPrefix q N) (qmul (inverseFactorial N) (power q N)) := by
  simpa only [scalarPrefix,GaussianRationalPolynomialExponential.scalar_body_at] using
    GaussianRationalFiniteSum.sum_succ (Γ := Γ) scalarBody N q

def splitLaw (q N k : PTm n) : Fm PTm n := scalarPrefix q (N+k) ≐ qadd (scalarPrefix q N) (tail q N k)
@[simp] theorem subst_splitLaw {l : ℕ} (σ : Fin n → PTm l) (q N k : PTm n) :
    (splitLaw q N k).subst σ = splitLaw (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ k) := by simp [splitLaw]

theorem split_zero (q N : PTm n) : Γ ⊢[PRAAx] splitLaw q N zero :=
  (GaussianRationalFiniteSum.sum_index_congr scalarBody (add_zero N) (.eqRefl q)).eqTrans
    ((qadd_congr (.eqRefl _) (tail_zero q N)).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (sum_canonical _ _ _))).eqSymm

theorem split_step (q N k : PTm n) (ih : Γ ⊢[PRAAx] splitLaw q N k) : Γ ⊢[PRAAx] splitLaw q N (succ k) :=
  (GaussianRationalFiniteSum.sum_index_congr scalarBody (add_succ N k) (.eqRefl q)).eqTrans
    ((prefix_succ q (N+k)).eqTrans ((qadd_congr ih (.eqRefl _)).eqTrans
      ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans
        (qadd_congr (.eqRefl _) (tail_succ q N k).eqSymm))))

/-- Literal split of the SAME original scalarBody sum. -/
theorem prefix_split (q N k : PTm n) : Γ ⊢[PRAAx] splitLaw q N k := by
  have all : Γ ⊢[PRAAx] .all (splitLaw (Syn.shift q) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using split_zero q N
    · simp only [subst_splitLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact split_step (Syn.shift q) (Syn.shift N) (var 0) Prf.hyp0
  simpa only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem prefix_difference (q N k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qsub (scalarPrefix q (N+k)) (scalarPrefix q N) ≐ tail q N k :=
  (qsub_congr (prefix_split q N k) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (tail_canonical q N k))

theorem prefix_distance (q B p k : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    distanceBounded (scalarPrefix q (cutoff B p+k)) (scalarPrefix q (cutoff B p)) one (precisionDenominator p) :=
  bound_congr (prefix_difference q (cutoff B p) k).eqSymm (.eqRefl _) (.eqRefl _) (dyadic_tail_bound q B p k hq)

def lastIndex (B p : PTm n) : PTm n := pred (cutoff B p)
@[simp] theorem subst_lastIndex {l : ℕ} (σ : Fin n → PTm l) (B p : PTm n) :
    Syn.subst σ (lastIndex B p) = lastIndex (Syn.subst σ B) (Syn.subst σ p) := by simp [lastIndex]
theorem cutoff_positive (B p : PTm n) : Γ ⊢[PRAAx] le one (cutoff B p) :=
  le_of_eq_add (d := B+B+B*(B+B)+p+num 3) (by unfold cutoff ExponentialTail.Nt; ipra_ring)
theorem last_successor (B p : PTm n) : Γ ⊢[PRAAx] succ (lastIndex B p) ≐ cutoff B p :=
  (RationalIntegerNormalization.positive_form (cutoff_positive B p)).eqSymm

theorem scalar_initial (q B p : PTm n) : Γ ⊢[PRAAx] scalarSum q (lastIndex B p) ≐ scalarPrefix q (cutoff B p) :=
  GaussianRationalFiniteSum.sum_index_congr scalarBody (last_successor B p) (.eqRefl q)
theorem scalar_later (q B p k : PTm n) : Γ ⊢[PRAAx] scalarSum q (lastIndex B p+k) ≐ scalarPrefix q (cutoff B p+k) :=
  GaussianRationalFiniteSum.sum_index_congr scalarBody
    ((by ipra_ring : Γ ⊢[PRAAx] succ (lastIndex B p+k) ≐ succ (lastIndex B p)+k).eqTrans
      (congrAdd (last_successor B p) (.eqRefl k))) (.eqRefl q)

/-- The actual original scalarSum, at the computed last included index
and ANY later finite cutoff, has the same certified dyadic tail error. -/
theorem scalar_cutoff_distance (q B p k : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum q (lastIndex B p+k)) (scalarSum q (lastIndex B p)) one (precisionDenominator p) :=
  GaussianRationalDistanceOrder.distance_congr (scalar_later q B p k).eqSymm (scalar_initial q B p).eqSymm
    (.eqRefl _) (.eqRefl _) (prefix_distance q B p k hq)

/-! Actual PR4 payload: the real scalar tail, both original scalar
partial sums, the computed last included index and dyadic denominator. -/
def output (q B p k : PTm n) : PTm n := pairT (tail q (cutoff B p) k)
  (pairT (scalarSum q (lastIndex B p)) (pairT (scalarSum q (lastIndex B p+k))
    (pairT (lastIndex B p) (precisionDenominator p))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (q B p k : PTm n) : PTm n := PTm.app outputF ![q,B,p,k]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (q B p k : PTm n) :
    Syn.subst σ (output q B p k) = output (Syn.subst σ q) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ k) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (q B p k : PTm n) :
    Syn.subst σ (run q B p k) = run (Syn.subst σ q) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ k) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (q B p k : PTm n) : Γ ⊢[PRAAx] run q B p k ≐ output q B p k := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![q,B,p,k]
theorem returned_tail (q B p k : PTm n) : Γ ⊢[PRAAx] fstT (run q B p k) ≐ tail q (cutoff B p) k :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_rest (q B p k : PTm n) : Γ ⊢[PRAAx] sndT (run q B p k) ≐
    pairT (scalarSum q (lastIndex B p)) (pairT (scalarSum q (lastIndex B p+k)) (pairT (lastIndex B p) (precisionDenominator p))) :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_initial (q B p k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run q B p k)) ≐ scalarSum q (lastIndex B p) :=
  (congrFst (returned_rest _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_suffix (q B p k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run q B p k)) ≐
    pairT (scalarSum q (lastIndex B p+k)) (pairT (lastIndex B p) (precisionDenominator p)) :=
  (congrSnd (returned_rest _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_later (q B p k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run q B p k))) ≐ scalarSum q (lastIndex B p+k) :=
  (congrFst (returned_suffix _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_pair (q B p k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run q B p k))) ≐ pairT (lastIndex B p) (precisionDenominator p) :=
  (congrSnd (returned_suffix _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_last_index (q B p k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run q B p k)))) ≐ lastIndex B p :=
  (congrFst (returned_pair _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_denominator (q B p k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run q B p k)))) ≐ precisionDenominator p :=
  (congrSnd (returned_pair _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_tail_bound (q B p k : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    bounded (fstT (run q B p k)) one (sndT (sndT (sndT (sndT (run q B p k))))) :=
  bound_congr (returned_tail _ _ _ _).eqSymm (.eqRefl _) (returned_denominator _ _ _ _).eqSymm
    (dyadic_tail_bound q B p k hq)
theorem returned_distance (q B p k : PTm n) (hq : Γ ⊢[PRAAx] bounded q B one) : Γ ⊢[PRAAx]
    distanceBounded (fstT (sndT (sndT (run q B p k)))) (fstT (sndT (run q B p k)))
      one (sndT (sndT (sndT (sndT (run q B p k))))) :=
  GaussianRationalDistanceOrder.distance_congr (returned_later _ _ _ _).eqSymm (returned_initial _ _ _ _).eqSymm
    (.eqRefl _) (returned_denominator _ _ _ _).eqSymm (scalar_cutoff_distance q B p k hq)

theorem original_scalar_factorial_term_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bounded (var 0) (var 1) one ⟶ bounded (qmul (inverseFactorial (var 2)) (power (var 0) (var 2)))
      (pw (var 1) (var 2)) (fact (var 2))) := closeUniv 3 (.impI (term_bound _ _ _ Prf.hyp0))
theorem actual_scalar_tail_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 0) (var 2) one ⟶ boundLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (tail_bound _ _ _ _ Prf.hyp0))
theorem actual_scalar_exponential_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (splitLaw (var 0) (var 1) (var 2)) := closeUniv 3 (prefix_split _ _ _)
theorem actual_scalar_exponential_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalMetric.qsub (scalarPrefix (var 0) (var 1+var 2)) (scalarPrefix (var 0) (var 1)) ≐ tail (var 0) (var 1) (var 2)) :=
  closeUniv 3 (prefix_difference _ _ _)
theorem original_gaussian_finite_exponential_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 0) (var 1) one ⟶ bounded (tail (var 0) (cutoff (var 1) (var 2)) (var 3))
      one (precisionDenominator (var 2))) := closeUniv 4 (.impI (dyadic_tail_bound _ _ _ _ Prf.hyp0))
theorem original_gaussian_finite_exponential_cutoff_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 0) (var 1) one ⟶ distanceBounded
      (scalarSum (var 0) (lastIndex (var 1) (var 2)+var 3)) (scalarSum (var 0) (lastIndex (var 1) (var 2)))
      one (precisionDenominator (var 2))) := closeUniv 4 (.impI (scalar_cutoff_distance _ _ _ _ Prf.hyp0))
theorem actual_scalar_exponential_cutoff_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (cutoff (var 0) (var 1))) := closeUniv 2 (cutoff_positive _ _)
theorem actual_scalar_exponential_tail_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_scalar_exponential_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 0) (var 1) one ⟶ bounded (fstT (run (var 0) (var 1) (var 2) (var 3))) one
      (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))) :=
  closeUniv 4 (.impI (returned_tail_bound _ _ _ _ Prf.hyp0))
theorem actual_returned_scalar_exponential_cutoff_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 0) (var 1) one ⟶ distanceBounded
      (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))))
      one (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))) :=
  closeUniv 4 (.impI (returned_distance _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalExponentialTail
