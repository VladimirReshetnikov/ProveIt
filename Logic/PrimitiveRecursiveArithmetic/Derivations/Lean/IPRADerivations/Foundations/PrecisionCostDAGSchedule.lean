import IPRADerivations.Foundations.PrecisionCostDAG
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSchedule
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.BoundedSums

/-!
# A derived dyadic schedule for the actual rational dependency DAG

The input graph has numerical size N. Its actual finite sum M of all input
weight numerators bounds every used rational edge multiplier. The sum of
already computed error budgets satisfies Q_(j+1)<=eta+(M+1)Q_j. Genuine QF
induction therefore gives Q_j<=(M+2)^j eta, including N=0 and zero weights.
The actual uniform dyadic schedule s=k+N*binaryLength(M+2) makes this at
most 2^-k. All graph data, sizes, counters and precision demands are internal.
No path-product, amplification, safe-assignment or global-output bound is
supplied. Local analytic estimates of a separate consumer remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.PrecisionCostDAGSchedule

open_ipra exports
open LeanProofs.IPRA.Foundations.PrecisionCostDAG
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add multiply)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numeratorBody : PTm 2 := fstT (safeEntry (var 1) (var 0))
def rowNumerators (G v : PTm n) : PTm n := ap2 (sumF numeratorBody) v (graphRow G v)
def majorantBody : PTm 2 := rowNumerators (var 1) (var 0)
def majorant (G N : PTm n) : PTm n := ap2 (sumF majorantBody) N G
def base (G N : PTm n) : PTm n := majorant G N+two
def amplification (G N : PTm n) : PTm n := pw (base G N) N
def precision (G N k : PTm n) : PTm n := k+N*Analysis.GaussianRootSchedule.binaryLength (base G N)
def unit (k : PTm n) : PTm n := pw two k
def schedule (G N k : PTm n) : PTm n := sequence (var 1) N (precision G N k)
def uniformErrors (N D : PTm n) : PTm n := sequence (var 1) N (pairT one (pred D))
def scheduledErrors (G N k : PTm n) : PTm n := uniformErrors N (unit (precision G N k))
def scheduledBudgets (G N k : PTm n) : PTm n := row G (scheduledErrors G N k) N

def entryBody : PTm 2 := entry (var 1) (var 0)
def prefixValue (r R : PTm n) : PTm n := Analysis.RationalFiniteSum.sum entryBody r R
def total (G Eta r : PTm n) : PTm n := prefixValue r (row G Eta r)

ipra_subst rowNumerators
ipra_subst majorant
ipra_subst base
ipra_subst amplification
ipra_subst precision
ipra_subst unit
ipra_subst schedule
ipra_subst uniformErrors
ipra_subst scheduledErrors
ipra_subst scheduledBudgets
@[simp] theorem subst_prefix {m : ℕ} (σ : Fin n → PTm m) (r R : PTm n) :
    Syn.subst σ (prefixValue r R) = prefixValue (Syn.subst σ r) (Syn.subst σ R) := by simp [prefixValue]
ipra_subst total

theorem numerator_body_at (w R : PTm n) : inst2 numeratorBody w R = fstT (safeEntry R w) := by simp [numeratorBody,inst2]
theorem majorant_body_at (v G : PTm n) : inst2 majorantBody v G = rowNumerators G v := by simp [majorantBody,inst2]
theorem numerator_bound (G N v w : PTm n) (hv : Γ ⊢[PRAAx] lt v N) (hw : Γ ⊢[PRAAx] lt w v) : Γ ⊢[PRAAx]
    le (fstT (weightDatum G v w)) (majorant G N) := by
  have inner := term_le_sum numeratorBody (x := graphRow G v) hw
  have outer := term_le_sum majorantBody (x := G) hv
  exact le_trans
    (by simpa only [numerator_body_at,weightDatum,rowNumerators] using inner)
    (by simpa only [majorant_body_at,majorant,rowNumerators] using outer)

theorem fraction_compare (a A b B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le (a*B) (b*A)) : Γ ⊢[PRAAx] rationalLE (fraction a A) (fraction b B) :=
  Analysis.GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hA hB
    (fraction_represents _ _ hA) (fraction_represents _ _ hB) (le_congr (mul_comm a B) (.eqRefl _) h)

theorem weight_bound (G N v w : PTm n) (hv : Γ ⊢[PRAAx] lt v N) (hw : Γ ⊢[PRAAx] lt w v) : Γ ⊢[PRAAx]
    rationalLE (weight G v w) (fraction (majorant G N) one) := by
  apply fraction_compare _ _ _ _ (zero_lt_succ _) (le_refl _)
  exact le_congr (by ipra_ring) (.eqRefl _) (le_trans (numerator_bound G N v w hv hw)
    (le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (majorant G N) (zero_lt_succ _))))

theorem entry_body_at (w R : PTm n) : Analysis.RationalFiniteSum.term entryBody w R = entry R w := by simp [entryBody,Analysis.RationalFiniteSum.term,inst2]
theorem prefix_ext (r R S : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift r) ⟶ entry (Syn.shift R) (var 0) ≐ entry (Syn.shift S) (var 0))) : Γ ⊢[PRAAx]
    prefixValue r R ≐ prefixValue r S := by
  apply Analysis.RationalFiniteSum.sum_ext
  refine .allI (.impI ?_)
  simpa only [entry_body_at] using rationalEq_of_code (Prf.impE h.allOpen.wk Prf.hyp0)
theorem prefix_succ (r R : PTm n) : Γ ⊢[PRAAx] prefixValue (succ r) R ≐ add (prefixValue r R) (entry R r) := by
  simpa only [entry_body_at,prefixValue] using Analysis.RationalFiniteSum.sum_succ entryBody r R
theorem total_zero (G Eta : PTm n) : Γ ⊢[PRAAx] total G Eta zero ≐ zeroCode := sum_zero_code entryBody _
theorem total_succ (G Eta r : PTm n) : Γ ⊢[PRAAx] total G Eta (succ r) ≐ add (total G Eta r) (node G Eta r) := by
  refine (prefix_succ r (row G Eta (succ r))).eqTrans (Analysis.RationalAlgebra.add_congr ?_ (row_new _ _ _))
  apply prefix_ext
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_row,ConciseIPRA.PTm.subst_succ] using
    row_old (Syn.shift G) (Syn.shift Eta) (Syn.shift r) (var 0) Prf.hyp0

theorem unit_positive (k : PTm n) : Γ ⊢[PRAAx] le one (unit k) :=
  le_trans (zero_lt_succ k) (Analysis.RationalClosure.succ_le_two_pow k)
theorem uniform_error_at (N D v : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    localError (uniformErrors N D) v ≐ fraction one D := by
  have len := MasterCertificate.sequence_length (Γ := Γ) (var 1 : PTm 2) N (pairT one (pred D))
  have guard := safeEntry_present (uniformErrors N D) v (lt_congr (.eqRefl _) len.eqSymm hv)
  have value : Γ ⊢[PRAAx] entry (uniformErrors N D) v ≐ pairT one (pred D) := by
    simpa only [uniformErrors,inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
      MasterCertificate.sequence_decode (var 1 : PTm 2) (x := pairT one (pred D)) hv
  exact (decode_congr (guard.eqTrans value)).eqTrans
    (fraction_congr (fst_pair _ _) ((congrSucc (snd_pair _ _)).eqTrans (Analysis.RationalIntegerNormalization.positive_form hD).eqSymm))


/-- Every actual weighted predecessor sum is controlled by the actual sum
of predecessor budgets. Only the pointwise edge bound and derived
nonnegativity are used. -/
theorem incoming_bound (G Eta N v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    rationalLE (incoming G v (row G Eta v)) (multiply (fraction (majorant G N) one) (total G Eta v)) := by
  let R := row G Eta v
  have sums : Γ ⊢[PRAAx] rationalLE
      (Analysis.RationalFiniteSum.sum weightedBody v (productData G v R))
      (Analysis.RationalSumLinearity.scaledSum entryBody v (fraction (majorant G N) one) R) := by
    apply Analysis.RationalFiniteSum.sum_monotone
    refine .allI (.impI ?_)
    have range : (lt (var 0) (Syn.shift v)) :: Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift v) (Syn.shift N) := by
      simpa only [Fm.shift,subst_lt,Syn.shift] using hv.shift.wk
    let Δ := lt (var 0) (Syn.shift v) :: Γ.map Fm.shift
    have hn : Δ ⊢[PRAAx] rationalLE zeroCode
        (entry (row (Syn.shift G) (Syn.shift Eta) (Syn.shift v)) (var 0)) :=
      rows_nonnegative_at _ _ _ (rows_nonnegative _ _ _) Prf.hyp0
    have native : Δ ⊢[PRAAx] rationalLE
        (multiply (entry (row (Syn.shift G) (Syn.shift Eta) (Syn.shift v)) (var 0))
          (weight (Syn.shift G) (Syn.shift v) (var 0)))
        (multiply (entry (row (Syn.shift G) (Syn.shift Eta) (Syn.shift v)) (var 0))
          (fraction (majorant (Syn.shift G) (Syn.shift N)) one)) := Analysis.RationalArithmetic.multiply_monotone
      (entry (row (Syn.shift G) (Syn.shift Eta) (Syn.shift v)) (var 0))
      (weight (Syn.shift G) (Syn.shift v) (var 0)) (fraction (majorant (Syn.shift G) (Syn.shift N)) one)
      (numerator_nonnegative_of_zero_lower _ hn)
      (weight_bound (Syn.shift G) (Syn.shift N) (Syn.shift v) (var 0) range Prf.hyp0)
    have ordered := Analysis.RationalArgmin.rationalLE_congr
      (Analysis.RationalAlgebra.multiply_commutative _ _) (Analysis.RationalAlgebra.multiply_commutative _ _) native
    have scaled : Δ ⊢[PRAAx]
        Analysis.RationalFiniteSum.term (Analysis.RationalSumLinearity.scaledBody entryBody) (var 0)
          (pairT (fraction (majorant (Syn.shift G) (Syn.shift N)) one)
            (row (Syn.shift G) (Syn.shift Eta) (Syn.shift v))) ≐
        multiply (fraction (majorant (Syn.shift G) (Syn.shift N)) one)
          (entry (row (Syn.shift G) (Syn.shift Eta) (Syn.shift v)) (var 0)) := by
      simpa only [entry_body_at] using Analysis.RationalSumLinearity.scaled_term (Γ := Δ) entryBody (var 0)
        (fraction (majorant (Syn.shift G) (Syn.shift N)) one) (row (Syn.shift G) (Syn.shift Eta) (Syn.shift v))
    have actual := Analysis.RationalArgmin.rationalLE_congr
      (weighted_at (Syn.shift G) (Syn.shift v) (row (Syn.shift G) (Syn.shift Eta) (Syn.shift v)) (var 0)).eqSymm
      scaled.eqSymm ordered
    simpa only [Δ,R,Syn.shift,subst_productData,subst_fraction,subst_majorant,subst_row,subst_pairT,entry_body_at,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using actual
  exact Analysis.RationalArgmin.rationalLE_congr (.eqRefl _)
    (Analysis.RationalSumLinearity.sum_homogeneous entryBody v (fraction (majorant G N) one) R) sums

def errorsBound (Eta N D : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ rationalLE (localError (Syn.shift Eta) (var 0)) (fraction one (Syn.shift D)))
def totalBoundLaw (G Eta N D r : PTm n) : Fm PTm n :=
  le r N ⟶ rationalLE (total G Eta r) (fraction (pw (base G N) r) D)
ipra_subst errorsBound [Syn.subst_shift, Syn.shift_subst]
ipra_subst totalBoundLaw

theorem errors_bound_at (Eta N D v : PTm n) (h : Γ ⊢[PRAAx] errorsBound Eta N D) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    rationalLE (localError Eta v) (fraction one D) := by
  have gate : Γ ⊢[PRAAx] lt v N ⟶ rationalLE (localError Eta v) (fraction one D) := by
    simpa only [errorsBound,Fm.subst_imp,subst_lt,Analysis.RationalArgmin.subst_rationalLE,
      subst_localError,subst_fraction,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE v
  exact .impE gate hv

theorem base_positive (G N : PTm n) : Γ ⊢[PRAAx] le one (base G N) :=
  le_of_eq_add (d := majorant G N+one) (by unfold base; ipra_ring)
theorem growth_step (m r : PTm n) : Γ ⊢[PRAAx]
    le (pw (m+two) r+(one+m*pw (m+two) r)) (pw (m+two) (succ r)) := by
  have hp := Analysis.GaussianFactorBudget.power_positive (Γ := Γ) (m+two) r
    (le_of_eq_add (d := m+one) (by ipra_ring))
  have rough : Γ ⊢[PRAAx] le (pw (m+two) r+(one+m*pw (m+two) r)) (pw (m+two) r*(m+two)) := by
    ipra_le sl hp
  exact le_congr (.eqRefl _) (pw_succ (m+two) r).eqSymm rough

theorem node_bound_step (G Eta N D r : PTm n) (hr : Γ ⊢[PRAAx] lt r N)
    (_hD : Γ ⊢[PRAAx] le one D) (hEta : Γ ⊢[PRAAx] rationalLE (localError Eta r) (fraction one D))
    (hPrevious : Γ ⊢[PRAAx] rationalLE (total G Eta r) (fraction (pw (base G N) r) D)) : Γ ⊢[PRAAx]
    rationalLE (node G Eta r)
      (add (fraction one D) (multiply (fraction (majorant G N) one) (fraction (pw (base G N) r) D))) := by
  have scaled := Analysis.GaussianWeightedErrorBudget.natural_scale_monotone (majorant G N) _ _ hPrevious
  exact Analysis.GaussianRationalSyntheticBounds.add_monotone _ _ _ _ hEta
    (Analysis.RationalArgmin.transitive (incoming_bound G Eta N r hr) scaled)

theorem total_bound_step (G Eta N D r : PTm n) (hr : Γ ⊢[PRAAx] lt r N)
    (hD : Γ ⊢[PRAAx] le one D) (hEta : Γ ⊢[PRAAx] rationalLE (localError Eta r) (fraction one D))
    (hPrevious : Γ ⊢[PRAAx] rationalLE (total G Eta r) (fraction (pw (base G N) r) D)) : Γ ⊢[PRAAx]
    rationalLE (total G Eta (succ r)) (fraction (pw (base G N) (succ r)) D) := by
  have localBudget := node_bound_step G Eta N D r hr hD hEta hPrevious
  have sum := Analysis.GaussianRationalSyntheticBounds.add_monotone _ _ _ _ hPrevious localBudget
  have combinedCode : Γ ⊢[PRAAx]
      add (fraction (pw (base G N) r) D)
        (add (fraction one D) (multiply (fraction (majorant G N) one) (fraction (pw (base G N) r) D))) ≐
      fraction (pw (base G N) r+(one+majorant G N*pw (base G N) r)) D :=
    (Analysis.RationalAlgebra.add_congr (.eqRefl _)
      ((Analysis.RationalAlgebra.add_congr (.eqRefl _) (fraction_scale _ _ _ hD)).eqTrans (fraction_add _ _ _ hD))).eqTrans
      (fraction_add _ _ _ hD)
  have bound := Analysis.RationalArgmin.rationalLE_congr (total_succ G Eta r).eqSymm combinedCode sum
  exact Analysis.RationalArgmin.transitive bound (fraction_order _ _ D hD (growth_step (majorant G N) r))

/-- The only quantitative induction is QF, guarded by the actual graph size.
The local-error premise controls each original eta separately, not this
conclusion or an incoming global budget recurrence. -/
theorem total_bound (G Eta N D r : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hEta : Γ ⊢[PRAAx] errorsBound Eta N D) (hr : Γ ⊢[PRAAx] le r N) : Γ ⊢[PRAAx]
    rationalLE (total G Eta r) (fraction (pw (base G N) r) D) := by
  have ds := Order.shift_one_le hD
  have es : Γ.map Fm.shift ⊢[PRAAx] errorsBound (Syn.shift Eta) (Syn.shift N) (Syn.shift D) := by
    simpa only [Fm.shift, subst_errorsBound, Syn.shift] using hEta.shift
  let P : Fm PTm (n + 1) := rationalLE (total (Syn.shift G) (Syn.shift Eta) (var 0))
    (fraction (pw (base (Syn.shift G) (Syn.shift N)) (var 0)) (Syn.shift D))
  have atIndex : Γ ⊢[PRAAx] P.subst (Syn.inst r) := by
    refine qfIndAtMost hr (le_QF _ _) ?_ ?_
    · simp only [P, Analysis.RationalArgmin.subst_rationalLE, subst_total, subst_fraction,
        subst_base, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact Analysis.RationalArgmin.rationalLE_congr (total_zero G Eta).eqSymm (.eqRefl _)
        (fraction_nonnegative _ D hD)
    · simp only [P, Analysis.RationalArgmin.subst_rationalLE, subst_total, subst_fraction,
        subst_base, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact .impI (total_bound_step (Syn.shift G) (Syn.shift Eta) (Syn.shift N) (Syn.shift D) (var 0)
        Prf.hyp0 ds.wk.wk (errors_bound_at _ _ _ _ es.wk.wk Prf.hyp0) Prf.hyp1)
  simpa only [P, Analysis.RationalArgmin.subst_rationalLE, subst_total, subst_fraction,
    subst_base, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using atIndex

/-- The actual uniform local-error list meets the local hypotheses, without
an input assertion about that list or its values. -/
theorem uniform_errors_bound (N D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    errorsBound (uniformErrors N D) N D := by
  refine .allI (.impI ?_)
  have ds : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) :=
    (Order.shift_one_le hD).wk
  have actual := uniform_error_at (Syn.shift N) (Syn.shift D) (var 0) ds Prf.hyp0
  simpa only [Syn.shift,subst_uniformErrors] using
    Analysis.RationalArgmin.rationalLE_congr actual.eqSymm (.eqRefl _) (Analysis.RationalArgmin.reflexive _)

theorem node_bound (G Eta N D v : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hEta : Γ ⊢[PRAAx] errorsBound Eta N D) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    rationalLE (node G Eta v) (fraction (amplification G N) D) := by
  have localBudget := node_bound_step G Eta N D v hv hD (errors_bound_at _ _ _ _ hEta hv)
    (total_bound G Eta N D v hD hEta (le_of_lt hv))
  have code : Γ ⊢[PRAAx]
      add (fraction one D) (multiply (fraction (majorant G N) one) (fraction (pw (base G N) v) D)) ≐
      fraction (one+majorant G N*pw (base G N) v) D :=
    (Analysis.RationalAlgebra.add_congr (.eqRefl _) (fraction_scale _ _ _ hD)).eqTrans (fraction_add _ _ _ hD)
  have first := Analysis.RationalArgmin.rationalLE_congr (.eqRefl _) code localBudget
  have grow : Γ ⊢[PRAAx] le (one+majorant G N*pw (base G N) v) (pw (base G N) (succ v)) := by
    have g := growth_step (Γ := Γ) (majorant G N) v
    exact le_trans (le_add_left _ _) g
  have last := Analysis.GaussianFactorBudget.power_monotone_length (base G N) (succ v) N (base_positive _ _) hv
  exact Analysis.RationalArgmin.transitive first (fraction_order _ _ _ hD (le_trans grow last))

/-- Binary-length arithmetic proves the actual dyadic amplification budget. -/
theorem amplification_budget (G N k : PTm n) : Γ ⊢[PRAAx]
    le (amplification G N*unit k) (unit (precision G N k)) := by
  have bits := (Analysis.GaussianRootSchedule.binary_length_correct (Γ := Γ) (base G N)).andE₁
  have powers := pw_le_pw N bits
  have powerCode : Γ ⊢[PRAAx]
      pw (pw two (Analysis.GaussianRootSchedule.binaryLength (base G N))) N ≐
      pw two (N*Analysis.GaussianRootSchedule.binaryLength (base G N)) :=
    (Analysis.GaussianDescentClockArithmetic.power_composition _ _ _).eqTrans
      (congrAp2 powF (mul_comm _ _) (.eqRefl _))
  have h := mul_le_mul_right (unit k) (le_congr (.eqRefl _) powerCode powers)
  exact le_congr (.eqRefl _)
    ((mul_comm _ _).eqTrans (pw_add two k (N*Analysis.GaussianRootSchedule.binaryLength (base G N))).eqSymm) h

theorem amplification_fraction_bound (G N k : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fraction (amplification G N) (unit (precision G N k))) (fraction one (unit k)) :=
  fraction_compare _ _ _ _ (unit_positive _) (unit_positive _)
    (le_congr (.eqRefl _) (by ipra_ring) (amplification_budget G N k))

theorem schedule_length (G N k : PTm n) : Γ ⊢[PRAAx] length (schedule G N k) ≐ N :=
  MasterCertificate.sequence_length _ _ _
theorem schedule_lookup (G N k v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    entry (schedule G N k) v ≐ precision G N k := by
  simpa only [schedule,inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    MasterCertificate.sequence_decode (var 1 : PTm 2) (x := precision G N k) hv

theorem scheduled_error_at (G N k v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    localError (scheduledErrors G N k) v ≐ fraction one (unit (entry (schedule G N k) v)) :=
  (uniform_error_at N _ v (unit_positive _) hv).eqTrans
    (fraction_congr (.eqRefl _) (congrAp2 powF (schedule_lookup G N k v hv).eqSymm (.eqRefl _)))

/-- The requested final error is obtained from the original numerical graph
alone, by executing the computed precision schedule and budget recursion. -/
theorem scheduled_total_bound (G N k : PTm n) : Γ ⊢[PRAAx]
    rationalLE (total G (scheduledErrors G N k) N) (fraction one (unit k)) :=
  Analysis.RationalArgmin.transitive
    (total_bound G _ N _ N (unit_positive _) (uniform_errors_bound N _ (unit_positive _)) (le_refl _))
    (amplification_fraction_bound G N k)

theorem scheduled_node_bound (G N k v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    rationalLE (node G (scheduledErrors G N k) v) (fraction one (unit k)) :=
  Analysis.RationalArgmin.transitive
    (node_bound G _ N _ v (unit_positive _) (uniform_errors_bound N _ (unit_positive _)) hv)
    (amplification_fraction_bound G N k)

theorem scheduled_budget_bound (G N k v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    rationalLE (entry (scheduledBudgets G N k) v) (fraction one (unit k)) :=
  Analysis.RationalArgmin.rationalLE_congr (row_lookup G (scheduledErrors G N k) N v hv).eqSymm (.eqRefl _)
    (scheduled_node_bound G N k v hv)

theorem scheduled_budget_nonnegative (G N k v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    rationalLE zeroCode (entry (scheduledBudgets G N k) v) :=
  rows_nonnegative_at N _ v (rows_nonnegative G (scheduledErrors G N k) N) hv

/-- A fixed PR3 returns the actual schedule, budgets, precision and weight
majorant. Its parameters are the graph, node count and requested precision. -/
def output (G N k : PTm n) : PTm n := pairT (schedule G N k)
  (pairT (scheduledBudgets G N k) (pairT (precision G N k) (majorant G N)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (G N k : PTm n) : PTm n := ap3 outputF G N k
ipra_subst output
ipra_subst run

theorem program_at (G N k : PTm n) : Γ ⊢[PRAAx] run G N k ≐ output G N k := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![G,N,k]
theorem returned_schedule (G N k : PTm n) : Γ ⊢[PRAAx] fstT (run G N k) ≐ schedule G N k :=
  (congrFst (program_at G N k)).eqTrans (fst_pair _ _)
theorem returned_budgets (G N k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run G N k)) ≐ scheduledBudgets G N k :=
  (congrFst ((congrSnd (program_at G N k)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_precision (G N k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run G N k))) ≐ precision G N k :=
  (congrFst ((congrSnd ((congrSnd (program_at G N k)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_majorant (G N k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run G N k))) ≐ majorant G N :=
  (congrSnd ((congrSnd ((congrSnd (program_at G N k)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_budget_bound (G N k v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    rationalLE (entry (fstT (sndT (run G N k))) v) (fraction one (unit k)) :=
  Analysis.RationalArgmin.rationalLE_congr (entry_congr (returned_budgets G N k).eqSymm (.eqRefl _)) (.eqRefl _)
    (scheduled_budget_bound G N k v hv)

theorem actual_safe_schedule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ rationalLE
      (entry (scheduledBudgets (var 0) (var 1) (var 2)) (var 3)) (fraction one (unit (var 2)))) :=
  closeUniv 4 (.impI (scheduled_budget_bound _ _ _ _ Prf.hyp0))
theorem actual_total_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rationalLE (total (var 0) (scheduledErrors (var 0) (var 1) (var 2)) (var 1)) (fraction one (unit (var 2)))) :=
  closeUniv 3 (scheduled_total_bound _ _ _)
theorem actual_precision_assignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ entry (schedule (var 0) (var 1) (var 2)) (var 3) ≐ precision (var 0) (var 1) (var 2)) :=
  closeUniv 4 (.impI (schedule_lookup _ _ _ _ Prf.hyp0))
theorem actual_local_error_assignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ localError (scheduledErrors (var 0) (var 1) (var 2)) (var 3) ≐
      fraction one (unit (entry (schedule (var 0) (var 1) (var 2)) (var 3)))) :=
  closeUniv 4 (.impI (scheduled_error_at _ _ _ _ Prf.hyp0))
theorem actual_amplification_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (amplification (var 0) (var 1)*unit (var 2)) (unit (precision (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (amplification_budget _ _ _)
theorem actual_schedule_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run (var 0) (var 1) (var 2)) ≐ schedule (var 0) (var 1) (var 2)) ⋏
      ((fstT (sndT (run (var 0) (var 1) (var 2))) ≐ scheduledBudgets (var 0) (var 1) (var 2)) ⋏
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ precision (var 0) (var 1) (var 2)) ⋏
          (sndT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ majorant (var 0) (var 1))))) :=
  closeUniv 3 (.andI (returned_schedule _ _ _) (.andI (returned_budgets _ _ _)
    (.andI (returned_precision _ _ _) (returned_majorant _ _ _))))
theorem actual_returned_safe_schedule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ rationalLE
      (entry (fstT (sndT (run (var 0) (var 1) (var 2)))) (var 3)) (fraction one (unit (var 2)))) :=
  closeUniv 4 (.impI (returned_budget_bound _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Foundations.PrecisionCostDAGSchedule
