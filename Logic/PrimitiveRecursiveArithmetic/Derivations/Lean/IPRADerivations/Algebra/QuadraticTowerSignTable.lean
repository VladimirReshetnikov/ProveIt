import IPRADerivations.Algebra.QuadraticTowerSignRecipe
import IPRADerivations.Algebra.QuadraticTowerOperandProperness

/-!
# Actual numerical-depth recursive sign tables

The original section2.3 sign recipe is scheduled by the SAME explicit
backward budget as multiplication. Actual sequence constructors store
ground tags and successor recipe outputs. All stored tags are bounded
unconditionally, and original operand heights give the exact normalized
successor equation of the actual query. This constructs the sign program;
its ordered-extension correctness and independent-cap coherence remain
separate proof gates.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerSignTable

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width)
open QuadraticTowerArrayCodec (arrayHeight horizon code decoded)
open QuadraticTowerMultiplicationTable (budget demandF)
open LeanProofs.IPRA.Foundations
open MasterCertificate (sequence entry sequence_length sequence_decode)
open SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def groundTag (q : PTm n) : PTm n := rem (QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf q)) (succ two)
def baseRow (B i : PTm n) : PTm n := groundTag
  (QuadraticTowerArrayCodec.digit (QuadraticTowerScalarBudget.codeCap B) i zero)
def baseBody : PTm 2 := baseRow (var 1) (var 0)
def base (B : PTm n) : PTm n := sequence baseBody (horizon zero B) B
def rowValue (h B S D i : PTm n) : PTm n := QuadraticTowerSignRecipe.recipe h B D S
  (decoded (width (succ h)) (QuadraticTowerScalarBudget.codeCap B) i)
def rowBody : PTm 2 := rowValue (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def step (h B S D : PTm n) : PTm n := sequence rowBody (horizon (succ h) B)
  (QuadraticTowerMultiplicationTable.rowData h B S D)
def baseSchema : PTm 2 := base (var 0)
def stepSchema : PTm 4 := step (var 0) (var 1) (var 2) (var 3)
def table (h B D : PTm n) : PTm n := DemandRecursion.X demandF baseSchema stepSchema h B D
def query (h B D A : PTm n) : PTm n := QuadraticTowerSignRecipe.read h B (table h B D) A

ipra_subst groundTag
ipra_subst baseRow
ipra_subst base
ipra_subst rowValue
ipra_subst step
ipra_subst table [DemandRecursion.X, DemandRecursion.subst_V]
ipra_subst query

theorem ground_tag_bound (q : PTm n) : Γ ⊢[PRAAx] lt (groundTag q) (succ two) :=
  .andE₂ (RuntimeWordAppend.divide_spec _ _ (zero_lt_succ two))
theorem ground_tag_exact (q : PTm n)
    (hq : Γ ⊢[PRAAx] lt (QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf q)) (succ two)) : Γ ⊢[PRAAx]
    groundTag q ≐ QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf q) :=
  RuntimeWordAppend.remainder_small _ _ (zero_lt_succ two) hq

theorem native_tag_bound (a : ZT n) : Γ ⊢[PRAAx] lt (QuadraticSignCertificates.tag a) (succ two) := by
  refine .orE (QuadraticSignCertificates.parts_disjoint a) ?_ ?_
  · refine .orE (zero_or_succ (QuadraticSignCertificates.negativePart a)) ?_ ?_
    · exact lt_congr (QuadraticSignCertificates.tag_zero a Prf.hyp1 Prf.hyp0).eqSymm (.eqRefl _) (zero_lt_succ two)
    · exact lt_congr (QuadraticSignCertificates.tag_negative a Prf.hyp1 Prf.hyp0).eqSymm (.eqRefl _) (le_refl _)
  · refine .orE (zero_or_succ (QuadraticSignCertificates.positivePart a)) ?_ ?_
    · exact lt_congr (QuadraticSignCertificates.tag_zero a Prf.hyp0 Prf.hyp1).eqSymm (.eqRefl _) (zero_lt_succ two)
    · exact lt_congr (QuadraticSignCertificates.tag_positive a Prf.hyp0 Prf.hyp1).eqSymm (.eqRefl _) (le_succ_self two)

theorem ground_tag_native (q : PTm n) : Γ ⊢[PRAAx]
    groundTag q ≐ QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf q) :=
  ground_tag_exact q (native_tag_bound _)

theorem table_zero (B D : PTm n) : Γ ⊢[PRAAx] table zero B D ≐ base B := by
  simpa only [table,baseSchema,subst_base,inst2,Syn.subst_var,Matrix.cons_val_zero] using
    DemandRecursion.demand_zero (Γ := Γ) demandF baseSchema stepSchema B D
theorem table_succ (h B D : PTm n) : Γ ⊢[PRAAx]
    table (succ h) B D ≐ step h B (table h (budget h B D) D) D := by
  simpa only [table,budget,DemandRecursion.appF,stepSchema,subst_step,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using
      DemandRecursion.demand_succ (Γ := Γ) demandF baseSchema stepSchema h B D

theorem table_congr {h h' B B' D D' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hb : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] D ≐ D') : Γ ⊢[PRAAx] table h B D ≐ table h' B' D' := by
  ipra_congr (table (var 0) (var 1) (var 2) : PTm 3) with [hh, hb, hd]
theorem row_value_congr {h h' B B' S S' D D' i i' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hb : Γ ⊢[PRAAx] B ≐ B') (hs : Γ ⊢[PRAAx] S ≐ S') (hd : Γ ⊢[PRAAx] D ≐ D') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] rowValue h B S D i ≐ rowValue h' B' S' D' i' := by
  ipra_congr (rowValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hh, hb, hs, hd, hi]

theorem base_body_at (B i : PTm n) : inst2 baseBody i B = baseRow B i := by simp [baseBody,inst2]
theorem row_body_at (h B S D i : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody i (QuadraticTowerMultiplicationTable.rowData h B S D) ≐ rowValue h B S D i := by
  simp only [rowBody,inst2,subst_rowValue,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have hp := snd_pair (Γ := Γ) h (pairT B (pairT S D))
  have hq := (congrSnd hp).eqTrans (snd_pair B (pairT S D))
  exact row_value_congr (fst_pair _ _) hp.fstE
    hq.fstE hq.sndE (.eqRefl _)

theorem base_lookup (B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (horizon zero B)) : Γ ⊢[PRAAx]
    entry (base B) i ≐ baseRow B i := by
  simpa only [base,base_body_at] using sequence_decode (Γ := Γ) baseBody (x := B) hi
theorem step_lookup (h B S D i : PTm n) (hi : Γ ⊢[PRAAx] lt i (horizon (succ h) B)) : Γ ⊢[PRAAx]
    entry (step h B S D) i ≐ rowValue h B S D i :=
  (sequence_decode rowBody hi).eqTrans (row_body_at _ _ _ _ _)

theorem base_entry_bound (B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (horizon zero B)) : Γ ⊢[PRAAx]
    lt (entry (base B) i) (succ two) :=
  lt_congr (base_lookup B i hi).eqSymm (.eqRefl _) (ground_tag_bound _)
theorem step_entry_bound (h B S D i : PTm n) (hi : Γ ⊢[PRAAx] lt i (horizon (succ h) B)) : Γ ⊢[PRAAx]
    lt (entry (step h B S D) i) (succ two) :=
  lt_congr (step_lookup h B S D i hi).eqSymm (.eqRefl _) (QuadraticTowerSignRecipe.recipe_bound _ _ _ _ _)

theorem horizon_congr {h h' B B' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h') (hb : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx]
    horizon h B ≐ horizon h' B' := by
  ipra_congr (horizon (var 0) (var 1) : PTm 2) with [hh, hb]

theorem table_length (h B D : PTm n) : Γ ⊢[PRAAx] length (table h B D) ≐ horizon h B := by
  refine .orE (zero_or_succ h) ?_ ?_
  · exact (congrFst ((table_congr Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans (table_zero B D))).eqTrans
      ((sequence_length _ _ _).eqTrans (horizon_congr Prf.hyp0.eqSymm (.eqRefl _)))
  · exact (congrFst ((table_congr Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans (table_succ _ B D))).eqTrans
      ((sequence_length _ _ _).eqTrans (horizon_congr Prf.hyp0.eqSymm (.eqRefl _)))

theorem table_entry_bound (h B D i : PTm n) (hi : Γ ⊢[PRAAx] lt i (horizon h B)) : Γ ⊢[PRAAx]
    lt (entry (table h B D) i) (succ two) := by
  refine .orE (zero_or_succ h) ?_ ?_
  · have hh : ((h ≐ zero) :: Γ) ⊢[PRAAx] h ≐ zero := Prf.hyp0
    have range : ((h ≐ zero) :: Γ) ⊢[PRAAx] lt i (horizon zero B) :=
      lt_congr (.eqRefl _) (horizon_congr hh (.eqRefl B)) hi.wk
    have stored : ((h ≐ zero) :: Γ) ⊢[PRAAx] entry (table h B D) i ≐ entry (base B) i :=
      entry_congr ((table_congr hh (.eqRefl B) (.eqRefl D)).eqTrans (table_zero B D)) (.eqRefl i)
    exact lt_congr stored.eqSymm (.eqRefl _) (base_entry_bound B i range)
  · have hh : ((h ≐ succ (PTm.pred h)) :: Γ) ⊢[PRAAx] h ≐ succ (PTm.pred h) := Prf.hyp0
    have range : ((h ≐ succ (PTm.pred h)) :: Γ) ⊢[PRAAx] lt i (horizon (succ (PTm.pred h)) B) :=
      lt_congr (.eqRefl _) (horizon_congr hh (.eqRefl B)) hi.wk
    have stored : ((h ≐ succ (PTm.pred h)) :: Γ) ⊢[PRAAx]
        entry (table h B D) i ≐ entry (step (PTm.pred h) B (table (PTm.pred h) (budget (PTm.pred h) B D) D) D) i :=
      entry_congr ((table_congr hh (.eqRefl B) (.eqRefl D)).eqTrans (table_succ _ B D)) (.eqRefl i)
    exact lt_congr stored.eqSymm (.eqRefl _) (step_entry_bound _ B _ D i range)

theorem query_bound (h B D A : PTm n) : Γ ⊢[PRAAx] lt (query h B D A) (succ two) :=
  QuadraticTowerSignRecipe.read_bound _ _ _ _

theorem query_exact (h B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B) : Γ ⊢[PRAAx]
    query h B D A ≐ entry (table h B D) (code h A B) :=
  QuadraticTowerSignRecipe.read_exact _ _ _ _
    (table_entry_bound h B D (code h A B) (QuadraticTowerArrayCodec.code_bound h A B ha))

theorem ground_tag_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] groundTag a ≐ groundTag b := by
  ipra_congr (groundTag (var 0) : PTm 1) with [h]

theorem ground_tag_from_projection (q : PTm n) : Γ ⊢[PRAAx]
    QuadraticRationalZeroProjection.sign (pairT q zero) ≐ groundTag q :=
  (ground_tag_native (fstT (pairT q zero))).eqSymm.eqTrans (ground_tag_congr (fst_pair _ _))

theorem ground_tag_proper (q r : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalEq q r) : Γ ⊢[PRAAx]
    groundTag q ≐ groundTag r :=
  (ground_tag_from_projection q).eqSymm.eqTrans
    ((QuadraticRationalZeroProjection.sign_congr _ _
      (QuadraticRationalZeroProjection.equivalent_of_projection _ _
        (RationalArgmin.rationalEq_congr (fst_pair q zero).eqSymm (fst_pair r zero).eqSymm h))).eqTrans
      (ground_tag_from_projection r))

theorem recipe_operand_congr (h B D S A E : PTm n) (ha : Γ ⊢[PRAAx] A ≐ E) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.recipe h B D S A ≐ QuadraticTowerSignRecipe.recipe h B D S E := by
  ipra_congr (QuadraticTowerSignRecipe.recipe (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl h, .eqRefl B, .eqRefl D, .eqRefl S, ha]

theorem query_zero (B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight zero A B) : Γ ⊢[PRAAx]
    query zero B D A ≐ groundTag (RationalArithmetic.recode (entry A zero)) :=
  (query_exact zero B D A ha).eqTrans
    ((entry_congr (table_zero B D) (.eqRefl _)).eqTrans
      ((base_lookup B _ (QuadraticTowerArrayCodec.code_bound zero A B ha)).eqTrans
        (ground_tag_congr (QuadraticTowerOperandProperness.ground_digit A B ha))))

theorem query_zero_original (B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight zero A B) : Γ ⊢[PRAAx]
    query zero B D A ≐ QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf (entry A zero)) :=
  (query_zero B D A ha).eqTrans
    ((ground_tag_proper _ _ (RationalArithmetic.recode_equal _)).eqTrans (ground_tag_native _))

theorem query_succ (h B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) : Γ ⊢[PRAAx]
    query (succ h) B D A ≐ QuadraticTowerSignRecipe.recipe h B D (table h (budget h B D) D)
      (QuadraticTowerArrayCodec.normalized (succ h) A) :=
  (query_exact (succ h) B D A ha).eqTrans
    ((entry_congr (table_succ h B D) (.eqRefl _)).eqTrans
      ((step_lookup h B _ D _ (QuadraticTowerArrayCodec.code_bound (succ h) A B ha)).eqTrans
        (recipe_operand_congr _ _ _ _ _ _ (QuadraticTowerArrayNormalization.restored_normalized _ _ _ ha))))

theorem successor_third_address (h B D A : PTm n)
    (hD : Γ ⊢[PRAAx] QuadraticTowerMultiplicationHeight.radicandsHeight D (succ h) B)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) : Γ ⊢[PRAAx]
    lt (code h (QuadraticTowerSignRecipe.thirdInput h B D (table h (budget h B D) D)
      (QuadraticTowerArrayCodec.normalized (succ h) A)) (budget h B D)) (horizon h (budget h B D)) := by
  have hn := QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _)
    (QuadraticTowerArrayNormalization.restored_normalized _ _ _ ha) (.eqRefl _)
      (QuadraticTowerMultiplicationHeight.restored_height _ _ _ _ ha (le_refl B))
  exact QuadraticTowerArrayCodec.code_bound _ _ _
    (QuadraticTowerSignRecipe.third_input_fits _ _ _ _ _ B (le_refl B) hD hn)

def tableF : PR 3 := PTm.toPR (table (var 0) (var 1) (var 2))
def queryF : PR 4 := PTm.toPR (query (var 0) (var 1) (var 2) (var 3))
def output (h B D A : PTm n) : PTm n := pairT (query h B D A) (pairT (table h B D) (horizon h B))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (h B D A : PTm n) : PTm n := PTm.app outputF ![h,B,D,A]
ipra_subst output
ipra_subst run

theorem table_program_at (h B D : PTm n) : Γ ⊢[PRAAx] ap3 tableF h B D ≐ table h B D := by
  simpa [tableF,ap3] using toPR_eq (Γ := Γ) (table (var 0) (var 1) (var 2) : PTm 3) ![h,B,D]
theorem query_program_at (h B D A : PTm n) : Γ ⊢[PRAAx] PTm.app queryF ![h,B,D,A] ≐ query h B D A := by
  simpa [queryF] using toPR_eq (Γ := Γ) (query (var 0) (var 1) (var 2) (var 3) : PTm 4) ![h,B,D,A]
theorem program_at (h B D A : PTm n) : Γ ⊢[PRAAx] run h B D A ≐ output h B D A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![h,B,D,A]
theorem returned_tag (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A) ≐ query h B D A :=
  (program_at _ _ _ _).fstE
theorem returned_tail (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A) ≐ pairT (table h B D) (horizon h B) :=
  (program_at _ _ _ _).sndE
theorem returned_table (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A)) ≐ table h B D :=
  (returned_tail _ _ _ _).fstE
theorem returned_horizon (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A)) ≐ horizon h B :=
  (returned_tail _ _ _ _).sndE
theorem returned_bound (h B D A : PTm n) : Γ ⊢[PRAAx] lt (fstT (run h B D A)) (succ two) :=
  lt_congr (returned_tag _ _ _ _).eqSymm (.eqRefl _) (query_bound _ _ _ _)
theorem returned_length (h B D A : PTm n) : Γ ⊢[PRAAx]
    length (fstT (sndT (run h B D A))) ≐ sndT (sndT (run h B D A)) :=
  (congrFst (returned_table _ _ _ _)).eqTrans ((table_length _ _ _).eqTrans (returned_horizon _ _ _ _).eqSymm)

theorem actual_sign_changed_budget_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (table (succ (var 0)) (var 1) (var 2) ≐ step (var 0) (var 1)
      (table (var 0) (budget (var 0) (var 1) (var 2)) (var 2)) (var 2)) := closeUniv 3 (table_succ _ _ _)
theorem actual_sign_table_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (table (var 0) (var 1) (var 2)) ≐ horizon (var 0) (var 1)) := closeUniv 3 (table_length _ _ _)
theorem actual_stored_sign_tag_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (horizon (var 0) (var 1)) ⟶ lt (entry (table (var 0) (var 1) (var 2)) (var 3)) (succ two)) :=
  closeUniv 4 (.impI (table_entry_bound _ _ _ _ Prf.hyp0))
theorem actual_recursive_sign_query_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (query (var 0) (var 1) (var 2) (var 3)) (succ two)) := closeUniv 4 (query_bound _ _ _ _)
theorem actual_recursive_sign_ground_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (arrayHeight zero (var 2) (var 0) ⟶ query zero (var 0) (var 1) (var 2) ≐
      QuadraticSignCertificates.tag (RationalSupMetric.numeratorOf (entry (var 2) zero))) :=
  closeUniv 3 (.impI (query_zero_original _ _ _ Prf.hyp0))
theorem actual_recursive_sign_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight (succ (var 0)) (var 3) (var 1) ⟶ query (succ (var 0)) (var 1) (var 2) (var 3) ≐
      QuadraticTowerSignRecipe.recipe (var 0) (var 1) (var 2)
        (table (var 0) (budget (var 0) (var 1) (var 2)) (var 2)) (QuadraticTowerArrayCodec.normalized (succ (var 0)) (var 3))) :=
  closeUniv 4 (.impI (query_succ _ _ _ _ Prf.hyp0))
theorem actual_recursive_sign_third_address_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (QuadraticTowerMultiplicationHeight.radicandsHeight (var 2) (succ (var 0)) (var 1) ⟶
      arrayHeight (succ (var 0)) (var 3) (var 1) ⟶
        lt (code (var 0) (QuadraticTowerSignRecipe.thirdInput (var 0) (var 1) (var 2)
          (table (var 0) (budget (var 0) (var 1) (var 2)) (var 2)) (QuadraticTowerArrayCodec.normalized (succ (var 0)) (var 3)))
          (budget (var 0) (var 1) (var 2))) (horizon (var 0) (budget (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (.impI (successor_third_address _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_sign_table_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 tableF (var 0) (var 1) (var 2) ≐ table (var 0) (var 1) (var 2)) := closeUniv 3 (table_program_at _ _ _)
theorem actual_sign_query_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app queryF ![var 0,var 1,var 2,var 3] ≐ query (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (query_program_at _ _ _ _)
theorem actual_sign_scheduler_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_sign_scheduler_returned_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (fstT (run (var 0) (var 1) (var 2) (var 3))) (succ two) ⋏
      length (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.andI (returned_bound _ _ _ _) (returned_length _ _ _ _))

end LeanProofs.IPRA.Algebra.QuadraticTowerSignTable
