import IPRADerivations.Algebra.QuadraticTowerArrayCodec
import IPRADerivations.Algebra.QuadraticTowerCoefficientArithmetic
import IPRADerivations.Foundations.DemandRecursion
import IPRADerivations.Foundations.RuntimeWordAppend

/-!
# The actual changed-budget five-call multiplication table

An ordinary PR demand construction stores all pairs of finite scalar words.
The next row performs the source's five lower-table queries, including the
query whose operand is the actual preceding be result. The equations below
bind this genuine program to its literal recipe. They do not yet prove that
the computed be operand fits the lower table: that range/result-height
induction remains necessary before this is a full tower multiplication.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationTable

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width singleton)
open QuadraticTowerScalarBudget (codeCap majorant)
open LeanProofs.IPRA.Foundations
open MasterCertificate (sequence entry sequence_length sequence_decode)
open SequenceComposition (length append entry_congr)
open RealizerComposition (slice)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sourceCost (h : PTm n) : PTm n := PTm.num 1000*pw (PTm.num 8) (succ h)
def demandBody : PTm 3 := majorant (sourceCost (succ (var 0))) (var 1)
def demandF : PR 3 := PTm.toPR demandBody
def budget (h B D : PTm n) : PTm n := ap3 demandF h B D
def rows (h B : PTm n) : PTm n := QuadraticTowerArrayCodec.horizon h B*QuadraticTowerArrayCodec.horizon h B
def address (h B A C : PTm n) : PTm n :=
  QuadraticTowerArrayCodec.code h A B*QuadraticTowerArrayCodec.horizon h B+QuadraticTowerArrayCodec.code h C B
def lookup (h B T A C : PTm n) : PTm n := entry T (address h B A C)
def leftHalf (h A : PTm n) : PTm n := slice A zero (width h)
def rightHalf (h A : PTm n) : PTm n := slice A (width h) (width h)

def recipe (h B T D A C : PTm n) : PTm n :=
  let b := budget h B D
  let ac := lookup h b T (leftHalf h A) (leftHalf h C)
  let be := lookup h b T (rightHalf h A) (rightHalf h C)
  let bed := lookup h b T be (entry D h)
  let ae := lookup h b T (leftHalf h A) (rightHalf h C)
  let bc := lookup h b T (rightHalf h A) (leftHalf h C)
  append (QuadraticTowerCoefficientArithmetic.added h ac bed)
    (QuadraticTowerCoefficientArithmetic.added h ae bc)

def rowValue (h B T D i : PTm n) : PTm n := recipe h B T D
  (QuadraticTowerArrayCodec.decoded (width (succ h)) (codeCap B)
    (quo i (QuadraticTowerArrayCodec.horizon (succ h) B)))
  (QuadraticTowerArrayCodec.decoded (width (succ h)) (codeCap B)
    (rem i (QuadraticTowerArrayCodec.horizon (succ h) B)))
def rowData (h B T D : PTm n) : PTm n := pairT h (pairT B (pairT T D))
def rowBody : PTm 2 := rowValue (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def step (h B T D : PTm n) : PTm n := sequence rowBody (rows (succ h) B) (rowData h B T D)
def baseRow (B i : PTm n) : PTm n := singleton (RationalArithmetic.multiply
  (QuadraticTowerArrayCodec.digit (codeCap B) (quo i (QuadraticTowerArrayCodec.horizon zero B)) zero)
  (QuadraticTowerArrayCodec.digit (codeCap B) (rem i (QuadraticTowerArrayCodec.horizon zero B)) zero))
def baseBody : PTm 2 := baseRow (var 1) (var 0)
def base (B : PTm n) : PTm n := sequence baseBody (rows zero B) B
def baseSchema : PTm 2 := base (var 0)
def stepSchema : PTm 4 := step (var 0) (var 1) (var 2) (var 3)
def table (h B D : PTm n) : PTm n := DemandRecursion.X demandF baseSchema stepSchema h B D
def query (h B D A C : PTm n) : PTm n := lookup h B (table h B D) A C

@[simp] theorem subst_sourceCost {k : ℕ} (σ : Fin n → PTm k) (h : PTm n) :
    Syn.subst σ (sourceCost h) = sourceCost (Syn.subst σ h) := by simp [sourceCost]
@[simp] theorem subst_budget {k : ℕ} (σ : Fin n → PTm k) (h B D : PTm n) :
    Syn.subst σ (budget h B D) = budget (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) := by simp [budget]
@[simp] theorem subst_rows {k : ℕ} (σ : Fin n → PTm k) (h B : PTm n) :
    Syn.subst σ (rows h B) = rows (Syn.subst σ h) (Syn.subst σ B) := by simp [rows]
@[simp] theorem subst_address {k : ℕ} (σ : Fin n → PTm k) (h B A C : PTm n) :
    Syn.subst σ (address h B A C) = address (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ C) := by simp [address]
@[simp] theorem subst_lookup {k : ℕ} (σ : Fin n → PTm k) (h B T A C : PTm n) :
    Syn.subst σ (lookup h B T A C) = lookup (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ C) := by simp [lookup]
@[simp] theorem subst_leftHalf {k : ℕ} (σ : Fin n → PTm k) (h A : PTm n) :
    Syn.subst σ (leftHalf h A) = leftHalf (Syn.subst σ h) (Syn.subst σ A) := by simp [leftHalf]
@[simp] theorem subst_rightHalf {k : ℕ} (σ : Fin n → PTm k) (h A : PTm n) :
    Syn.subst σ (rightHalf h A) = rightHalf (Syn.subst σ h) (Syn.subst σ A) := by simp [rightHalf]
@[simp] theorem subst_recipe {k : ℕ} (σ : Fin n → PTm k) (h B T D A C : PTm n) :
    Syn.subst σ (recipe h B T D A C) = recipe (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ T)
      (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [recipe]
@[simp] theorem subst_rowValue {k : ℕ} (σ : Fin n → PTm k) (h B T D i : PTm n) :
    Syn.subst σ (rowValue h B T D i) = rowValue (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ T)
      (Syn.subst σ D) (Syn.subst σ i) := by simp [rowValue]
@[simp] theorem subst_rowData {k : ℕ} (σ : Fin n → PTm k) (h B T D : PTm n) :
    Syn.subst σ (rowData h B T D) = rowData (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ T) (Syn.subst σ D) := by simp [rowData]
@[simp] theorem subst_step {k : ℕ} (σ : Fin n → PTm k) (h B T D : PTm n) :
    Syn.subst σ (step h B T D) = step (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ T) (Syn.subst σ D) := by simp [step]
@[simp] theorem subst_baseRow {k : ℕ} (σ : Fin n → PTm k) (B i : PTm n) :
    Syn.subst σ (baseRow B i) = baseRow (Syn.subst σ B) (Syn.subst σ i) := by simp [baseRow]
@[simp] theorem subst_base {k : ℕ} (σ : Fin n → PTm k) (B : PTm n) :
    Syn.subst σ (base B) = base (Syn.subst σ B) := by simp [base]
@[simp] theorem subst_table {k : ℕ} (σ : Fin n → PTm k) (h B D : PTm n) :
    Syn.subst σ (table h B D) = table (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) := by
  simp only [table,DemandRecursion.X,DemandRecursion.subst_V]
@[simp] theorem subst_query {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    Syn.subst σ (query h B D A C) = query (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [query]

theorem budget_at (h B D : PTm n) : Γ ⊢[PRAAx] budget h B D ≐ majorant (sourceCost (succ h)) B := by
  simpa [budget,demandF,demandBody,ap3] using toPR_eq (Γ := Γ) demandBody ![h,B,D]
theorem table_zero (B D : PTm n) : Γ ⊢[PRAAx] table zero B D ≐ base B := by
  simpa only [table,baseSchema,subst_base,inst2,Syn.subst_var,Matrix.cons_val_zero] using
    DemandRecursion.demand_zero (Γ := Γ) demandF baseSchema stepSchema B D
theorem table_succ (h B D : PTm n) : Γ ⊢[PRAAx]
    table (succ h) B D ≐ step h B (table h (budget h B D) D) D := by
  simpa only [table,budget,DemandRecursion.appF,stepSchema,subst_step,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using DemandRecursion.demand_succ (Γ := Γ) demandF baseSchema stepSchema h B D
theorem table_congr {h h' B B' D D' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hb : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] D ≐ D') : Γ ⊢[PRAAx] table h B D ≐ table h' B' D' := by
  simpa only [subst_table,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (table (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![h,B,D]) (σ' := ![h',B',D']) (fun i => by fin_cases i; exact hh; exact hb; exact hd)
theorem rows_congr {h h' B B' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h') (hb : Γ ⊢[PRAAx] B ≐ B') :
    Γ ⊢[PRAAx] rows h B ≐ rows h' B' := by
  simpa only [subst_rows,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (rows (var 0) (var 1) : PTm 2) (σ := ![h,B]) (σ' := ![h',B'])
      (fun i => by fin_cases i; exact hh; exact hb)
theorem table_length (h B D : PTm n) : Γ ⊢[PRAAx] length (table h B D) ≐ rows h B := by
  refine .orE (zero_or_succ h) ?_ ?_
  · exact (congrFst ((table_congr Prf.hyp0 (.eqRefl B) (.eqRefl D)).eqTrans (table_zero B D))).eqTrans
      ((sequence_length _ _ _).eqTrans (rows_congr Prf.hyp0.eqSymm (.eqRefl B)))
  · exact (congrFst ((table_congr Prf.hyp0 (.eqRefl B) (.eqRefl D)).eqTrans (table_succ _ B D))).eqTrans
      ((sequence_length _ _ _).eqTrans (rows_congr Prf.hyp0.eqSymm (.eqRefl B)))

theorem row_value_congr {h h' B B' T T' D D' i i' : PTm n}
    (hh : Γ ⊢[PRAAx] h ≐ h') (hb : Γ ⊢[PRAAx] B ≐ B') (ht : Γ ⊢[PRAAx] T ≐ T')
    (hd : Γ ⊢[PRAAx] D ≐ D') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] rowValue h B T D i ≐ rowValue h' B' T' D' i' := by
  simpa [subst_rowValue] using
    Prf.eqCongr (rowValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![h,B,T,D,i]) (σ' := ![h',B',T',D',i'])
      (fun j => by fin_cases j; exact hh; exact hb; exact ht; exact hd; exact hi)
theorem recipe_congr {h h' B B' T T' D D' A A' C C' : PTm n}
    (hh : Γ ⊢[PRAAx] h ≐ h') (hb : Γ ⊢[PRAAx] B ≐ B') (ht : Γ ⊢[PRAAx] T ≐ T')
    (hd : Γ ⊢[PRAAx] D ≐ D') (ha : Γ ⊢[PRAAx] A ≐ A') (hc : Γ ⊢[PRAAx] C ≐ C') :
    Γ ⊢[PRAAx] recipe h B T D A C ≐ recipe h' B' T' D' A' C' := by
  simpa [subst_recipe] using
    Prf.eqCongr (recipe (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![h,B,T,D,A,C]) (σ' := ![h',B',T',D',A',C'])
      (fun j => by fin_cases j; exact hh; exact hb; exact ht; exact hd; exact ha; exact hc)
theorem decoded_congr {W W' S S' w w' : PTm n} (hW : Γ ⊢[PRAAx] W ≐ W')
    (hS : Γ ⊢[PRAAx] S ≐ S') (hw : Γ ⊢[PRAAx] w ≐ w') :
    Γ ⊢[PRAAx] QuadraticTowerArrayCodec.decoded W S w ≐ QuadraticTowerArrayCodec.decoded W' S' w' := by
  simpa [QuadraticTowerArrayCodec.subst_decoded] using
    Prf.eqCongr (QuadraticTowerArrayCodec.decoded (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![W,S,w]) (σ' := ![W',S',w']) (fun j => by fin_cases j; exact hW; exact hS; exact hw)

theorem row_body_at (h B T D i : PTm n) : Γ ⊢[PRAAx] inst2 rowBody i (rowData h B T D) ≐ rowValue h B T D i := by
  simp only [rowBody,inst2,subst_rowValue,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact row_value_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))
    ((congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem step_lookup (h B T D i : PTm n) (hi : Γ ⊢[PRAAx] lt i (rows (succ h) B)) :
    Γ ⊢[PRAAx] entry (step h B T D) i ≐ rowValue h B T D i :=
  (sequence_decode rowBody (x := rowData h B T D) hi).eqTrans (row_body_at _ _ _ _ _)
theorem base_lookup (B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (rows zero B)) :
    Γ ⊢[PRAAx] entry (base B) i ≐ baseRow B i := by
  simpa only [base,baseBody,inst2,subst_baseRow,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    sequence_decode (Γ := Γ) baseBody (x := B) hi

theorem address_bound (h B A C : PTm n)
    (ha : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight h A B)
    (hc : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight h C B) :
    Γ ⊢[PRAAx] lt (address h B A C) (rows h B) :=
  lt_congr (by unfold address; ipra_ring) (.eqRefl _)
    (MixedRadixExpansion.append_interval (QuadraticTowerArrayCodec.code_bound h C B hc)
      (QuadraticTowerArrayCodec.code_bound h A B ha))
theorem horizon_positive (h B : PTm n) : Γ ⊢[PRAAx] le one (QuadraticTowerArrayCodec.horizon h B) :=
  RuntimeWordAppend.power_positive (codeCap B) (width h) (zero_lt_succ _)
theorem address_parts (h B A C : PTm n)
    (hc : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight h C B) : Γ ⊢[PRAAx]
    (quo (address h B A C) (QuadraticTowerArrayCodec.horizon h B) ≐ QuadraticTowerArrayCodec.code h A B) ⋏
      (rem (address h B A C) (QuadraticTowerArrayCodec.horizon h B) ≐ QuadraticTowerArrayCodec.code h C B) :=
  RuntimeWordAppend.divide_unique _ _ _ _ (horizon_positive h B) (by unfold address; ipra_ring)
    (QuadraticTowerArrayCodec.code_bound h C B hc)

theorem row_at_address (h B T D A C : PTm n)
    (hc : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight (succ h) C B) : Γ ⊢[PRAAx]
    rowValue h B T D (address (succ h) B A C) ≐ recipe h B T D
      (QuadraticTowerArrayCodec.restored (succ h) A B) (QuadraticTowerArrayCodec.restored (succ h) C B) := by
  have parts := address_parts (succ h) B A C hc
  exact recipe_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (decoded_congr (.eqRefl _) (.eqRefl _) (Prf.andE₁ parts))
    (decoded_congr (.eqRefl _) (.eqRefl _) (Prf.andE₂ parts))

/-- This is the actual guarded next-row equation. Lower lookups, including
the query at the computed be operand, remain the original numerical terms. -/
theorem query_succ (h B D A C : PTm n)
    (ha : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight (succ h) A B)
    (hc : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight (succ h) C B) : Γ ⊢[PRAAx]
    query (succ h) B D A C ≐ recipe h B (table h (budget h B D) D) D
      (QuadraticTowerArrayCodec.restored (succ h) A B) (QuadraticTowerArrayCodec.restored (succ h) C B) :=
  (entry_congr (table_succ h B D) (.eqRefl _)).eqTrans
    ((step_lookup h B (table h (budget h B D) D) D _ (address_bound _ _ _ _ ha hc)).eqTrans
      (row_at_address h B _ D A C hc))
theorem query_zero (B D A C : PTm n)
    (ha : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight zero A B)
    (hc : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight zero C B) : Γ ⊢[PRAAx]
    query zero B D A C ≐ singleton (RationalArithmetic.multiply
      (QuadraticTowerArrayCodec.digit (codeCap B) (QuadraticTowerArrayCodec.code zero A B) zero)
      (QuadraticTowerArrayCodec.digit (codeCap B) (QuadraticTowerArrayCodec.code zero C B) zero)) := by
  have parts := address_parts zero B A C hc
  have dig (w w' : PTm n) (hw : Γ ⊢[PRAAx] w ≐ w') : Γ ⊢[PRAAx]
      QuadraticTowerArrayCodec.digit (codeCap B) w zero ≐ QuadraticTowerArrayCodec.digit (codeCap B) w' zero :=
    congrAp2 remF (congrAp2 quoF hw (.eqRefl _)) (.eqRefl _)
  have scalar := RationalAlgebra.multiply_congr (dig _ _ (Prf.andE₁ parts)) (dig _ _ (Prf.andE₂ parts))
  have row : Γ ⊢[PRAAx] baseRow B (address zero B A C) ≐ singleton (RationalArithmetic.multiply
      (QuadraticTowerArrayCodec.digit (codeCap B) (QuadraticTowerArrayCodec.code zero A B) zero)
      (QuadraticTowerArrayCodec.digit (codeCap B) (QuadraticTowerArrayCodec.code zero C B) zero)) := by
    simpa only [baseRow,QuadraticTowerCoefficients.subst_singleton,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (singleton (var 0) : PTm 1) (σ := ![_]) (σ' := ![_]) (fun i => by fin_cases i; exact scalar)
  exact (entry_congr (table_zero B D) (.eqRefl _)).eqTrans
    ((base_lookup B _ (address_bound _ _ _ _ ha hc)).eqTrans row)

theorem recipe_length (h B T D A C : PTm n) : Γ ⊢[PRAAx] length (recipe h B T D A C) ≐ width (succ h) :=
  (SequenceComposition.append_length _ _).eqTrans
    ((congrAdd (QuadraticTowerCoefficientArithmetic.added_length _ _ _)
      (QuadraticTowerCoefficientArithmetic.added_length _ _ _)).eqTrans
      (QuadraticTowerCoefficients.width_succ h).eqSymm)
theorem base_entry_length (B i : PTm n) (hi : Γ ⊢[PRAAx] lt i (rows zero B)) :
    Γ ⊢[PRAAx] length (entry (base B) i) ≐ one :=
  (congrFst (base_lookup B i hi)).eqTrans (QuadraticTowerCoefficients.singleton_length _)
theorem step_entry_length (h B T D i : PTm n) (hi : Γ ⊢[PRAAx] lt i (rows (succ h) B)) :
    Γ ⊢[PRAAx] length (entry (step h B T D) i) ≐ width (succ h) :=
  (congrFst (step_lookup h B T D i hi)).eqTrans (recipe_length _ _ _ _ _ _)
theorem table_entry_length (h B D i : PTm n) (hi : Γ ⊢[PRAAx] lt i (rows h B)) :
    Γ ⊢[PRAAx] length (entry (table h B D) i) ≐ width h := by
  refine .orE (zero_or_succ h) ?_ ?_
  · have bound : ((h ≐ zero) :: Γ) ⊢[PRAAx] lt i (rows zero B) :=
      lt_congr (.eqRefl _) (rows_congr Prf.hyp0 (.eqRefl _)) hi.wk
    have value : ((h ≐ zero) :: Γ) ⊢[PRAAx] entry (table h B D) i ≐ entry (base B) i :=
      entry_congr ((table_congr Prf.hyp0 (.eqRefl B) (.eqRefl D)).eqTrans (table_zero B D)) (.eqRefl i)
    exact (congrFst value).eqTrans ((base_entry_length B i bound).eqTrans
      ((QuadraticTowerCoefficients.width_zero).eqSymm.eqTrans (congrAp2 powF Prf.hyp0.eqSymm (.eqRefl _))))
  · have bound : ((h ≐ succ (PTm.pred h)) :: Γ) ⊢[PRAAx] lt i (rows (succ (PTm.pred h)) B) :=
      lt_congr (.eqRefl _) (rows_congr Prf.hyp0 (.eqRefl _)) hi.wk
    have value : ((h ≐ succ (PTm.pred h)) :: Γ) ⊢[PRAAx] entry (table h B D) i ≐
        entry (step (PTm.pred h) B (table (PTm.pred h) (budget (PTm.pred h) B D) D) D) i :=
      entry_congr ((table_congr Prf.hyp0 (.eqRefl B) (.eqRefl D)).eqTrans (table_succ _ B D)) (.eqRefl i)
    exact (congrFst value).eqTrans ((step_entry_length _ B _ D i bound).eqTrans
      (congrAp2 powF Prf.hyp0.eqSymm (.eqRefl _)))
theorem query_length (h B D A C : PTm n)
    (ha : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight h A B)
    (hc : Γ ⊢[PRAAx] QuadraticTowerArrayCodec.arrayHeight h C B) :
    Γ ⊢[PRAAx] length (query h B D A C) ≐ width h :=
  table_entry_length h B D _ (address_bound h B A C ha hc)

/-- The actual intermediate result passed as the third lower query's
operand. Its height/range is deliberately a later theorem, not a premise. -/
def computedBe (h B D A C : PTm n) : PTm n := lookup h (budget h B D) (table h (budget h B D) D)
  (rightHalf h (QuadraticTowerArrayCodec.restored (succ h) A B))
  (rightHalf h (QuadraticTowerArrayCodec.restored (succ h) C B))
def computedBed (h B D A C : PTm n) : PTm n :=
  lookup h (budget h B D) (table h (budget h B D) D) (computedBe h B D A C) (entry D h)
def operands (h B D A C : PTm n) : PTm n := pairT (computedBe h B D A C) (computedBed h B D A C)
def tableF : PR 3 := PTm.toPR (table (var 0) (var 1) (var 2))
def queryF : PR 5 := PTm.toPR (query (var 0) (var 1) (var 2) (var 3) (var 4))
def operandsF : PR 5 := PTm.toPR (operands (var 0) (var 1) (var 2) (var 3) (var 4))

@[simp] theorem subst_computedBe {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    Syn.subst σ (computedBe h B D A C) = computedBe (Syn.subst σ h) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [computedBe]
@[simp] theorem subst_computedBed {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    Syn.subst σ (computedBed h B D A C) = computedBed (Syn.subst σ h) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [computedBed]
@[simp] theorem subst_operands {k : ℕ} (σ : Fin n → PTm k) (h B D A C : PTm n) :
    Syn.subst σ (operands h B D A C) = operands (Syn.subst σ h) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ C) := by simp [operands]
theorem table_program_at (h B D : PTm n) : Γ ⊢[PRAAx] ap3 tableF h B D ≐ table h B D := by
  simpa [tableF,ap3] using toPR_eq (Γ := Γ) (table (var 0) (var 1) (var 2) : PTm 3) ![h,B,D]
theorem query_program_at (h B D A C : PTm n) : Γ ⊢[PRAAx] PTm.app queryF ![h,B,D,A,C] ≐ query h B D A C := by
  simpa [queryF] using toPR_eq (Γ := Γ) (query (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,B,D,A,C]
theorem operands_program_at (h B D A C : PTm n) : Γ ⊢[PRAAx] PTm.app operandsF ![h,B,D,A,C] ≐ operands h B D A C := by
  simpa [operandsF] using toPR_eq (Γ := Γ) (operands (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,B,D,A,C]
theorem returned_be (h B D A C : PTm n) : Γ ⊢[PRAAx] fstT (PTm.app operandsF ![h,B,D,A,C]) ≐ computedBe h B D A C :=
  (congrFst (operands_program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_bed (h B D A C : PTm n) : Γ ⊢[PRAAx] sndT (PTm.app operandsF ![h,B,D,A,C]) ≐
    lookup h (budget h B D) (table h (budget h B D) D) (computedBe h B D A C) (entry D h) :=
  (congrSnd (operands_program_at _ _ _ _ _)).eqTrans (snd_pair _ _)

theorem actual_table_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (budget (var 0) (var 1) (var 2) ≐ majorant (sourceCost (succ (var 0))) (var 1)) := closeUniv 3 (budget_at _ _ _)
theorem actual_changed_budget_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (table (succ (var 0)) (var 1) (var 2) ≐ step (var 0) (var 1)
      (table (var 0) (budget (var 0) (var 1) (var 2)) (var 2)) (var 2)) := closeUniv 3 (table_succ _ _ _)
theorem actual_table_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (table (var 0) (var 1) (var 2)) ≐ rows (var 0) (var 1)) := closeUniv 3 (table_length _ _ _)
theorem actual_stored_row_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (rows (var 0) (var 1)) ⟶ length (entry (table (var 0) (var 1) (var 2)) (var 3)) ≐ width (var 0)) :=
  closeUniv 4 (.impI (table_entry_length _ _ _ _ Prf.hyp0))
theorem actual_guarded_query_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerArrayCodec.arrayHeight (succ (var 0)) (var 3) (var 1) ⟶
      QuadraticTowerArrayCodec.arrayHeight (succ (var 0)) (var 4) (var 1) ⟶
      query (succ (var 0)) (var 1) (var 2) (var 3) (var 4) ≐ recipe (var 0) (var 1)
        (table (var 0) (budget (var 0) (var 1) (var 2)) (var 2)) (var 2)
        (QuadraticTowerArrayCodec.restored (succ (var 0)) (var 3) (var 1))
        (QuadraticTowerArrayCodec.restored (succ (var 0)) (var 4) (var 1))) :=
  closeUniv 5 (.impI (.impI (query_succ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_guarded_query_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerArrayCodec.arrayHeight (var 0) (var 3) (var 1) ⟶
      QuadraticTowerArrayCodec.arrayHeight (var 0) (var 4) (var 1) ⟶
      length (query (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ width (var 0)) :=
  closeUniv 5 (.impI (.impI (query_length _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_table_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 tableF (var 0) (var 1) (var 2) ≐ table (var 0) (var 1) (var 2)) := closeUniv 3 (table_program_at _ _ _)
theorem actual_query_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app queryF ![var 0,var 1,var 2,var 3,var 4] ≐ query (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (query_program_at _ _ _ _ _)
theorem actual_nested_operands_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app operandsF ![var 0,var 1,var 2,var 3,var 4] ≐ operands (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (operands_program_at _ _ _ _ _)
theorem actual_computed_third_operand_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (PTm.app operandsF ![var 0,var 1,var 2,var 3,var 4]) ≐ lookup (var 0)
      (budget (var 0) (var 1) (var 2)) (table (var 0) (budget (var 0) (var 1) (var 2)) (var 2))
      (computedBe (var 0) (var 1) (var 2) (var 3) (var 4)) (entry (var 2) (var 0))) :=
  closeUniv 5 (returned_bed _ _ _ _ _)

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationTable
