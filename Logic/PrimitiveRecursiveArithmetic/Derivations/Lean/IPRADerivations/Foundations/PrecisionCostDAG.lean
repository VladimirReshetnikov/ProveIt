import IPRADerivations.Analysis.RationalSumLinearity
import IPRADerivations.Analysis.RationalAlgebra
import IPRADerivations.Analysis.GaussianWeightedErrorBudget
import IPRADerivations.Foundations.BoundedSyntaxInduction
import IPRADerivations.Foundations.BoundedEnumeration
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Foundations.RealizerComposition
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CertificateTactics

/-!
# Actual rational budgets on finite topologically ordered dependency graphs

Source: `foundations/ipra_evidence_framework/report.tex`, finite witness-gluing
and precision-cost DAG paragraphs, lines 85--87. The numerical graph stores
lower-triangular rows: node v reads only predecessors w<v. A rational datum
is pair(p,q-1), decoded as the actual canonical nonnegative fraction p/q.
Missing rows/entries are explicitly guarded to the zero datum (0/1); the
padding behavior of the raw sequence decoder is never assumed.

An actual PR recursion appends eta_v + sum_(w<v) L_vw E_w. Both the graph
and local-error list are numerical data. No global budget, schedule, path
product identity or output property is an input. Uniform safe scheduling is
a separate quantitative obligation for `PrecisionCostDAGSchedule`; this
producer assumes no such bound.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.PrecisionCostDAG

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus pred)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length empty append append_length append_left append_right entry_congr)
open LeanProofs.IPRA.Foundations.RealizerComposition (ap4 subst_ap4)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add multiply represents)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize)
open LeanProofs.IPRA.Analysis.RationalFiniteSum (sum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fraction (p q : PTm n) : PTm n := normalize (ZT.ofNat p) q
def zeroCode : PTm n := fraction zero one
/-- Total nonnegative rational data. The stored denominator is q-1. -/
def decodeFraction (c : PTm n) : PTm n := fraction (fstT c) (succ (sndT c))
def safeEntry (L i : PTm n) : PTm n := Signum.sg (monus (length L) i)*entry L i
def graphRow (G v : PTm n) : PTm n := safeEntry G v
def weightDatum (G v w : PTm n) : PTm n := safeEntry (graphRow G v) w
def weight (G v w : PTm n) : PTm n := decodeFraction (weightDatum G v w)
def localError (Eta v : PTm n) : PTm n := decodeFraction (safeEntry Eta v)
def data (G Eta : PTm n) : PTm n := pairT G Eta
def productData (G v R : PTm n) : PTm n := pairT v (pairT G R)
def weightedBody : PTm 2 := multiply
  (weight (fstT (sndT (var 1))) (fstT (var 1)) (var 0))
  (entry (sndT (sndT (var 1))) (var 0))
def incoming (G v R : PTm n) : PTm n := sum weightedBody v (productData G v R)
def next (G Eta v R : PTm n) : PTm n := add (localError Eta v) (incoming G v R)
def nextF : PR 4 := PTm.toPR (next (var 0) (var 1) (var 2) (var 3))
def singleton (c : PTm n) : PTm n := sequence (var 1) one c
def rowStep : PTm 3 := append (var 1)
  (singleton (ap4 nextF (fstT (var 2)) (sndT (var 2)) (var 0) (var 1)))
def rowF : PR 2 := rec2 empty rowStep
def row (G Eta r : PTm n) : PTm n := ap2 rowF r (data G Eta)
def node (G Eta v : PTm n) : PTm n := next G Eta v (row G Eta v)

def appendF : PR 2 := PTm.toPR (append (var 0) (var 1))

@[simp] theorem subst_fraction {m : ℕ} (σ : Fin n → PTm m) (p q : PTm n) :
    Syn.subst σ (fraction p q) = fraction (Syn.subst σ p) (Syn.subst σ q) := by simp [fraction]
@[simp] theorem subst_zeroCode {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (zeroCode : PTm n) = (zeroCode : PTm m) := by simp [zeroCode]
@[simp] theorem subst_decodeFraction {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    Syn.subst σ (decodeFraction c) = decodeFraction (Syn.subst σ c) := by simp [decodeFraction]
@[simp] theorem subst_safeEntry {m : ℕ} (σ : Fin n → PTm m) (L i : PTm n) :
    Syn.subst σ (safeEntry L i) = safeEntry (Syn.subst σ L) (Syn.subst σ i) := by simp [safeEntry]
@[simp] theorem subst_graphRow {m : ℕ} (σ : Fin n → PTm m) (G v : PTm n) :
    Syn.subst σ (graphRow G v) = graphRow (Syn.subst σ G) (Syn.subst σ v) := by simp [graphRow]
@[simp] theorem subst_weightDatum {m : ℕ} (σ : Fin n → PTm m) (G v w : PTm n) :
    Syn.subst σ (weightDatum G v w) = weightDatum (Syn.subst σ G) (Syn.subst σ v) (Syn.subst σ w) := by simp [weightDatum]
@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (G v w : PTm n) :
    Syn.subst σ (weight G v w) = weight (Syn.subst σ G) (Syn.subst σ v) (Syn.subst σ w) := by simp [weight]
@[simp] theorem subst_localError {m : ℕ} (σ : Fin n → PTm m) (Eta v : PTm n) :
    Syn.subst σ (localError Eta v) = localError (Syn.subst σ Eta) (Syn.subst σ v) := by simp [localError]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (G Eta : PTm n) :
    Syn.subst σ (data G Eta) = data (Syn.subst σ G) (Syn.subst σ Eta) := by simp [data]
@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (G v R : PTm n) :
    Syn.subst σ (productData G v R) = productData (Syn.subst σ G) (Syn.subst σ v) (Syn.subst σ R) := by simp [productData]
@[simp] theorem subst_incoming {m : ℕ} (σ : Fin n → PTm m) (G v R : PTm n) :
    Syn.subst σ (incoming G v R) = incoming (Syn.subst σ G) (Syn.subst σ v) (Syn.subst σ R) := by simp [incoming]
@[simp] theorem subst_next {m : ℕ} (σ : Fin n → PTm m) (G Eta v R : PTm n) :
    Syn.subst σ (next G Eta v R) = next (Syn.subst σ G) (Syn.subst σ Eta) (Syn.subst σ v) (Syn.subst σ R) := by simp [next]
@[simp] theorem subst_singleton {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) :
    Syn.subst σ (singleton c) = singleton (Syn.subst σ c) := by simp [singleton]
@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (G Eta r : PTm n) :
    Syn.subst σ (row G Eta r) = row (Syn.subst σ G) (Syn.subst σ Eta) (Syn.subst σ r) := by simp [row]
@[simp] theorem subst_node {m : ℕ} (σ : Fin n → PTm m) (G Eta v : PTm n) :
    Syn.subst σ (node G Eta v) = node (Syn.subst σ G) (Syn.subst σ Eta) (Syn.subst σ v) := by simp [node]

theorem safeEntry_present (L i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    safeEntry L i ≐ entry L i :=
  (congrMul (AnalyticNumberTheory.Totatives.sg_lt hi) (.eqRefl _)).eqTrans (one_mul _)
theorem safeEntry_absent (L i : PTm n) (hi : Γ ⊢[PRAAx] le (length L) i) : Γ ⊢[PRAAx]
    safeEntry L i ≐ zero :=
  (congrMul (AnalyticNumberTheory.Totatives.sg_le hi) (.eqRefl _)).eqTrans (zero_mul _)

theorem fraction_represents (p q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    represents (fraction p q) (ZT.ofNat p) q :=
  Analysis.RationalIntegerNormalization.normalize_preserves_value _ _ hq
theorem fraction_well_formed (p q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    Analysis.RationalNormalForm.wellFormed (fraction p q) :=
  Analysis.RationalNormalForm.normalize_well_formed _ _ hq
theorem fraction_congr {p p' q q' : PTm n} (hp : Γ ⊢[PRAAx] p ≐ p') (hq : Γ ⊢[PRAAx] q ≐ q') : Γ ⊢[PRAAx]
    fraction p q ≐ fraction p' q' := by
  ipra_congr (fraction (var 0) (var 1) : PTm 2) with [hp, hq]
theorem decode_represents (c : PTm n) : Γ ⊢[PRAAx]
    represents (decodeFraction c) (ZT.ofNat (fstT c)) (succ (sndT c)) :=
  fraction_represents _ _ (zero_lt_succ _)

theorem append_at (a b : PTm n) : Γ ⊢[PRAAx] ap2 appendF a b ≐ append a b := by
  simpa [appendF,ap2] using toPR_eq (Γ := Γ) (append (var 0) (var 1) : PTm 2) ![a,b]
theorem append_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    append a b ≐ append a' b' :=
  (append_at _ _).eqSymm.eqTrans ((congrAp2 appendF ha hb).eqTrans (append_at _ _))
theorem singleton_length (c : PTm n) : Γ ⊢[PRAAx] length (singleton c) ≐ one :=
  MasterCertificate.sequence_length _ _ _
theorem singleton_zero (c : PTm n) : Γ ⊢[PRAAx] entry (singleton c) zero ≐ c := by
  simpa only [singleton,inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    MasterCertificate.sequence_decode (var 1 : PTm 2) (x := c) (le_refl one)
theorem singleton_congr {c d : PTm n} (h : Γ ⊢[PRAAx] c ≐ d) : Γ ⊢[PRAAx]
    singleton c ≐ singleton d := by
  ipra_congr (singleton (var 0) : PTm 1) with [h]

theorem next_at (G Eta v R : PTm n) : Γ ⊢[PRAAx] ap4 nextF G Eta v R ≐ next G Eta v R := by
  simpa [nextF,ap4] using toPR_eq (Γ := Γ) (next (var 0) (var 1) (var 2) (var 3) : PTm 4) ![G,Eta,v,R]
theorem row_zero (G Eta : PTm n) : Γ ⊢[PRAAx] row G Eta zero ≐ empty := by
  simpa [row,rowF] using rec2_zero (Γ := Γ) empty rowStep (data G Eta)
theorem row_succ (G Eta v : PTm n) : Γ ⊢[PRAAx]
    row G Eta (succ v) ≐ append (row G Eta v) (singleton (node G Eta v)) := by
  have step := rec2_succ (Γ := Γ) empty rowStep v (data G Eta)
  simp only [rowStep,SequenceComposition.subst_append,subst_singleton,subst_ap4,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at step
  have fields : Γ ⊢[PRAAx] ap4 nextF (fstT (data G Eta)) (sndT (data G Eta)) v (row G Eta v) ≐
      ap4 nextF G Eta v (row G Eta v) :=
    congrApp nextF (ts := ![fstT (data G Eta),sndT (data G Eta),v,row G Eta v])
      (us := ![G,Eta,v,row G Eta v]) (fun i => by
        fin_cases i; exact fst_pair G Eta; exact snd_pair G Eta; exact .eqRefl v; exact .eqRefl _)
  exact step.eqTrans (append_congr (.eqRefl _) (singleton_congr (fields.eqTrans (next_at _ _ _ _))))

theorem row_length (G Eta r : PTm n) : Γ ⊢[PRAAx] length (row G Eta r) ≐ r := by
  have all : Γ ⊢[PRAAx] .all (length (row (Syn.shift G) (Syn.shift Eta) (var 0)) ≐ var 0) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,SequenceComposition.subst_length,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (row_zero G Eta)).eqTrans SequenceComposition.empty_length
    · simp only [Fm.subst_eq,SequenceComposition.subst_length,subst_row,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (row_succ (Syn.shift G) (Syn.shift Eta) (var 0))).eqTrans
        ((append_length _ _).eqTrans ((congrAdd Prf.hyp0 (singleton_length _)).eqTrans (succ_eq_add_one _).eqSymm))
  simpa only [Fm.subst_eq,SequenceComposition.subst_length,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem row_old (G Eta r w : PTm n) (hw : Γ ⊢[PRAAx] lt w r) : Γ ⊢[PRAAx]
    entry (row G Eta (succ r)) w ≐ entry (row G Eta r) w :=
  (entry_congr (row_succ _ _ _) (.eqRefl _)).eqTrans
    (append_left (lt_congr (.eqRefl _) (row_length _ _ _).eqSymm hw))
theorem row_new (G Eta r : PTm n) : Γ ⊢[PRAAx] entry (row G Eta (succ r)) r ≐ node G Eta r := by
  have last : Γ ⊢[PRAAx] entry (append (row G Eta r) (singleton (node G Eta r))) (length (row G Eta r)+zero) ≐
      entry (singleton (node G Eta r)) zero := append_right (a := row G Eta r) (b := singleton (node G Eta r))
    (lt_congr (.eqRefl _) (singleton_length _).eqSymm (le_refl one))
  exact (entry_congr (row_succ _ _ _) (.eqRefl _)).eqTrans
    ((entry_congr (.eqRefl _) ((congrAdd (row_length _ _ _) (.eqRefl zero)).eqTrans (add_zero r)).eqSymm).eqTrans
      (last.eqTrans (singleton_zero _)))

theorem next_congr {G G' Eta Eta' v v' R R' : PTm n}
    (hG : Γ ⊢[PRAAx] G ≐ G') (hEta : Γ ⊢[PRAAx] Eta ≐ Eta')
    (hv : Γ ⊢[PRAAx] v ≐ v') (hR : Γ ⊢[PRAAx] R ≐ R') : Γ ⊢[PRAAx]
    next G Eta v R ≐ next G' Eta' v' R' :=
  (next_at _ _ _ _).eqSymm.eqTrans ((congrApp nextF (ts := ![G,Eta,v,R]) (us := ![G',Eta',v',R'])
    (fun i => by fin_cases i; exact hG; exact hEta; exact hv; exact hR)).eqTrans (next_at _ _ _ _))
theorem node_index_congr {v w : PTm n} (G Eta : PTm n) (h : Γ ⊢[PRAAx] v ≐ w) : Γ ⊢[PRAAx]
    node G Eta v ≐ node G Eta w :=
  next_congr (.eqRefl _) (.eqRefl _) h (congrAp2 rowF h (.eqRefl _))

def lookupLaw (G Eta w r : PTm n) : Fm PTm n :=
  lt w r ⟶ entry (row G Eta r) w ≐ node G Eta w
@[simp] theorem subst_lookupLaw {m : ℕ} (σ : Fin n → PTm m) (G Eta w r : PTm n) :
    (lookupLaw G Eta w r).subst σ = lookupLaw (Syn.subst σ G) (Syn.subst σ Eta) (Syn.subst σ w) (Syn.subst σ r) := by
  simp [lookupLaw]

/-- Actual earlier stored entries are stable throughout the whole recursion. -/
theorem row_lookup (G Eta r w : PTm n) (hw : Γ ⊢[PRAAx] lt w r) : Γ ⊢[PRAAx]
    entry (row G Eta r) w ≐ node G Eta w := by
  have all : Γ ⊢[PRAAx] .all (lookupLaw (Syn.shift G) (Syn.shift Eta) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨lt_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_lookupLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (.botE _ (succ_ne_zero' _ ((monus_zero _).eqSymm.eqTrans Prf.hyp0)))
    · simp only [subst_lookupLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)) ?_ ?_
      · exact (row_old (Syn.shift G) (Syn.shift Eta) (var 0) (Syn.shift w) Prf.hyp0).eqTrans
          (.impE Prf.hyp1.wk Prf.hyp0)
      · exact (entry_congr (.eqRefl _) Prf.hyp0).eqTrans
          ((row_new (Syn.shift G) (Syn.shift Eta) (var 0)).eqTrans
            (node_index_congr (Syn.shift G) (Syn.shift Eta) Prf.hyp0.eqSymm))
  have rule : Γ ⊢[PRAAx] lookupLaw G Eta w r := by
    simpa only [subst_lookupLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hw

def weightF : PR 3 := PTm.toPR (weight (var 0) (var 1) (var 2))
theorem weight_at (G v w : PTm n) : Γ ⊢[PRAAx] ap3 weightF G v w ≐ weight G v w := by
  simpa [weightF,ap3] using toPR_eq (Γ := Γ) (weight (var 0) (var 1) (var 2) : PTm 3) ![G,v,w]
theorem weight_congr {G G' v v' w w' : PTm n} (hG : Γ ⊢[PRAAx] G ≐ G')
    (hv : Γ ⊢[PRAAx] v ≐ v') (hw : Γ ⊢[PRAAx] w ≐ w') : Γ ⊢[PRAAx]
    weight G v w ≐ weight G' v' w' :=
  (weight_at _ _ _).eqSymm.eqTrans ((congrAp3 weightF hG hv hw).eqTrans (weight_at _ _ _))

theorem weighted_at (G v R w : PTm n) : Γ ⊢[PRAAx]
    Analysis.RationalFiniteSum.term weightedBody w (productData G v R) ≐
      multiply (weight G v w) (entry R w) := by
  have tail := snd_pair (Γ := Γ) v (pairT G R)
  have g := (congrFst tail).eqTrans (fst_pair G R)
  have r := (congrSnd tail).eqTrans (snd_pair G R)
  simpa only [Analysis.RationalFiniteSum.term,weightedBody,inst2,Analysis.RationalArithmetic.subst_multiply,
    subst_weight,MasterCertificate.subst_entry,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,productData] using
    Analysis.RationalAlgebra.multiply_congr (weight_congr g (fst_pair v (pairT G R)) (.eqRefl w))
      (entry_congr r (.eqRefl w))

theorem rationalEq_of_code {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] Analysis.RationalArgmin.rationalEq a b :=
  (Analysis.RationalArgmin.left_congr (.eqRefl a) h).eqSymm.eqTrans
    (Analysis.RationalArgmin.left_congr h (.eqRefl a))

theorem incoming_ext (G v R S : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift v) ⟶ entry (Syn.shift R) (var 0) ≐ entry (Syn.shift S) (var 0))) : Γ ⊢[PRAAx]
    incoming G v R ≐ incoming G v S := by
  apply Analysis.RationalFiniteSum.sum_ext weightedBody weightedBody
  refine .allI (.impI ?_)
  have equality := Prf.impE h.allOpen.wk Prf.hyp0
  have e : (lt (var 0) (Syn.shift v)) :: Γ.map Fm.shift ⊢[PRAAx]
      Analysis.RationalFiniteSum.term weightedBody (var 0) (productData (Syn.shift G) (Syn.shift v) (Syn.shift R)) ≐
        Analysis.RationalFiniteSum.term weightedBody (var 0) (productData (Syn.shift G) (Syn.shift v) (Syn.shift S)) :=
    (weighted_at _ _ _ _).eqTrans ((Analysis.RationalAlgebra.multiply_congr (.eqRefl _) equality).eqTrans
      (weighted_at _ _ _ _).eqSymm)
  simpa only [Syn.shift,subst_productData] using rationalEq_of_code e

/-- Source recurrence for the ACTUAL final returned row, not an incoming
recurrence or an equality between arbitrary sequence codes. -/
theorem final_recurrence (G Eta N v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    entry (row G Eta N) v ≐ add (localError Eta v) (incoming G v (row G Eta N)) := by
  refine (row_lookup G Eta N v hv).eqTrans (Analysis.RationalAlgebra.add_congr (.eqRefl _) ?_)
  apply incoming_ext
  refine .allI (.impI ?_)
  have range : (lt (var 0) (Syn.shift v)) :: Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift v) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hv.shift.wk
  simpa only [Syn.shift,subst_row] using
    (row_lookup (Syn.shift G) (Syn.shift Eta) (Syn.shift v) (var 0) Prf.hyp0).eqTrans
      (row_lookup (Syn.shift G) (Syn.shift Eta) (Syn.shift N) (var 0) (lt_of_lt_of_le Prf.hyp0 (le_of_lt range))).eqSymm

/-- Reuse the existing independent-denominator scalar arithmetic. -/
theorem fraction_add (a b D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    add (fraction a D) (fraction b D) ≐ fraction (a+b) D :=
  Analysis.GaussianWeightedErrorBudget.frac_add _ _ _ hD
theorem fraction_scale (m a D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    multiply (fraction m one) (fraction a D) ≐ fraction (m*a) D :=
  Analysis.GaussianWeightedErrorBudget.nat_scale_frac _ _ _ hD
theorem fraction_order (a b D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    rationalLE (fraction a D) (fraction b D) := Analysis.GaussianWeightedErrorBudget.frac_order _ _ _ hD hab

theorem zero_integer : Γ ⊢[PRAAx] (zeroCode : PTm n) ≐ Analysis.RationalIntegerNormalization.integerCode (ZT.natLit 0) := by
  apply Analysis.RationalIntegerNormalization.normalize_integer _ _ _ (le_refl one)
  ipra_lc

theorem fraction_nonnegative (p D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    rationalLE zeroCode (fraction p D) := by
  apply Analysis.RationalArithmetic.order_of_representations _ _ _ _ _ _
    (fraction_represents zero one (le_refl _)) (fraction_represents p D hD) (le_refl _) hD
  apply zle_of_toZ p
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem fraction_numerator_nonnegative (p D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    le (Analysis.RationalSupMetric.numeratorOf (fraction p D)).neg (Analysis.RationalSupMetric.numeratorOf (fraction p D)).pos :=
  Analysis.GaussianRationalL1.nonnegative_of_representation _ _ _ hD (fraction_represents _ _ hD)
theorem numerator_nonnegative_of_zero_lower (c : PTm n) (hc : Γ ⊢[PRAAx] rationalLE zeroCode c) : Γ ⊢[PRAAx]
    le (Analysis.RationalSupMetric.numeratorOf c).neg (Analysis.RationalSupMetric.numeratorOf c).pos :=
  Analysis.GaussianRationalL1.nonnegative_of_lower zeroCode c (fraction_numerator_nonnegative zero one (le_refl _)) hc

theorem multiply_zero (c : PTm n) : Γ ⊢[PRAAx] multiply c zeroCode ≐ zeroCode := by
  have rep := Analysis.RationalRepresentations.represents_multiply c zeroCode _ _ _ _
    (Analysis.RationalRepresentations.represents_self (Γ := Γ) c) (fraction_represents zero one (le_refl _))
  apply Analysis.RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (Analysis.RationalArithmetic.multiply_guard _ _) (fraction_well_formed zero one (le_refl _))
    rep (fraction_represents zero one (le_refl _))
    (Analysis.RationalAlgebra.positive_product (Analysis.RationalArgmin.denominator_positive c) (le_refl one)) (le_refl one)
  ipra_lc

theorem add_nonnegative (a b : PTm n) (ha : Γ ⊢[PRAAx] rationalLE zeroCode a)
    (hb : Γ ⊢[PRAAx] rationalLE zeroCode b) : Γ ⊢[PRAAx] rationalLE zeroCode (add a b) :=
  Analysis.RationalArgmin.rationalLE_congr
    ((fraction_add zero zero one (le_refl _)).eqTrans (fraction_congr (add_zero zero) (.eqRefl _))) (.eqRefl _)
    (Analysis.GaussianRationalSyntheticBounds.add_monotone zeroCode a zeroCode b ha hb)
theorem multiply_nonnegative (a b : PTm n) (ha : Γ ⊢[PRAAx] rationalLE zeroCode a)
    (hb : Γ ⊢[PRAAx] rationalLE zeroCode b) : Γ ⊢[PRAAx] rationalLE zeroCode (multiply a b) :=
  Analysis.RationalArgmin.rationalLE_congr (multiply_zero a) (.eqRefl _)
    (Analysis.RationalArithmetic.multiply_monotone a zeroCode b (numerator_nonnegative_of_zero_lower a ha) hb)

theorem sum_zero_code (A : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] sum A zero x ≐ zeroCode :=
  (Analysis.RationalFiniteSum.sum_zero A x).eqTrans zero_integer.eqSymm

def nonnegativeTerms (A : PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ rationalLE zeroCode (Analysis.RationalFiniteSum.term A (var 0) (Syn.shift x)))
def sumNonnegativeLaw (A : PTm 2) (N x r : PTm n) : Fm PTm n :=
  le r N ⟶ rationalLE zeroCode (sum A r x)
@[simp] theorem subst_nonnegativeTerms {m : ℕ} (σ : Fin n → PTm m) (A : PTm 2) (N x : PTm n) :
    (nonnegativeTerms A N x).subst σ = nonnegativeTerms A (Syn.subst σ N) (Syn.subst σ x) := by
  simp [nonnegativeTerms,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_sumNonnegativeLaw {m : ℕ} (σ : Fin n → PTm m) (A : PTm 2) (N x r : PTm n) :
    (sumNonnegativeLaw A N x r).subst σ = sumNonnegativeLaw A (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ r) := by
  simp [sumNonnegativeLaw]

theorem sum_nonnegative (A : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] nonnegativeTerms A N x) : Γ ⊢[PRAAx]
    rationalLE zeroCode (sum A N x) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] nonnegativeTerms A (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_nonnegativeTerms,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (sumNonnegativeLaw A (Syn.shift N) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_sumNonnegativeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (Analysis.RationalArgmin.rationalLE_congr (.eqRefl _) (sum_zero_code A x).eqSymm
        (Analysis.RationalArgmin.reflexive _))
    · simp only [subst_sumNonnegativeLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift N) ::
        sumNonnegativeLaw A (Syn.shift N) (Syn.shift x) (var 0) :: Γ.map Fm.shift
      have previous : Δ ⊢[PRAAx] rationalLE zeroCode (sum A (var 0) (Syn.shift x)) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have gate : Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift N) ⟶
          rationalLE zeroCode (Analysis.RationalFiniteSum.term A (var 0) (Syn.shift x)) := by
        simpa only [nonnegativeTerms,Fm.subst_imp,subst_lt,Analysis.RationalArgmin.subst_rationalLE,
          subst_zeroCode,Analysis.RationalFiniteSum.subst_term,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hs.allE (var 0)
      have term : Δ ⊢[PRAAx] rationalLE zeroCode (Analysis.RationalFiniteSum.term A (var 0) (Syn.shift x)) :=
        .impE gate.wk.wk Prf.hyp0
      exact Analysis.RationalArgmin.rationalLE_congr (.eqRefl _)
        (Analysis.RationalFiniteSum.sum_succ A (var 0) (Syn.shift x)).eqSymm (add_nonnegative _ _ previous term)
  have final : Γ ⊢[PRAAx] sumNonnegativeLaw A N x N := by
    simpa only [subst_sumNonnegativeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE final (le_refl _)

/-- This finite all-bit, not a quantified induction predicate, records
nonnegativity of every already computed scalar budget. -/
def nonnegativeDefect : PTm 2 := monus
  (Analysis.RationalArgmin.left zeroCode (entry (var 1) (var 0)))
  (Analysis.RationalArgmin.left (entry (var 1) (var 0)) zeroCode)
def nonnegativeBody : PTm 2 := BoundedEnumeration.vb nonnegativeDefect
def rowsNonnegative (r R : PTm n) : Fm PTm n := BoundedReflection.allB nonnegativeBody r R ≐ one
@[simp] theorem subst_rowsNonnegative {m : ℕ} (σ : Fin n → PTm m) (r R : PTm n) :
    (rowsNonnegative r R).subst σ = rowsNonnegative (Syn.subst σ r) (Syn.subst σ R) := by
  simp [rowsNonnegative,BoundedReflection.allB]
theorem nonnegative_defect_at (i R : PTm n) :
    inst2 nonnegativeDefect i R = monus (Analysis.RationalArgmin.left zeroCode (entry R i))
      (Analysis.RationalArgmin.left (entry R i) zeroCode) := by simp [nonnegativeDefect,inst2]

theorem rows_nonnegative_at (r R i : PTm n) (h : Γ ⊢[PRAAx] rowsNonnegative r R)
    (hi : Γ ⊢[PRAAx] lt i r) : Γ ⊢[PRAAx] rationalLE zeroCode (entry R i) := by
  have kept := BoundedReflection.all_elim nonnegativeBody h hi
  have valid := BoundedEnumeration.valid_of_kept (f := nonnegativeDefect) kept
  simpa only [nonnegative_defect_at,Analysis.RationalArgmin.rationalLE,le] using valid

theorem rows_nonnegative_intro (r R : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift r) ⟶ rationalLE zeroCode (entry (Syn.shift R) (var 0)))) : Γ ⊢[PRAAx]
    rowsNonnegative r R := by
  apply BoundedReflection.all_intro nonnegativeBody
  refine .allI (.impI ?_)
  have localOrder := Prf.impE h.allOpen.wk Prf.hyp0
  have valid : (lt (var 0) (Syn.shift r)) :: Γ.map Fm.shift ⊢[PRAAx]
      inst2 nonnegativeDefect (var 0) (Syn.shift R) ≐ zero := by
    simpa only [nonnegative_defect_at,Analysis.RationalArgmin.rationalLE,le] using localOrder
  exact BoundedEnumeration.kept_of_valid valid

theorem decode_nonnegative (c : PTm n) : Γ ⊢[PRAAx] rationalLE zeroCode (decodeFraction c) :=
  fraction_nonnegative _ _ (zero_lt_succ _)
theorem weight_nonnegative (G v w : PTm n) : Γ ⊢[PRAAx] rationalLE zeroCode (weight G v w) := decode_nonnegative _
theorem error_nonnegative (Eta v : PTm n) : Γ ⊢[PRAAx] rationalLE zeroCode (localError Eta v) := decode_nonnegative _

theorem next_nonnegative (G Eta v R : PTm n) (hRows : Γ ⊢[PRAAx] rowsNonnegative v R) : Γ ⊢[PRAAx]
    rationalLE zeroCode (next G Eta v R) := by
  apply add_nonnegative _ _ (error_nonnegative _ _)
  apply sum_nonnegative weightedBody
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowsNonnegative (Syn.shift v) (Syn.shift R) := by
    simpa only [Fm.shift,subst_rowsNonnegative,Syn.shift] using hRows.shift
  have actual := Analysis.RationalArgmin.rationalLE_congr (.eqRefl _)
    (weighted_at (Γ := lt (var 0) (Syn.shift v) :: Γ.map Fm.shift) (Syn.shift G) (Syn.shift v) (Syn.shift R) (var 0)).eqSymm
      (multiply_nonnegative _ _ (weight_nonnegative _ _ _) (rows_nonnegative_at _ _ _ hs.wk Prf.hyp0))
  simpa only [Syn.shift,subst_productData] using actual

theorem new_entry_nonnegative (G Eta r w : PTm n)
    (hRows : Γ ⊢[PRAAx] rowsNonnegative r (row G Eta r)) (hw : Γ ⊢[PRAAx] lt w (succ r)) : Γ ⊢[PRAAx]
    rationalLE zeroCode (entry (row G Eta (succ r)) w) := by
  refine .orE (lt_or_eq_of_le ((succ_monus_succ _ _).eqSymm.eqTrans hw)) ?_ ?_
  · exact Analysis.RationalArgmin.rationalLE_congr (.eqRefl _) (row_old G Eta r w Prf.hyp0).eqSymm
      (rows_nonnegative_at _ _ _ hRows.wk Prf.hyp0)
  · have e : ((w ≐ r) :: Γ) ⊢[PRAAx] entry (row G Eta (succ r)) w ≐ node G Eta r :=
      (entry_congr (.eqRefl _) Prf.hyp0).eqTrans (row_new G Eta r)
    exact Analysis.RationalArgmin.rationalLE_congr (.eqRefl _) e.eqSymm (next_nonnegative G Eta r _ hRows).wk

theorem rows_nonnegative_step (G Eta r : PTm n) (hRows : Γ ⊢[PRAAx] rowsNonnegative r (row G Eta r)) : Γ ⊢[PRAAx]
    rowsNonnegative (succ r) (row G Eta (succ r)) := by
  apply rows_nonnegative_intro
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowsNonnegative (Syn.shift r) (row (Syn.shift G) (Syn.shift Eta) (Syn.shift r)) := by
    simpa only [Fm.shift,subst_rowsNonnegative,subst_row,Syn.shift] using hRows.shift
  simpa only [Syn.shift,subst_row,ConciseIPRA.PTm.subst_succ] using
    new_entry_nonnegative (Syn.shift G) (Syn.shift Eta) (Syn.shift r) (var 0) hs.wk Prf.hyp0

/-- Genuine QF induction on the actual finite universal bit derives all
budget nonnegativity; it is never supplied as an incoming invariant. -/
theorem rows_nonnegative (G Eta r : PTm n) : Γ ⊢[PRAAx] rowsNonnegative r (row G Eta r) := by
  have all : Γ ⊢[PRAAx] .all (rowsNonnegative (var 0) (row (Syn.shift G) (Syn.shift Eta) (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_rowsNonnegative,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact BoundedReflection.allB_zero nonnegativeBody _
    · simp only [subst_rowsNonnegative,subst_row,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact rows_nonnegative_step _ _ _ Prf.hyp0
  simpa only [subst_rowsNonnegative,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem zero_fst : Γ ⊢[PRAAx] fstT (zero : PTm n) ≐ zero :=
  (congrFst (show Γ ⊢[PRAAx] zero ≐ pairT zero zero by unfold pairT; ipra_ring)).eqTrans (fst_pair zero zero)
theorem zero_snd : Γ ⊢[PRAAx] sndT (zero : PTm n) ≐ zero :=
  (congrSnd (show Γ ⊢[PRAAx] zero ≐ pairT zero zero by unfold pairT; ipra_ring)).eqTrans (snd_pair zero zero)
theorem default_fraction : Γ ⊢[PRAAx] decodeFraction (zero : PTm n) ≐ zeroCode :=
  fraction_congr zero_fst (congrSucc zero_snd)
theorem safeEntry_zero (i : PTm n) : Γ ⊢[PRAAx] safeEntry zero i ≐ zero :=
  safeEntry_absent _ _ (le_congr zero_fst.eqSymm (.eqRefl _) (zero_le _))
theorem safeEntry_congr {L L' i i' : PTm n} (hL : Γ ⊢[PRAAx] L ≐ L') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    safeEntry L i ≐ safeEntry L' i' := by
  ipra_congr (safeEntry (var 0) (var 1) : PTm 2) with [hL, hi]
theorem decode_congr {c d : PTm n} (h : Γ ⊢[PRAAx] c ≐ d) : Γ ⊢[PRAAx] decodeFraction c ≐ decodeFraction d :=
  fraction_congr (congrFst h) (congrSucc (congrSnd h))
theorem missing_row_weight (G v w : PTm n) (h : Γ ⊢[PRAAx] le (length G) v) : Γ ⊢[PRAAx]
    weight G v w ≐ zeroCode :=
  (decode_congr ((safeEntry_congr (safeEntry_absent G v h) (.eqRefl w)).eqTrans (safeEntry_zero w))).eqTrans default_fraction
theorem missing_edge_weight (G v w : PTm n) (h : Γ ⊢[PRAAx] le (length (graphRow G v)) w) : Γ ⊢[PRAAx]
    weight G v w ≐ zeroCode := (decode_congr (safeEntry_absent _ _ h)).eqTrans default_fraction
theorem missing_local_error (Eta v : PTm n) (h : Γ ⊢[PRAAx] le (length Eta) v) : Γ ⊢[PRAAx]
    localError Eta v ≐ zeroCode := (decode_congr (safeEntry_absent _ _ h)).eqTrans default_fraction

def outputF : PR 3 := PTm.toPR (row (var 0) (var 1) (var 2))
def run (G Eta N : PTm n) : PTm n := ap3 outputF G Eta N
def nodeF : PR 3 := PTm.toPR (node (var 0) (var 1) (var 2))
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (G Eta N : PTm n) :
    Syn.subst σ (run G Eta N) = run (Syn.subst σ G) (Syn.subst σ Eta) (Syn.subst σ N) := by
  simp only [run,ap3,ConciseIPRA.PTm.subst_app]
  congr 1; funext i; fin_cases i <;> rfl

theorem output_at (G Eta N : PTm n) : Γ ⊢[PRAAx] run G Eta N ≐ row G Eta N := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (row (var 0) (var 1) (var 2) : PTm 3) ![G,Eta,N]
theorem node_at (G Eta v : PTm n) : Γ ⊢[PRAAx] ap3 nodeF G Eta v ≐ node G Eta v := by
  simpa [nodeF,ap3] using toPR_eq (Γ := Γ) (node (var 0) (var 1) (var 2) : PTm 3) ![G,Eta,v]
theorem returned_length (G Eta N : PTm n) : Γ ⊢[PRAAx] length (run G Eta N) ≐ N :=
  (congrFst (output_at _ _ _)).eqTrans (row_length _ _ _)
theorem returned_lookup (G Eta N v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    entry (run G Eta N) v ≐ node G Eta v :=
  (entry_congr (output_at _ _ _) (.eqRefl _)).eqTrans (row_lookup _ _ _ _ hv)
theorem returned_nonnegative (G Eta N v : PTm n) (hv : Γ ⊢[PRAAx] lt v N) : Γ ⊢[PRAAx]
    rationalLE zeroCode (entry (run G Eta N) v) :=
  Analysis.RationalArgmin.rationalLE_congr (.eqRefl _) (entry_congr (output_at _ _ _) (.eqRefl _)).eqSymm
    (rows_nonnegative_at _ _ _ (rows_nonnegative _ _ _) hv)

theorem actual_rational_budget_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ row (var 0) (var 1) (var 2) ⋏
      length (run (var 0) (var 1) (var 2)) ≐ var 2) :=
  closeUniv 3 (.andI (output_at _ _ _) (returned_length _ _ _))
theorem actual_budget_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ entry (run (var 0) (var 1) (var 2)) (var 3) ≐ node (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (returned_lookup _ _ _ _ Prf.hyp0))
theorem actual_budget_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ entry (row (var 0) (var 1) (var 2)) (var 3) ≐
      add (localError (var 1) (var 3)) (incoming (var 0) (var 3) (row (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (final_recurrence _ _ _ _ Prf.hyp0))
theorem actual_budget_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ rationalLE zeroCode (entry (run (var 0) (var 1) (var 2)) (var 3))) :=
  closeUniv 4 (.impI (returned_nonnegative _ _ _ _ Prf.hyp0))
theorem actual_node_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 nodeF (var 0) (var 1) (var 2) ≐ node (var 0) (var 1) (var 2) ⋏
      ap3 weightF (var 0) (var 1) (var 2) ≐ weight (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.andI (node_at _ _ _) (weight_at _ _ _))
theorem guarded_missing_data_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (length (var 0)) (var 1) ⟶ weight (var 0) (var 1) (var 2) ≐ zeroCode) :=
  closeUniv 3 (.impI (missing_row_weight _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Foundations.PrecisionCostDAG
