import IPRADerivations.Foundations.FilteredEnumerationCode
import IPRADerivations.Foundations.RuntimeWordAppend
import IPRADerivations.Analysis.GaussianRationalPowerAlgebra

/-!
# Actual weighted monomial lists and evaluation vectors

The numerical label i*(L+1)+j implements the original loops with Y
exponent i outermost and X exponent j innermost. The actual filtered
enumerator retains exactly m*j+d*i<=L. Its returned labels are decoded
into stored exponent pairs; the evaluation vector reads those SAME pairs.
All counts, bounds, exponents and point codes are numerical. No symbolic
basis, coverage law, span or annihilator contract is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianWeightedMonomialBasis

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.RuntimeWordAppend (divide_spec divide_unique)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF power_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stride (L : PTm n) : PTm n := succ L
def label (L i j : PTm n) : PTm n := i*stride L+j
def horizon (m L : PTm n) : PTm n := m*stride L
def decodeY (L r : PTm n) : PTm n := quo r (stride L)
def decodeX (L r : PTm n) : PTm n := rem r (stride L)
def weight (m d i j : PTm n) : PTm n := m*j+d*i
def admissible (m d L i j : PTm n) : Fm PTm n := lt i m ⋏ le (weight m d i j) L
def data (m d L : PTm n) : PTm n := pairT m (pairT d L)
def keep (m d L r : PTm n) : PTm n := eqb (monus (weight m d (decodeY L r) (decodeX L r)) L) zero
def keepBody : PTm 2 := keep (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def count (m d L : PTm n) : PTm n := Foundations.FilteredEnumerationCode.count keepBody (horizon m L) (data m d L)
def labels (m d L : PTm n) : PTm n := Foundations.FilteredEnumerationCode.list keepBody (horizon m L) (data m d L)
def position (m d L i j : PTm n) : PTm n := Foundations.FilteredEnumeration.rank keepBody (label L i j) (data m d L)

@[simp] theorem subst_stride {l : ℕ} (σ : Fin n → PTm l) (L : PTm n) : Syn.subst σ (stride L) = stride (Syn.subst σ L) := by simp [stride]
@[simp] theorem subst_label {l : ℕ} (σ : Fin n → PTm l) (L i j : PTm n) :
    Syn.subst σ (label L i j) = label (Syn.subst σ L) (Syn.subst σ i) (Syn.subst σ j) := by simp [label]
@[simp] theorem subst_horizon {l : ℕ} (σ : Fin n → PTm l) (m L : PTm n) :
    Syn.subst σ (horizon m L) = horizon (Syn.subst σ m) (Syn.subst σ L) := by simp [horizon]
@[simp] theorem subst_decodeY {l : ℕ} (σ : Fin n → PTm l) (L r : PTm n) :
    Syn.subst σ (decodeY L r) = decodeY (Syn.subst σ L) (Syn.subst σ r) := by simp [decodeY]
@[simp] theorem subst_decodeX {l : ℕ} (σ : Fin n → PTm l) (L r : PTm n) :
    Syn.subst σ (decodeX L r) = decodeX (Syn.subst σ L) (Syn.subst σ r) := by simp [decodeX]
@[simp] theorem subst_weight {l : ℕ} (σ : Fin n → PTm l) (m d i j : PTm n) :
    Syn.subst σ (weight m d i j) = weight (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ i) (Syn.subst σ j) := by simp [weight]
@[simp] theorem subst_admissible {l : ℕ} (σ : Fin n → PTm l) (m d L i j : PTm n) :
    (admissible m d L i j).subst σ = admissible (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ i) (Syn.subst σ j) := by simp [admissible]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (m d L : PTm n) :
    Syn.subst σ (data m d L) = data (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [data]
@[simp] theorem subst_keep {l : ℕ} (σ : Fin n → PTm l) (m d L r : PTm n) :
    Syn.subst σ (keep m d L r) = keep (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ r) := by simp [keep]
@[simp] theorem subst_count {l : ℕ} (σ : Fin n → PTm l) (m d L : PTm n) :
    Syn.subst σ (count m d L) = count (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [count]
@[simp] theorem subst_labels {l : ℕ} (σ : Fin n → PTm l) (m d L : PTm n) :
    Syn.subst σ (labels m d L) = labels (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [labels]
@[simp] theorem subst_position {l : ℕ} (σ : Fin n → PTm l) (m d L i j : PTm n) :
    Syn.subst σ (position m d L i j) = position (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ i) (Syn.subst σ j) := by
  simp [position,Foundations.FilteredEnumeration.rank]

theorem keep_congr {m m' d d' L L' r r' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hd : Γ ⊢[PRAAx] d ≐ d') (hL : Γ ⊢[PRAAx] L ≐ L') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    keep m d L r ≐ keep m' d' L' r' := by
  simpa using Prf.eqCongr (Γ := Γ) (keep (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![m,d,L,r]) (σ' := ![m',d',L',r']) (fun k => by fin_cases k; exact hm; exact hd; exact hL; exact hr)
theorem keep_body_at (m d L r : PTm n) : Γ ⊢[PRAAx] inst2 keepBody r (data m d L) ≐ keep m d L r := by
  simp only [keepBody,inst2,subst_keep,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact keep_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem keep_one (m d L r : PTm n) (h : Γ ⊢[PRAAx] le (weight m d (decodeY L r) (decodeX L r)) L) : Γ ⊢[PRAAx]
    keep m d L r ≐ one := eqb_of_eq h
theorem keep_bound (m d L r : PTm n) (h : Γ ⊢[PRAAx] neg (keep m d L r ≐ zero)) : Γ ⊢[PRAAx]
    le (weight m d (decodeY L r) (decodeX L r)) L := AnalyticNumberTheory.Valuation.eq_of_eqb_ne h
theorem label_decode (L r : PTm n) : Γ ⊢[PRAAx] label L (decodeY L r) (decodeX L r) ≐ r :=
  ((congrAdd (mul_comm _ _) (.eqRefl _)).eqTrans (Prf.andE₁ (divide_spec (stride L) r (zero_lt_succ L))).eqSymm)
theorem decode_label (L i j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    (decodeY L (label L i j) ≐ i) ⋏ (decodeX L (label L i j) ≐ j) :=
  divide_unique (stride L) (label L i j) i j (zero_lt_succ L) (by unfold label; ipra_ring)
    ((succ_monus_succ _ _).eqTrans hj)
theorem label_bound (m L i j : PTm n) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    lt (label L i j) (horizon m L) :=
  lt_congr (add_comm _ _) (mul_comm _ _) (Foundations.MixedRadixExpansion.append_interval
    ((succ_monus_succ _ _).eqTrans hj) hi)
theorem decode_bounds (m L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (horizon m L)) : Γ ⊢[PRAAx]
    lt (decodeY L r) m ⋏ le (decodeX L r) L := by
  have spec := divide_spec (Γ := Γ) (stride L) r (zero_lt_succ L)
  refine .andI ?_ ((succ_monus_succ _ _).eqSymm.eqTrans (.andE₂ spec))
  refine .orE (lt_or_le (decodeY L r) m) Prf.hyp0 ?_
  have mul : (le m (decodeY L r)) :: Γ ⊢[PRAAx] le (horizon m L) (decodeY L r*stride L) :=
    AnalyticNumberTheory.PhiLower.le_mul_mono Prf.hyp0 (le_refl _)
  have bound : (le m (decodeY L r)) :: Γ ⊢[PRAAx] le (horizon m L) r :=
    le_trans mul (le_congr (.eqRefl _) (label_decode L r) (le_add_right _ _))
  exact .botE _ (le_lt_absurd _ bound hr.wk)
theorem admissible_x_bound (m d L i j : PTm n) (h : Γ ⊢[PRAAx] admissible m d L i j) : Γ ⊢[PRAAx] le j L := by
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le i) (.andE₁ h)
  have mul := le_congr (one_mul j) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono hm (le_refl j))
  exact le_trans (le_trans mul (le_add_right _ _)) (.andE₂ h)
theorem label_keep (m d L i j : PTm n) (h : Γ ⊢[PRAAx] admissible m d L i j) : Γ ⊢[PRAAx]
    keep m d L (label L i j) ≐ one := by
  have dec := decode_label L i j (admissible_x_bound _ _ _ _ _ h)
  have weightEq : Γ ⊢[PRAAx] weight m d (decodeY L (label L i j)) (decodeX L (label L i j)) ≐ weight m d i j :=
    congrAdd (congrMul (.eqRefl _) (.andE₂ dec)) (congrMul (.eqRefl _) (.andE₁ dec))
  exact keep_one _ _ _ _ (le_congr weightEq.eqSymm (.eqRefl _) (.andE₂ h))
theorem labels_length (m d L : PTm n) : Γ ⊢[PRAAx] length (labels m d L) ≐ count m d L :=
  Foundations.FilteredEnumerationCode.list_length _ _ _
theorem labels_bound (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    lt (entry (labels m d L) r) (horizon m L) := Foundations.FilteredEnumerationCode.entry_bound _ _ _ _ hr
theorem labels_admissible (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    admissible m d L (decodeY L (entry (labels m d L) r)) (decodeX L (entry (labels m d L) r)) := by
  have valid := Foundations.FilteredEnumerationCode.entry_valid keepBody (horizon m L) (data m d L) r hr
  have nonzero : Γ ⊢[PRAAx] neg (keep m d L (entry (labels m d L) r) ≐ zero) :=
    .impI (.impE valid.wk ((keep_body_at _ _ _ _).wk.eqTrans Prf.hyp0))
  exact .andI (.andE₁ (decode_bounds m L _ (labels_bound _ _ _ _ hr))) (keep_bound _ _ _ _ nonzero)
theorem listed_label (m d L i j : PTm n) (h : Γ ⊢[PRAAx] admissible m d L i j) : Γ ⊢[PRAAx]
    lt (position m d L i j) (count m d L) ⋏ entry (labels m d L) (position m d L i j) ≐ label L i j :=
  Foundations.FilteredEnumerationCode.listed keepBody (horizon m L) (data m d L) (label L i j)
    (label_bound m L i j (.andE₁ h) (admissible_x_bound _ _ _ _ _ h))
    (.impI (succ_ne_zero (((keep_body_at _ _ _ _).eqTrans (label_keep _ _ _ _ _ h)).wk.eqSymm.eqTrans Prf.hyp0)))

theorem label_rank (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    Foundations.FilteredEnumeration.rank keepBody (entry (labels m d L) r) (data m d L) ≐ r :=
  (congrAp2 (sumF (Foundations.BoundedReflection.sgB keepBody))
    (Foundations.FilteredEnumerationCode.list_lookup _ _ _ _ hr) (.eqRefl _)).eqTrans
      (.andE₂ (.andE₂ (Foundations.FilteredEnumeration.sel_spec keepBody hr)))
theorem count_bound (m d L : PTm n) : Γ ⊢[PRAAx] le (count m d L) (horizon m L) :=
  Foundations.FilteredEnumerationCode.count_le _ _ _
theorem count_zero (d L : PTm n) : Γ ⊢[PRAAx] count zero d L ≐ zero :=
  le_antisymm (le_congr (.eqRefl _) (by unfold horizon; ipra_ring) (count_bound zero d L)) (zero_le _)
theorem constant_admissible (m d L : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] admissible m d L zero zero :=
  .andI hm (le_congr (by unfold weight; ipra_ring) (.eqRefl _) (zero_le L))
theorem constant_position (m d L : PTm n) : Γ ⊢[PRAAx] position m d L zero zero ≐ zero :=
  (congrAp2 (sumF (Foundations.BoundedReflection.sgB keepBody)) (by unfold label; ipra_ring) (.eqRefl _)).eqTrans
    (Foundations.FilteredEnumeration.rank_zero _ _)
theorem count_positive (m d L : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] le one (count m d L) :=
  lt_congr (constant_position _ _ _) (.eqRefl _) (.andE₁ (listed_label _ _ _ _ _ (constant_admissible _ _ _ hm)))

def basisPair (m d L r : PTm n) : PTm n := pairT (decodeY L (entry (labels m d L) r)) (decodeX L (entry (labels m d L) r))
def basisBody : PTm 2 := basisPair (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def basis (m d L : PTm n) : PTm n := sequence basisBody (count m d L) (data m d L)
@[simp] theorem subst_basisPair {l : ℕ} (σ : Fin n → PTm l) (m d L r : PTm n) :
    Syn.subst σ (basisPair m d L r) = basisPair (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ r) := by simp [basisPair]
@[simp] theorem subst_basis {l : ℕ} (σ : Fin n → PTm l) (m d L : PTm n) :
    Syn.subst σ (basis m d L) = basis (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [basis]
theorem basis_pair_congr {m m' d d' L L' r r' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hd : Γ ⊢[PRAAx] d ≐ d') (hL : Γ ⊢[PRAAx] L ≐ L') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    basisPair m d L r ≐ basisPair m' d' L' r' := by
  simpa using Prf.eqCongr (Γ := Γ) (basisPair (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![m,d,L,r]) (σ' := ![m',d',L',r']) (fun k => by fin_cases k; exact hm; exact hd; exact hL; exact hr)
theorem basis_body_at (m d L r : PTm n) : Γ ⊢[PRAAx] inst2 basisBody r (data m d L) ≐ basisPair m d L r := by
  simp only [basisBody,inst2,subst_basisPair,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact basis_pair_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem basis_length (m d L : PTm n) : Γ ⊢[PRAAx] length (basis m d L) ≐ count m d L := sequence_length _ _ _
theorem basis_lookup (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    entry (basis m d L) r ≐ basisPair m d L r :=
  (sequence_decode basisBody hr).eqTrans (basis_body_at _ _ _ _)
theorem basis_Y (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    fstT (entry (basis m d L) r) ≐ decodeY L (entry (labels m d L) r) :=
  (congrFst (basis_lookup _ _ _ _ hr)).eqTrans (fst_pair _ _)
theorem basis_X (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    sndT (entry (basis m d L) r) ≐ decodeX L (entry (labels m d L) r) :=
  (congrSnd (basis_lookup _ _ _ _ hr)).eqTrans (snd_pair _ _)
theorem basis_admissible (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    admissible m d L (fstT (entry (basis m d L) r)) (sndT (entry (basis m d L) r)) := by
  have h := labels_admissible _ _ _ _ hr
  exact .andI (lt_congr (basis_Y _ _ _ _ hr).eqSymm (.eqRefl _) (.andE₁ h))
    (le_congr (congrAdd (congrMul (.eqRefl _) (basis_X _ _ _ _ hr))
      (congrMul (.eqRefl _) (basis_Y _ _ _ _ hr))).eqSymm (.eqRefl _) (.andE₂ h))
theorem listed_basis (m d L i j : PTm n) (h : Γ ⊢[PRAAx] admissible m d L i j) : Γ ⊢[PRAAx]
    lt (position m d L i j) (count m d L) ⋏ entry (basis m d L) (position m d L i j) ≐ pairT i j := by
  have labels := listed_label _ _ _ _ _ h
  have dec := decode_label L i j (admissible_x_bound _ _ _ _ _ h)
  exact .andI (.andE₁ labels) ((basis_lookup _ _ _ _ (.andE₁ labels)).eqTrans
    (congrPairT ((congrAp2 quoF (.andE₂ labels) (.eqRefl _)).eqTrans (.andE₁ dec))
      ((congrAp2 remF (.andE₂ labels) (.eqRefl _)).eqTrans (.andE₂ dec))))
theorem basis_constant (m d L : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    entry (basis m d L) zero ≐ pairT zero zero :=
  (entry_congr (.eqRefl _) (constant_position m d L).eqSymm).eqTrans
    (.andE₂ (listed_basis _ _ _ _ _ (constant_admissible _ _ _ hm)))
theorem basis_position (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    position m d L (fstT (entry (basis m d L) r)) (sndT (entry (basis m d L) r)) ≐ r :=
  (congrAp2 (sumF (Foundations.BoundedReflection.sgB keepBody))
    ((congrAdd (congrMul (basis_Y _ _ _ _ hr) (.eqRefl _)) (basis_X _ _ _ _ hr)).eqTrans (label_decode _ _)) (.eqRefl _)).eqTrans
      (label_rank _ _ _ _ hr)

/-- Numerical labels increase in precisely the source loop order. -/
theorem earlier_Y (L i j k l : PTm n) (hik : Γ ⊢[PRAAx] lt i k) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    lt (label L i j) (label L k l) := lt_of_lt_of_le (label_bound k L i j hik hj) (le_add_right _ _)
theorem cancel_common_lt (C a b : PTm n) (h : Γ ⊢[PRAAx] lt (C+a) (C+b)) : Γ ⊢[PRAAx] lt a b := by
  have e : Γ ⊢[PRAAx] monus (succ a+C) (b+C) ≐ zero :=
    (congrMonus (by ipra_ring : Γ ⊢[PRAAx] succ (C+a) ≐ succ a+C) (add_comm C b)).eqSymm.eqTrans h
  exact (monus_add_add _ _ _).eqSymm.eqTrans e
theorem labels_lex (L u v : PTm n) (h : Γ ⊢[PRAAx] lt u v) : Γ ⊢[PRAAx]
    lt (decodeY L u) (decodeY L v) ⋎
      ((decodeY L u ≐ decodeY L v) ⋏ lt (decodeX L u) (decodeX L v)) := by
  have sv := divide_spec (Γ := Γ) (stride L) v (zero_lt_succ L)
  refine .orE (lt_or_le (decodeY L u) (decodeY L v)) (.orI₁ Prf.hyp0) ?_
  refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
  · have rev := earlier_Y (Γ := (lt (decodeY L v) (decodeY L u)) :: (le (decodeY L v) (decodeY L u)) :: Γ)
      L (decodeY L v) (decodeX L v) (decodeY L u) (decodeX L u) Prf.hyp0
      ((succ_monus_succ _ _).eqSymm.eqTrans (.andE₂ sv.wk.wk))
    exact .botE _ (lt_irrefl u _ (lt_of_lt_of_le h.wk.wk (le_of_lt (lt_congr (label_decode L v) (label_decode L u) rev))))
  · have order : (decodeY L v ≐ decodeY L u) :: (le (decodeY L v) (decodeY L u)) :: Γ ⊢[PRAAx]
        lt (label L (decodeY L u) (decodeX L u)) (label L (decodeY L v) (decodeX L v)) :=
      lt_congr (label_decode L u).eqSymm (label_decode L v).eqSymm h.wk.wk
    have same : (decodeY L v ≐ decodeY L u) :: (le (decodeY L v) (decodeY L u)) :: Γ ⊢[PRAAx]
        lt (decodeY L v*stride L+decodeX L u) (decodeY L v*stride L+decodeX L v) :=
      lt_congr (congrAdd (congrMul Prf.hyp0.eqSymm (.eqRefl _)) (.eqRefl _)) (.eqRefl _) order
    exact .orI₂ (.andI Prf.hyp0.eqSymm (cancel_common_lt _ _ _ same))
def lexBefore (p q : PTm n) : Fm PTm n := lt (fstT p) (fstT q) ⋎ ((fstT p ≐ fstT q) ⋏ lt (sndT p) (sndT q))
@[simp] theorem subst_lexBefore {l : ℕ} (σ : Fin n → PTm l) (p q : PTm n) :
    (lexBefore p q).subst σ = lexBefore (Syn.subst σ p) (Syn.subst σ q) := by simp [lexBefore]
theorem basis_increasing (m d L r s : PTm n) (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s (count m d L)) : Γ ⊢[PRAAx]
    lexBefore (entry (basis m d L) r) (entry (basis m d L) s) := by
  have hr := lt_of_lt_of_le hrs (le_of_lt hs)
  have order := labels_lex L _ _ (Foundations.FilteredEnumerationCode.increasing keepBody _ _ _ _ hrs hs)
  refine .orE order ?_ ?_
  · exact .orI₁ (lt_congr (basis_Y _ _ _ _ hr.wk).eqSymm (basis_Y _ _ _ _ hs.wk).eqSymm Prf.hyp0)
  · exact .orI₂ (.andI ((basis_Y _ _ _ _ hr.wk).eqTrans ((Prf.andE₁ Prf.hyp0).eqTrans (basis_Y _ _ _ _ hs.wk).eqSymm))
      (lt_congr (basis_X _ _ _ _ hr.wk).eqSymm (basis_X _ _ _ _ hs.wk).eqSymm (.andE₂ Prf.hyp0)))
theorem basis_distinct (m d L r s : PTm n) (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s (count m d L)) : Γ ⊢[PRAAx]
    neg (entry (basis m d L) r ≐ entry (basis m d L) s) := by
  refine .impI (.orE (basis_increasing m d L r s hrs hs).wk ?_ ?_)
  · exact lt_irrefl _ _ (lt_congr (congrFst Prf.hyp1) (.eqRefl _) Prf.hyp0)
  · exact lt_irrefl _ _ (lt_congr (congrSnd Prf.hyp1) (.eqRefl _) (.andE₂ Prf.hyp0))
theorem admissible_of_basis_pair (m d L r i j : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L))
    (hp : Γ ⊢[PRAAx] entry (basis m d L) r ≐ pairT i j) : Γ ⊢[PRAAx] admissible m d L i j := by
  have valid := basis_admissible m d L r hr
  have ey := (congrFst hp).eqTrans (fst_pair _ _)
  have ex := (congrSnd hp).eqTrans (snd_pair _ _)
  exact .andI (lt_congr ey (.eqRefl _) (.andE₁ valid))
    (le_congr (congrAdd (congrMul (.eqRefl _) ex) (congrMul (.eqRefl _) ey)) (.eqRefl _) (.andE₂ valid))
def occurs (m d L i j : PTm n) : Fm PTm n := .ex (lt (var 0) (count (Syn.shift m) (Syn.shift d) (Syn.shift L)) ⋏
  entry (basis (Syn.shift m) (Syn.shift d) (Syn.shift L)) (var 0) ≐ pairT (Syn.shift i) (Syn.shift j))
@[simp] theorem subst_occurs {l : ℕ} (σ : Fin n → PTm l) (m d L i j : PTm n) :
    (occurs m d L i j).subst σ = occurs (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ i) (Syn.subst σ j) := by
  simp [occurs,Syn.subst_shift,Syn.shift_subst]
theorem complete (m d L i j : PTm n) (h : Γ ⊢[PRAAx] admissible m d L i j) : Γ ⊢[PRAAx] occurs m d L i j := by
  refine .exI (position m d L i j) ?_
  simpa [occurs] using listed_basis m d L i j h
theorem occurs_admissible (m d L i j : PTm n) (h : Γ ⊢[PRAAx] occurs m d L i j) : Γ ⊢[PRAAx] admissible m d L i j := by
  refine .exE h ?_
  let Δ := (lt (var 0) (count (Syn.shift m) (Syn.shift d) (Syn.shift L)) ⋏ entry (basis (Syn.shift m) (Syn.shift d) (Syn.shift L)) (var 0) ≐
    pairT (Syn.shift i) (Syn.shift j)) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 0) (count (Syn.shift m) (Syn.shift d) (Syn.shift L)) := by
    simpa only [Δ,Syn.shift,subst_count] using (Prf.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] _))
  have hp : Δ ⊢[PRAAx] entry (basis (Syn.shift m) (Syn.shift d) (Syn.shift L)) (var 0) ≐ pairT (Syn.shift i) (Syn.shift j) := by
    simpa only [Δ,Syn.shift,subst_basis] using (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _))
  simpa only [Δ,Fm.shift,subst_admissible,Syn.shift] using
    admissible_of_basis_pair (Syn.shift m) (Syn.shift d) (Syn.shift L) (var 0) (Syn.shift i) (Syn.shift j) hr hp
theorem coverage (m d L i j : PTm n) : Γ ⊢[PRAAx] Fm.iff (admissible m d L i j) (occurs m d L i j) :=
  .andI (.impI (complete _ _ _ _ _ Prf.hyp0)) (.impI (occurs_admissible _ _ _ _ _ Prf.hyp0))

def monomial (x y p : PTm n) : PTm n := qmul (power x (sndT p)) (power y (fstT p))
def valueAt (m d L x y r : PTm n) : PTm n := monomial x y (entry (basis m d L) r)
def evaluationData (m d L x y : PTm n) : PTm n := pairT (data m d L) (pairT x y)
def evaluationBody : PTm 2 := valueAt (fstT (fstT (var 1))) (fstT (sndT (fstT (var 1))))
  (sndT (sndT (fstT (var 1)))) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def evaluationVector (m d L x y : PTm n) : PTm n := sequence evaluationBody (count m d L) (evaluationData m d L x y)
@[simp] theorem subst_monomial {l : ℕ} (σ : Fin n → PTm l) (x y p : PTm n) :
    Syn.subst σ (monomial x y p) = monomial (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ p) := by simp [monomial]
@[simp] theorem subst_valueAt {l : ℕ} (σ : Fin n → PTm l) (m d L x y r : PTm n) :
    Syn.subst σ (valueAt m d L x y r) = valueAt (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L)
      (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ r) := by simp [valueAt]
@[simp] theorem subst_evaluationData {l : ℕ} (σ : Fin n → PTm l) (m d L x y : PTm n) :
    Syn.subst σ (evaluationData m d L x y) = evaluationData (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L)
      (Syn.subst σ x) (Syn.subst σ y) := by simp [evaluationData]
@[simp] theorem subst_evaluationVector {l : ℕ} (σ : Fin n → PTm l) (m d L x y : PTm n) :
    Syn.subst σ (evaluationVector m d L x y) = evaluationVector (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L)
      (Syn.subst σ x) (Syn.subst σ y) := by simp [evaluationVector]
theorem value_congr {m m' d d' L L' x x' y y' r r' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hd : Γ ⊢[PRAAx] d ≐ d') (hL : Γ ⊢[PRAAx] L ≐ L') (hx : Γ ⊢[PRAAx] x ≐ x')
    (hy : Γ ⊢[PRAAx] y ≐ y') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    valueAt m d L x y r ≐ valueAt m' d' L' x' y' r' := by
  simpa using Prf.eqCongr (Γ := Γ) (valueAt (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![m,d,L,x,y,r]) (σ' := ![m',d',L',x',y',r'])
    (fun k => by fin_cases k; exact hm; exact hd; exact hL; exact hx; exact hy; exact hr)
theorem evaluation_body_at (m d L x y r : PTm n) : Γ ⊢[PRAAx]
    inst2 evaluationBody r (evaluationData m d L x y) ≐ valueAt m d L x y r := by
  have head := fst_pair (Γ := Γ) (data m d L) (pairT x y)
  have rest := (congrSnd head).eqTrans (snd_pair m (pairT d L))
  have tail := snd_pair (Γ := Γ) (data m d L) (pairT x y)
  simp only [evaluationBody,inst2,subst_valueAt,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact value_congr ((congrFst head).eqTrans (fst_pair _ _)) ((congrFst rest).eqTrans (fst_pair _ _))
    ((congrSnd rest).eqTrans (snd_pair _ _)) ((congrFst tail).eqTrans (fst_pair _ _))
      ((congrSnd tail).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem evaluation_length (m d L x y : PTm n) : Γ ⊢[PRAAx] length (evaluationVector m d L x y) ≐ count m d L := sequence_length _ _ _
theorem evaluation_lookup (m d L x y r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    entry (evaluationVector m d L x y) r ≐ monomial x y (entry (basis m d L) r) :=
  (sequence_decode evaluationBody hr).eqTrans (evaluation_body_at _ _ _ _ _ _)
theorem evaluation_canonical_at (m d L x y r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    canonical (entry (evaluationVector m d L x y) r) :=
  GaussianRationalHorner.canonical_congr (evaluation_lookup _ _ _ _ _ _ hr) (GaussianRationalHorner.qmul_canonical _ _)
theorem evaluation_listed (m d L i j x y : PTm n) (h : Γ ⊢[PRAAx] admissible m d L i j) : Γ ⊢[PRAAx]
    entry (evaluationVector m d L x y) (position m d L i j) ≐ qmul (power x j) (power y i) := by
  have listed := listed_basis _ _ _ _ _ h
  exact (evaluation_lookup _ _ _ _ _ _ (.andE₁ listed)).eqTrans
    (qmul_congr (congrAp2 powerF ((congrSnd (.andE₂ listed)).eqTrans (snd_pair _ _)) (.eqRefl _))
      (congrAp2 powerF ((congrFst (.andE₂ listed)).eqTrans (fst_pair _ _)) (.eqRefl _)))
theorem evaluation_constant (m d L x y : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    entry (evaluationVector m d L x y) zero ≐ qone :=
  (entry_congr (.eqRefl _) (constant_position m d L).eqSymm).eqTrans
    ((evaluation_listed _ _ _ _ _ _ _ (constant_admissible _ _ _ hm)).eqTrans
      ((qmul_congr (power_zero _) (power_zero _)).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ GaussianRationalSyntheticDivision.qone_canonical)))

def output (m d L x y : PTm n) : PTm n := pairT (basis m d L)
  (pairT (evaluationVector m d L x y) (pairT (count m d L) (labels m d L)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (m d L x y : PTm n) : PTm n := app outputF ![m,d,L,x,y]
def fields (p : PTm n) (i : Fin 4) : PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))] i
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (m d L x y : PTm n) :
    Syn.subst σ (output m d L x y) = output (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ y) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (m d L x y : PTm n) :
    Syn.subst σ (run m d L x y) = run (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ y) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (m d L x y : PTm n) : Γ ⊢[PRAAx] run m d L x y ≐ output m d L x y := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![m,d,L,x,y]
theorem returned_fields (m d L x y : PTm n) (i : Fin 4) : Γ ⊢[PRAAx]
    fields (run m d L x y) i ≐ ![basis m d L,evaluationVector m d L x y,count m d L,labels m d L] i := by
  have e0 := program_at (Γ := Γ) m d L x y
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  have e3 := (congrSnd e2).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact e3
theorem returned_lengths (m d L x y : PTm n) : Γ ⊢[PRAAx]
    (length (fields (run m d L x y) 0) ≐ fields (run m d L x y) 2) ⋏
      (length (fields (run m d L x y) 1) ≐ fields (run m d L x y) 2) :=
  .andI ((congrFst (returned_fields _ _ _ _ _ 0)).eqTrans ((basis_length _ _ _).eqTrans (returned_fields _ _ _ _ _ 2).eqSymm))
    ((congrFst (returned_fields _ _ _ _ _ 1)).eqTrans ((evaluation_length _ _ _ _ _).eqTrans (returned_fields _ _ _ _ _ 2).eqSymm))

/-! Original bounds, exponent pairs, list positions and point codes are
all bound internally. The constant requires only positive m. -/
theorem actual_decode_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (horizon (var 0) (var 1)) ⟶
      (lt (decodeY (var 1) (var 2)) (var 0) ⋏ le (decodeX (var 1) (var 2)) (var 1))) :=
  closeUniv 3 (.impI (decode_bounds _ _ _ Prf.hyp0))
theorem actual_admissible_x_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (admissible (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (var 4) (var 2)) :=
  closeUniv 5 (.impI (admissible_x_bound _ _ _ _ _ Prf.hyp0))
theorem actual_listed_basis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (admissible (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (lt (position (var 0) (var 1) (var 2) (var 3) (var 4)) (count (var 0) (var 1) (var 2)) ⋏
        entry (basis (var 0) (var 1) (var 2)) (position (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ pairT (var 3) (var 4))) :=
  closeUniv 5 (.impI (listed_basis _ _ _ _ _ Prf.hyp0))
theorem actual_basis_sound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (count (var 0) (var 1) (var 2)) ⟶
      admissible (var 0) (var 1) (var 2) (fstT (entry (basis (var 0) (var 1) (var 2)) (var 3)))
        (sndT (entry (basis (var 0) (var 1) (var 2)) (var 3)))) :=
  closeUniv 4 (.impI (basis_admissible _ _ _ _ Prf.hyp0))
theorem actual_basis_coverage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (admissible (var 0) (var 1) (var 2) (var 3) (var 4)) (occurs (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (coverage _ _ _ _ _)
theorem actual_basis_rank_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (count (var 0) (var 1) (var 2)) ⟶
      position (var 0) (var 1) (var 2) (fstT (entry (basis (var 0) (var 1) (var 2)) (var 3)))
        (sndT (entry (basis (var 0) (var 1) (var 2)) (var 3))) ≐ var 3) :=
  closeUniv 4 (.impI (basis_position _ _ _ _ Prf.hyp0))
theorem actual_basis_lex_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 4) ⟶ lt (var 4) (count (var 0) (var 1) (var 2)) ⟶
      lexBefore (entry (basis (var 0) (var 1) (var 2)) (var 3)) (entry (basis (var 0) (var 1) (var 2)) (var 4))) :=
  closeUniv 5 (.impI (.impI (basis_increasing _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_constant_monomial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ (le one (count (var 0) (var 1) (var 2)) ⋏
      ((entry (basis (var 0) (var 1) (var 2)) zero ≐ pairT zero zero) ⋏
        (entry (evaluationVector (var 0) (var 1) (var 2) (var 3) (var 4)) zero ≐ qone)))) :=
  closeUniv 5 (.impI (.andI (count_positive _ _ _ Prf.hyp0)
    (.andI (basis_constant _ _ _ Prf.hyp0) (evaluation_constant _ _ _ _ _ Prf.hyp0))))
theorem actual_listed_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (admissible (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      entry (evaluationVector (var 0) (var 1) (var 2) (var 5) (var 6)) (position (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
        qmul (power (var 5) (var 4)) (power (var 6) (var 3))) :=
  closeUniv 7 (.impI (evaluation_listed _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_empty_basis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (basis zero (var 0) (var 1)) ≐ zero) ⋏
      (length (evaluationVector zero (var 0) (var 1) (var 2) (var 3)) ≐ zero)) :=
  closeUniv 4 (.andI ((basis_length _ _ _).eqTrans (count_zero _ _)) ((evaluation_length _ _ _ _ _).eqTrans (count_zero _ _)))
theorem actual_basis_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((length (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 0) ≐ fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 2) ⋏
        (length (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 1) ≐ fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 2))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (returned_lengths _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianWeightedMonomialBasis
