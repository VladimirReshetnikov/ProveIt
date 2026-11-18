import IPRADerivations.Analysis.RationalHausdorffConcat
import IPRADerivations.Analysis.RationalNearest
import IPRADerivations.Foundations.FiniteHausdorffProduct

/-!
# Actual Cartesian products of original rational-vector lists

Finite-demand `lem:aggregate-calculus`, clause 3. Each Cartesian entry is
an actual append of its two rational coordinate vectors. Both dimensions,
all list lengths and every index are internal. The explicit point-shape
guards identify the append boundary with the first runtime dimension.
The output uses its own normalization pool; independently scaled Hausdorff
numerators are compared only after exact original-coordinate cover transport.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalHausdorffProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalHausdorff
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf rationalNumerator rationalDenominator)
open LeanProofs.IPRA.Analysis.RationalHausdorffConcat
  (maximumNumerator maximumDenominator maximum_left_bound maximum_right_bound pointRadius_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length subst_length entry_congr append subst_append append_length append_left append_right_at)
open LeanProofs.IPRA.Foundations.FiniteHausdorffConcat (suffix_range)
open LeanProofs.IPRA.Foundations.FiniteHausdorffProduct (pairIndex pair_index_range pair_index_decode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shaped (S d : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift S)) ⟶ length (entry (Syn.shift S) (var 0)) ≐ Syn.shift d)

@[simp] theorem subst_shaped {m : ℕ} (σ : Fin n → PTm m) (S d : PTm n) :
    (shaped S d).subst σ = shaped (Syn.subst σ S) (Syn.subst σ d) := by
  simp only [shaped,Fm.subst_all,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_length,subst_entry,
    Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

theorem shaped_at (S d i : PTm n) (h : Γ ⊢[PRAAx] shaped S d)
    (hi : Γ ⊢[PRAAx] lt i (length S)) : Γ ⊢[PRAAx] length (entry S i) ≐ d := by
  have r : Γ ⊢[PRAAx] lt i (length S) ⟶ length (entry S i) ≐ d := by
    simpa only [shaped,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_length,subst_entry,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE i h
  exact .impE r hi

def productValue (S S' i : PTm n) : PTm n :=
  append (entry S (quo i (length S'))) (entry S' (rem i (length S')))
def productBody : PTm 2 := productValue (fstT (var 1)) (sndT (var 1)) (var 0)
def product (S S' : PTm n) : PTm n := sequence productBody (length S*length S') (pairT S S')
def productF : PR 2 := PTm.toPR (product (var 0) (var 1))

@[simp] theorem subst_productValue {m : ℕ} (σ : Fin n → PTm m) (S S' i : PTm n) :
    Syn.subst σ (productValue S S' i) = productValue (Syn.subst σ S) (Syn.subst σ S') (Syn.subst σ i) := by
  simp only [productValue,subst_append,subst_entry,subst_ap2,subst_length]
@[simp] theorem subst_product {m : ℕ} (σ : Fin n → PTm m) (S S' : PTm n) :
    Syn.subst σ (product S S') = product (Syn.subst σ S) (Syn.subst σ S') := by
  simp only [product,subst_sequence,PTm.subst_mul,subst_length,subst_pairT]

theorem product_length (S S' : PTm n) : Γ ⊢[PRAAx] length (product S S') ≐ length S*length S' := sequence_length _ _ _

theorem product_at (S S' : PTm n) : Γ ⊢[PRAAx] ap2 productF S S' ≐ product S S' := by
  simpa only [productF,ap2,subst_product,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (product (var 0) (var 1) : PTm 2) ![S,S']

theorem product_body_at (S S' i : PTm n) : Γ ⊢[PRAAx] inst2 productBody i (pairT S S') ≐ productValue S S' i := by
  have h := Prf.eqCongr (Γ := Γ) (productValue (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT S S'),sndT (pairT S S'),i]) (σ' := ![S,S',i])
    (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)
  simpa only [inst2,productBody,subst_productValue,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h

theorem product_lookup (S S' i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (product S S'))) :
    Γ ⊢[PRAAx] entry (product S S') i ≐ productValue S S' i :=
  (sequence_decode productBody (lt_congr (.eqRefl _) (product_length S S') hi)).eqTrans (product_body_at S S' i)

theorem product_indices (S S' i : PTm n) (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hi : Γ ⊢[PRAAx] lt i (length (product S S'))) :
    Γ ⊢[PRAAx] lt (quo i (length S')) (length S) ⋏ lt (rem i (length S')) (length S') :=
  Foundations.FiniteHausdorffProduct.product_indices hS'
    (lt_congr (.eqRefl _) ((product_length S S').eqTrans (Foundations.FiniteHausdorffProduct.product_length S S').eqSymm) hi)

theorem product_pair_range (T T' j l : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T)) (hl : Γ ⊢[PRAAx] lt l (length T')) :
    Γ ⊢[PRAAx] lt (pairIndex T' j l) (length (product T T')) :=
  lt_congr (.eqRefl _) ((Foundations.FiniteHausdorffProduct.product_length T T').eqTrans (product_length T T').eqSymm)
    (pair_index_range hj hl)

theorem append_congr {x x' y y' : PTm n} (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] append x y ≐ append x' y' := by
  have h := Prf.eqCongr (Γ := Γ) (append (var 0) (var 1) : PTm 2)
    (σ := ![x,y]) (σ' := ![x',y']) (fun i => by fin_cases i; exact hx; exact hy)
  simpa only [subst_append,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem product_pair_entry (T T' j l : PTm n) (hT' : Γ ⊢[PRAAx] le one (length T'))
    (hj : Γ ⊢[PRAAx] lt j (length T)) (hl : Γ ⊢[PRAAx] lt l (length T')) :
    Γ ⊢[PRAAx] entry (product T T') (pairIndex T' j l) ≐ append (entry T j) (entry T' l) := by
  have dec := pair_index_decode (j := j) hT' hl
  exact (product_lookup T T' _ (product_pair_range T T' j l hj hl)).eqTrans
    (append_congr (entry_congr (.eqRefl _) (Prf.andE₁ dec)) (entry_congr (.eqRefl _) (Prf.andE₂ dec)))

/-- Transport through actual coordinate entries, allowing different indices. -/
theorem coordinate_from_entries (x y u v k l A B : PTm n)
    (hx : Γ ⊢[PRAAx] entry x k ≐ entry u l) (hy : Γ ⊢[PRAAx] entry y k ≐ entry v l)
    (h : Γ ⊢[PRAAx] coordinateRadius u v l A B) : Γ ⊢[PRAAx] coordinateRadius x y k A B := by
  have nx : ZT.toZ Γ (rationalNumerator x k) = ZT.toZ Γ (rationalNumerator u l) := by
    simp only [rationalNumerator,numeratorOf,ZT.toZ]
    rw [natEq (congrFst (congrFst hx)),natEq (congrSnd (congrFst hx))]
  have ny : ZT.toZ Γ (rationalNumerator y k) = ZT.toZ Γ (rationalNumerator v l) := by
    simp only [rationalNumerator,numeratorOf,ZT.toZ]
    rw [natEq (congrFst (congrFst hy)),natEq (congrSnd (congrFst hy))]
  have dx : Γ ⊢[PRAAx] rationalDenominator x k ≐ rationalDenominator u l := congrSucc (congrSnd hx)
  have dy : Γ ⊢[PRAAx] rationalDenominator y k ≐ rationalDenominator v l := congrSucc (congrSnd hy)
  have cross : ZT.toZ Γ (crossNumerator x y k) = ZT.toZ Γ (crossNumerator u v l) := by
    simp only [crossNumerator,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
    rw [nx,ny,natEq dx,natEq dy]
  exact le_congr (congrMul (.eqRefl _) (Foundations.GapDecision.zabs_congr cross)).eqSymm
    (congrMul (.eqRefl _) (congrMul dx dy)).eqSymm h

/-- Original-coordinate sup-product radius, derived by a genuine coordinate
block split. The dimensions match the actual stored vector lengths. -/
theorem pointRadius_append (x x' y y' d d' A B : PTm n)
    (hx : Γ ⊢[PRAAx] length x ≐ d) (hx' : Γ ⊢[PRAAx] length x' ≐ d')
    (hy : Γ ⊢[PRAAx] length y ≐ d) (hy' : Γ ⊢[PRAAx] length y' ≐ d')
    (h : Γ ⊢[PRAAx] pointRadius x y d A B) (h' : Γ ⊢[PRAAx] pointRadius x' y' d' A B) :
    Γ ⊢[PRAAx] pointRadius (append x x') (append y y') (d+d') A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (d+d')) :: Γ.map Fm.shift
  have first : Δ ⊢[PRAAx] pointRadius (Syn.shift x) (Syn.shift y) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_pointRadius,Syn.shift] using h.shift.wk
  have second : Δ ⊢[PRAAx] pointRadius (Syn.shift x') (Syn.shift y') (Syn.shift d') (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_pointRadius,Syn.shift] using h'.shift.wk
  have ex : Δ ⊢[PRAAx] length (Syn.shift x) ≐ Syn.shift d := by simpa only [Fm.shift,Fm.subst_eq,subst_length,Syn.shift] using hx.shift.wk
  have ey : Δ ⊢[PRAAx] length (Syn.shift y) ≐ Syn.shift d := by simpa only [Fm.shift,Fm.subst_eq,subst_length,Syn.shift] using hy.shift.wk
  have ex' : Δ ⊢[PRAAx] length (Syn.shift x') ≐ Syn.shift d' := by simpa only [Fm.shift,Fm.subst_eq,subst_length,Syn.shift] using hx'.shift.wk
  have ey' : Δ ⊢[PRAAx] length (Syn.shift y') ≐ Syn.shift d' := by simpa only [Fm.shift,Fm.subst_eq,subst_length,Syn.shift] using hy'.shift.wk
  have total : Δ ⊢[PRAAx] lt (var 0) (Syn.shift d+Syn.shift d') := by
    simpa only [Δ,Syn.shift,PTm.subst_add] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have result : Δ ⊢[PRAAx] coordinateRadius (append (Syn.shift x) (Syn.shift x'))
      (append (Syn.shift y) (Syn.shift y')) (var 0) (Syn.shift A) (Syn.shift B) := by
    refine .orE (lt_or_le (var 0) (Syn.shift d)) ?_ ?_
    · have branch : lt (var 0) (Syn.shift d) :: Δ ⊢[PRAAx] lt (var 0) (Syn.shift d) := Prf.hyp0
      have leftX := append_left (b := Syn.shift x') (lt_congr (.eqRefl _) ex.wk.eqSymm branch)
      have leftY := append_left (b := Syn.shift y') (lt_congr (.eqRefl _) ey.wk.eqSymm branch)
      exact coordinate_from_entries _ _ _ _ _ _ _ _ leftX leftY (pointRadius_at _ _ _ _ _ _ first.wk branch)
    · have branch : le (Syn.shift d) (var 0) :: Δ ⊢[PRAAx] le (Syn.shift d) (var 0) := Prf.hyp0
      have localRange := suffix_range branch total.wk
      have rightX := (append_right_at (le_congr ex.wk.eqSymm (.eqRefl _) branch)
        (lt_congr (.eqRefl _) (congrAdd ex.wk ex'.wk).eqSymm total.wk)).eqTrans
          (entry_congr (.eqRefl _) (congrMonus (.eqRefl _) ex.wk))
      have rightY := (append_right_at (le_congr ey.wk.eqSymm (.eqRefl _) branch)
        (lt_congr (.eqRefl _) (congrAdd ey.wk ey'.wk).eqSymm total.wk)).eqTrans
          (entry_congr (.eqRefl _) (congrMonus (.eqRefl _) ey.wk))
      exact coordinate_from_entries _ _ _ _ _ _ _ _ rightX rightY
        (pointRadius_at _ _ _ _ _ _ second.wk localRange)
  simpa only [Δ,Syn.shift,subst_append,PTm.subst_add] using result

/-- Explicit source guards for the two factor lists and their point dimensions. -/
def pairGuard (S S' d d' : PTm n) : Fm PTm n :=
  le one (length S) ⋏ (le one (length S') ⋏ (shaped S d ⋏ shaped S' d'))

@[simp] theorem subst_pairGuard {m : ℕ} (σ : Fin n → PTm m) (S S' d d' : PTm n) :
    (pairGuard S S' d d').subst σ = pairGuard (Syn.subst σ S) (Syn.subst σ S') (Syn.subst σ d) (Syn.subst σ d') := by
  simp only [pairGuard,Fm.subst_and,subst_le,subst_length,subst_shaped,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]

theorem product_nonempty (S S' d d' : PTm n) (h : Γ ⊢[PRAAx] pairGuard S S' d d') :
    Γ ⊢[PRAAx] le one (length (product S S')) :=
  le_congr (one_mul one) (product_length S S').eqSymm
    (AnalyticNumberTheory.PhiLower.le_mul_mono (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h)))

/-- Actual flattened entries have the sum of the supplied runtime dimensions. -/
theorem product_shaped (S S' d d' : PTm n) (h : Γ ⊢[PRAAx] pairGuard S S' d d') :
    Γ ⊢[PRAAx] shaped (product S S') (d+d') := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (product S S'))) :: Γ.map Fm.shift
  have guard : Δ ⊢[PRAAx] pairGuard (Syn.shift S) (Syn.shift S') (Syn.shift d) (Syn.shift d') := by
    simpa only [Fm.shift,subst_pairGuard,Syn.shift] using h.shift.wk
  have rangeI : Δ ⊢[PRAAx] lt (var 0) (length (product (Syn.shift S) (Syn.shift S'))) := by
    simpa only [Δ,Syn.shift,subst_product] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have indices := product_indices (Syn.shift S) (Syn.shift S') (var 0) (Prf.andE₁ (Prf.andE₂ guard)) rangeI
  have entryEq := product_lookup (Syn.shift S) (Syn.shift S') (var 0) rangeI
  have leftLength := shaped_at _ _ _ (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ guard))) (Prf.andE₁ indices)
  have rightLength := shaped_at _ _ _ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ guard))) (Prf.andE₂ indices)
  have result := (congrFst entryEq).eqTrans ((append_length _ _).eqTrans (congrAdd leftLength rightLength))
  simpa only [Δ,Syn.shift,subst_product,PTm.subst_add,Foundations.SequenceComposition.length] using result

/-- Two actual original nearest indices provide one actual Cartesian target
index. There is no product-cover premise or product metric axiom. -/
theorem product_hit (S S' T T' d d' A B i : PTm n)
    (hS : Γ ⊢[PRAAx] pairGuard S S' d d') (hT : Γ ⊢[PRAAx] pairGuard T T' d d')
    (h : Γ ⊢[PRAAx] originalClose S T d A B) (h' : Γ ⊢[PRAAx] originalClose S' T' d' A B)
    (hi : Γ ⊢[PRAAx] lt i (length (product S S'))) :
    Γ ⊢[PRAAx] originalHit .left .right (product S S') (product T T') (d+d') A B i := by
  let a := quo i (length S')
  let b := rem i (length S')
  let j := RationalNearest.selected S T d a
  let l := RationalNearest.selected S' T' d' b
  have ranges := product_indices S S' i (Prf.andE₁ (Prf.andE₂ hS)) hi
  have ja : Γ ⊢[PRAAx] lt j (length T) := RationalNearest.selected_spec S T d a (Prf.andE₁ hT)
  have lb : Γ ⊢[PRAAx] lt l (length T') := RationalNearest.selected_spec S' T' d' b (Prf.andE₁ (Prf.andE₂ hT))
  have first := RationalNearest.cover_selected_radius S T d a A B (Prf.andE₁ ranges) (Prf.andE₁ hT) h
  have second := RationalNearest.cover_selected_radius S' T' d' b A B (Prf.andE₂ ranges) (Prf.andE₁ (Prf.andE₂ hT)) h'
  have combined := pointRadius_append (entry S a) (entry S' b) (entry T j) (entry T' l) d d' A B
    (shaped_at S d a (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hS))) (Prf.andE₁ ranges))
    (shaped_at S' d' b (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hS))) (Prf.andE₂ ranges))
    (shaped_at T d j (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hT))) ja)
    (shaped_at T' d' l (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hT))) lb) first second
  have radius := pointRadius_congr (product_lookup S S' i hi).eqSymm
    (product_pair_entry T T' j l (Prf.andE₁ (Prf.andE₂ hT)) ja lb).eqSymm combined
  exact originalHit_intro .left .right (product S S') (product T T') (d+d') A B i (pairIndex T' j l)
    (product_pair_range T T' j l ja lb) radius

theorem originalCover_product (S S' T T' d d' A B : PTm n)
    (hS : Γ ⊢[PRAAx] pairGuard S S' d d') (hT : Γ ⊢[PRAAx] pairGuard T T' d d')
    (h : Γ ⊢[PRAAx] originalClose S T d A B) (h' : Γ ⊢[PRAAx] originalClose S' T' d' A B) :
    Γ ⊢[PRAAx] originalCover .left .right (product S S') (product T T') (d+d') A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (product S S'))) :: Γ.map Fm.shift
  have gs : Δ ⊢[PRAAx] pairGuard (Syn.shift S) (Syn.shift S') (Syn.shift d) (Syn.shift d') := by
    simpa only [Fm.shift,subst_pairGuard,Syn.shift] using hS.shift.wk
  have gt : Δ ⊢[PRAAx] pairGuard (Syn.shift T) (Syn.shift T') (Syn.shift d) (Syn.shift d') := by
    simpa only [Fm.shift,subst_pairGuard,Syn.shift] using hT.shift.wk
  have first : Δ ⊢[PRAAx] originalClose (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_originalClose,Syn.shift] using h.shift.wk
  have second : Δ ⊢[PRAAx] originalClose (Syn.shift S') (Syn.shift T') (Syn.shift d') (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_originalClose,Syn.shift] using h'.shift.wk
  have rangeI : Δ ⊢[PRAAx] lt (var 0) (length (product (Syn.shift S) (Syn.shift S'))) := by
    simpa only [Δ,Syn.shift,subst_product] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have result := product_hit (Syn.shift S) (Syn.shift S') (Syn.shift T) (Syn.shift T')
    (Syn.shift d) (Syn.shift d') (Syn.shift A) (Syn.shift B) (var 0) gs gt first second rangeI
  simpa only [Δ,source,Syn.shift,subst_product,PTm.subst_add] using result

private theorem reverse_close (S T d A B : PTm n) (h : Γ ⊢[PRAAx] originalClose S T d A B) :
    Γ ⊢[PRAAx] originalClose T S d A B := by
  have first : Γ ⊢[PRAAx] originalCover .left .right T S d A B := .andE₂ h
  have second : Γ ⊢[PRAAx] originalCover .right .left T S d A B := .andE₁ h
  exact .andI first second

private theorem reverse_cover (S T d A B : PTm n)
    (h : Γ ⊢[PRAAx] originalCover .left .right T S d A B) :
    Γ ⊢[PRAAx] originalCover .right .left S T d A B := h

theorem originalClose_product (S S' T T' d d' A B : PTm n)
    (hS : Γ ⊢[PRAAx] pairGuard S S' d d') (hT : Γ ⊢[PRAAx] pairGuard T T' d d')
    (h : Γ ⊢[PRAAx] originalClose S T d A B) (h' : Γ ⊢[PRAAx] originalClose S' T' d' A B) :
    Γ ⊢[PRAAx] originalClose (product S S') (product T T') (d+d') A B :=
  .andI (originalCover_product S S' T T' d d' A B hS hT h h')
    (reverse_cover (product S S') (product T T') (d+d') A B
      (originalCover_product T T' S S' d d' A B hT hS
        (reverse_close S T d A B h) (reverse_close S' T' d' A B h')))

def radiusNumerator (S S' T T' d d' : PTm n) : PTm n :=
  maximumNumerator (numerator S T d) (denominator S T d) (numerator S' T' d') (denominator S' T' d')
def radiusDenominator (S S' T T' d d' : PTm n) : PTm n :=
  maximumDenominator (numerator S T d) (denominator S T d) (numerator S' T' d') (denominator S' T' d')

@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (S S' T T' d d' : PTm n) :
    Syn.subst σ (radiusNumerator S S' T T' d d') = radiusNumerator (Syn.subst σ S) (Syn.subst σ S')
      (Syn.subst σ T) (Syn.subst σ T') (Syn.subst σ d) (Syn.subst σ d') := by
  simp only [radiusNumerator,RationalHausdorffConcat.subst_maximumNumerator,subst_numerator,subst_denominator]
@[simp] theorem subst_radiusDenominator {m : ℕ} (σ : Fin n → PTm m) (S S' T T' d d' : PTm n) :
    Syn.subst σ (radiusDenominator S S' T T' d d') = radiusDenominator (Syn.subst σ S) (Syn.subst σ S')
      (Syn.subst σ T) (Syn.subst σ T') (Syn.subst σ d) (Syn.subst σ d') := by
  simp only [radiusDenominator,RationalHausdorffConcat.subst_maximumDenominator,subst_numerator,subst_denominator]

/-- The two independently normalized factor distances bound their original
coordinate covers at the exact common rational maximum. -/
theorem maximum_own_covers (S S' T T' d d' : PTm n)
    (hS : Γ ⊢[PRAAx] pairGuard S S' d d') (hT : Γ ⊢[PRAAx] pairGuard T T' d d') :
    Γ ⊢[PRAAx] originalClose S T d (radiusNumerator S S' T T' d d') (radiusDenominator S S' T T' d d') ⋏
      originalClose S' T' d' (radiusNumerator S S' T T' d d') (radiusDenominator S S' T T' d d') :=
  .andI (original_close_of_bound S T d _ _ (Prf.andE₁ hS) (Prf.andE₁ hT) (maximum_left_bound _ _ _ _))
    (original_close_of_bound S' T' d' _ _ (Prf.andE₁ (Prf.andE₂ hS)) (Prf.andE₁ (Prf.andE₂ hT)) (maximum_right_bound _ _ _ _))

theorem product_cover (S S' T T' d d' : PTm n)
    (hS : Γ ⊢[PRAAx] pairGuard S S' d d') (hT : Γ ⊢[PRAAx] pairGuard T T' d d') :
    Γ ⊢[PRAAx] originalClose (product S S') (product T T') (d+d')
      (radiusNumerator S S' T T' d d') (radiusDenominator S S' T T' d d') := by
  have h := maximum_own_covers S S' T T' d d' hS hT
  exact originalClose_product S S' T T' d d' _ _ hS hT (Prf.andE₁ h) (Prf.andE₂ h)

/-- Exact clause 3 at two independent factor scales and a third output scale. -/
theorem rational_product (S S' T T' d d' : PTm n)
    (hS : Γ ⊢[PRAAx] pairGuard S S' d d') (hT : Γ ⊢[PRAAx] pairGuard T T' d d') :
    Γ ⊢[PRAAx] le
      (radiusDenominator S S' T T' d d' * numerator (product S S') (product T T') (d+d'))
      (radiusNumerator S S' T T' d d' * denominator (product S S') (product T T') (d+d')) :=
  bound_of_original_close _ _ _ _ _ (product_cover S S' T T' d d' hS hT)

theorem product_checker (S S' T T' d d' : PTm n)
    (hS : Γ ⊢[PRAAx] pairGuard S S' d d') (hT : Γ ⊢[PRAAx] pairGuard T T' d d') :
    Γ ⊢[PRAAx] apply5 checkerF (product S S') (product T T') (d+d')
      (radiusNumerator S S' T T' d d') (radiusDenominator S S' T T' d d') ≐ one :=
  checker_complete _ _ _ _ _ (product_cover S S' T T' d d' hS hT)

theorem code_product (S S' T T' d d' : PTm n)
    (hS : Γ ⊢[PRAAx] pairGuard S S' d d') (hT : Γ ⊢[PRAAx] pairGuard T T' d d') :
    Γ ⊢[PRAAx] le
      (radiusDenominator S S' T T' d d' * fstT (ap3 codeF (product S S') (product T T') (d+d')))
      (radiusNumerator S S' T T' d d' * sndT (ap3 codeF (product S S') (product T T') (d+d'))) :=
  le_congr (congrMul (.eqRefl _) (code_numerator _ _ _).eqSymm)
    (congrMul (.eqRefl _) (code_denominator _ _ _).eqSymm) (rational_product S S' T T' d d' hS hT)

theorem rational_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (pairGuard (var 0) (var 1) (var 4) (var 5) ⟶ pairGuard (var 2) (var 3) (var 4) (var 5) ⟶
      le (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)*
        numerator (product (var 0) (var 1)) (product (var 2) (var 3)) (var 4+var 5))
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)*
          denominator (product (var 0) (var 1)) (product (var 2) (var 3)) (var 4+var 5))) :=
  closeUniv 6 (.impI (.impI (rational_product _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem product_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (pairGuard (var 0) (var 1) (var 4) (var 5) ⟶ pairGuard (var 2) (var 3) (var 4) (var 5) ⟶
      originalClose (product (var 0) (var 1)) (product (var 2) (var 3)) (var 4+var 5)
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (product_cover _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem product_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (pairGuard (var 0) (var 1) (var 4) (var 5) ⟶ pairGuard (var 2) (var 3) (var 4) (var 5) ⟶
      apply5 checkerF (product (var 0) (var 1)) (product (var 2) (var 3)) (var 4+var 5)
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ one) :=
  closeUniv 6 (.impI (.impI (product_checker _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 productF (var 0) (var 1) ≐ product (var 0) (var 1)) ⋏
      (length (product (var 0) (var 1)) ≐ length (var 0)*length (var 1))) :=
  closeUniv 2 (.andI (product_at _ _) (product_length _ _))

theorem product_shapes_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (pairGuard (var 0) (var 1) (var 2) (var 3) ⟶
      (le one (length (product (var 0) (var 1))) ⋏ shaped (product (var 0) (var 1)) (var 2+var 3))) :=
  closeUniv 4 (.impI (.andI (product_nonempty _ _ _ _ Prf.hyp0) (product_shaped _ _ _ _ Prf.hyp0)))

theorem radius_positive (S S' T T' d d' : PTm n) :
    Γ ⊢[PRAAx] le one (radiusDenominator S S' T T' d d') :=
  RationalHausdorffConcat.maximum_positive _ _ _ _
    (RationalSupMetric.commonDenominator_one_le _ _) (RationalSupMetric.commonDenominator_one_le _ _)

theorem code_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (pairGuard (var 0) (var 1) (var 4) (var 5) ⟶ pairGuard (var 2) (var 3) (var 4) (var 5) ⟶
      le (radiusDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)*
        fstT (ap3 codeF (product (var 0) (var 1)) (product (var 2) (var 3)) (var 4+var 5)))
        (radiusNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)*
          sndT (ap3 codeF (product (var 0) (var 1)) (product (var 2) (var 3)) (var 4+var 5)))) :=
  closeUniv 6 (.impI (.impI (code_product _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem product_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (length (product (var 0) (var 1))) ⟶
      (entry (product (var 0) (var 1)) (var 2) ≐ productValue (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (product_lookup _ _ _ Prf.hyp0))

theorem product_indices_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (length (var 1)) ⟶ lt (var 2) (length (product (var 0) (var 1))) ⟶
      (lt (quo (var 2) (length (var 1))) (length (var 0)) ⋏
        lt (rem (var 2) (length (var 1))) (length (var 1)))) :=
  closeUniv 3 (.impI (.impI (product_indices _ _ _ Prf.hyp1 Prf.hyp0)))

theorem point_product_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (length (var 0) ≐ var 4 ⟶ length (var 1) ≐ var 5 ⟶
      length (var 2) ≐ var 4 ⟶ length (var 3) ≐ var 5 ⟶
      pointRadius (var 0) (var 2) (var 4) (var 6) (var 7) ⟶
      pointRadius (var 1) (var 3) (var 5) (var 6) (var 7) ⟶
        pointRadius (append (var 0) (var 1)) (append (var 2) (var 3)) (var 4+var 5) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (.impI (pointRadius_append _ _ _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.RationalHausdorffProduct
