import IPRADerivations.Analysis.Stirling.AllOrders.Covariance.GaussianStirlingAllOrderBoxProductGap
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelTail
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalCrossedProductSums

/-!
# Crossed-product comparison on the original reflected Bernoulli mesh

The entries are the original centered Bernoulli samples and the same
reflected reciprocal-power weights. Any pair in the first half of the
grid satisfies the weak cell order. The two separated subintervals
have the uniform positive margin already verified for their samples.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCrossedCells

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation)
open GaussianStirlingAllOrderBernoulliMeshOrder (sample_monotone)
open GaussianStirlingAllOrderBoxProductGap (sampleAt weightAt boxMargin box_product_gap)
open GaussianStirlingAllOrderCenteredBernoulli (sample_canonical)
open GaussianStirlingAllOrderPairedRefinement (mesh start pair_monotone)
open GaussianStirlingAllOrderPairedWeight (pairWeight subst_pairWeight)
open GaussianStirlingAllOrderPanelTail (panelData)
open RationalAlgebra (add_congr add_associative add_commutative multiply_commutative)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (add add_guard multiply)
open RationalCrossedProductSums (cell rectangleCells rowCells)
open RationalFiniteSum (term subst_term)
open RationalNormalForm (wellFormed normalize_well_formed)
open RationalReciprocalPowerTail (add_zero_right)
open RationalReverseChebyshevCell (rectangle_margin)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

local notation "qzero" => fraction zero one

private theorem half_mesh_positive (S : PTm n) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx] le one (S*num 8) :=
  positive_product _ _ hS (by ipra_le 7)

private theorem weight_monotone (q A B S i j : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le one S) (hij : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le (two*j) (S*num 8)) :
    Γ ⊢[PRAAx] rationalLE (weightAt q A B S j) (weightAt q A B S i) := by
  have hu : Γ ⊢[PRAAx] le one (start A S) :=
    positive_product _ _ hS (positive_product _ _ (by ipra_le 7) hA)
  have step : Γ ⊢[PRAAx] le (B*i) (B*j) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right B hij)
  have bound : Γ ⊢[PRAAx] le (two*(B*j)) (mesh B S) := by
    unfold mesh
    exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right B hj)
  exact pair_monotone _ _ _ _ _ hu step bound

private theorem put_middle (a b c : PTm n) : Γ ⊢[PRAAx] add (add a b) c ≐ add (add a c) b :=
  (add_associative a b c).eqTrans
    ((add_congr (.eqRefl _) (add_commutative b c)).eqTrans (add_associative a c b).eqSymm)

private theorem increasing_cell (m : ℕ) (q A B S i j : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le one S) (hij : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le (two*j) (S*num 8)) :
    Γ ⊢[PRAAx] rationalLE
      (add (multiply (sampleAt m S i) (weightAt q A B S i)) (multiply (sampleAt m S j) (weightAt q A B S j)))
      (add (multiply (sampleAt m S i) (weightAt q A B S j)) (multiply (sampleAt m S j) (weightAt q A B S i))) := by
  let X := sampleAt m S i
  let Y := sampleAt m S j
  let U := weightAt q A B S i
  let V := weightAt q A B S j
  have hM := half_mesh_positive S hS
  have hX : Γ ⊢[PRAAx] wellFormed X := sample_canonical _ _ _ hM
  have hY : Γ ⊢[PRAAx] wellFormed Y := sample_canonical _ _ _ hM
  have hU : Γ ⊢[PRAAx] wellFormed U := add_guard _ _
  have hV : Γ ⊢[PRAAx] wellFormed V := add_guard _ _
  have h0 : Γ ⊢[PRAAx] wellFormed qzero := normalize_well_formed _ _ (le_refl one)
  have s0 := nonnegative_of_representation (Γ := Γ) qzero zero one (le_refl one) (fraction_represents zero one (le_refl one))
  have H : Γ ⊢[PRAAx] rationalLE X Y := sample_monotone m i j (S*num 8) hM hij hj
  have W := weight_monotone q A B S i j hA hS hij hj
  have left := rationalLE_congr (add_zero_right X hX).eqSymm (.eqRefl _) H
  have right := rationalLE_congr (add_zero_right V hV).eqSymm (.eqRefl _) W
  have balance := rectangle_margin X Y U V qzero qzero hY hU h0 h0 s0 s0 left right
  exact rationalLE_congr
    ((add_congr (.eqRefl _) (GaussianStirlingAllOrderKernel.multiply_zero_right qzero)).eqTrans
      (add_zero_right _ (add_guard _ _))) (.eqRefl _) balance

theorem weak_cell (m : ℕ) (q A B S i j : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le one S) (hi : Γ ⊢[PRAAx] le (two*i) (S*num 8))
    (hj : Γ ⊢[PRAAx] le (two*j) (S*num 8)) :
    Γ ⊢[PRAAx] cell (sampleAt m S i) (weightAt q A B S i) (sampleAt m S j) (weightAt q A B S j) qzero := by
  let X := sampleAt m S i
  let Y := sampleAt m S j
  let U := weightAt q A B S i
  let V := weightAt q A B S j
  have step : Γ ⊢[PRAAx] rationalLE (add (multiply X U) (multiply Y V)) (add (multiply X V) (multiply Y U)) := by
    refine .orE (le_total i j) (increasing_cell m q A B S i j hA.wk hS.wk Prf.hyp0 hj.wk) ?_
    exact rationalLE_congr (add_commutative _ _) (add_commutative _ _)
      (increasing_cell m q A B S j i hA.wk hS.wk Prf.hyp0 hi.wk)
  exact rationalLE_congr (add_congr (add_zero_right _ (RationalArithmetic.multiply_guard _ _)).eqSymm (.eqRefl _))
    (add_congr (.eqRefl _) (multiply_commutative Y U)) step

theorem strong_cell (m : ℕ) (q A B S i j : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S)
    (hi : Γ ⊢[PRAAx] le i (S*one)) (hj : Γ ⊢[PRAAx] le (S*num 3) j)
    (hM : Γ ⊢[PRAAx] le (two*j) (S*num 8)) :
    Γ ⊢[PRAAx] cell (sampleAt m S i) (weightAt q A B S i) (sampleAt m S j) (weightAt q A B S j)
      (boxMargin m q A B) :=
  rationalLE_congr (put_middle _ _ _) (add_congr (.eqRefl _) (multiply_commutative _ _))
    (box_product_gap m q A B S i j hA hB hS hi hj hM)

/-- Shared table environment for a half-grid segment with an initial index. -/
def segmentData (q A B S startIndex : PTm n) : PTm n := panelData q A B S startIndex

private def parameter (d : PTm n) : PTm n := sndT (sndT (sndT d))
noncomputable def bernoulliBody (m : ℕ) : PTm 2 :=
  sampleAt m (fstT (parameter (var 1))) (sndT (parameter (var 1))+var 0)
def reflectedBody : PTm 2 :=
  let d := var 1
  weightAt (fstT d) (fstT (sndT d)) (fstT (sndT (sndT d))) (fstT (parameter d)) (sndT (parameter d)+var 0)

@[simp] theorem subst_segmentData {l : ℕ} (σ : Fin n → PTm l) (q A B S t : PTm n) :
    Syn.subst σ (segmentData q A B S t) =
      segmentData (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ S) (Syn.subst σ t) := by
  simp [segmentData]

@[simp] theorem subst_sampleAt {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (S p : PTm n) :
    Syn.subst σ (sampleAt m S p) = sampleAt m (Syn.subst σ S) (Syn.subst σ p) := by simp [sampleAt]

@[simp] theorem subst_weightAt {l : ℕ} (σ : Fin n → PTm l) (q A B S p : PTm n) :
    Syn.subst σ (weightAt q A B S p) =
      weightAt (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ S) (Syn.subst σ p) := by simp [weightAt,mesh,start]

private theorem tail_read (q A B S t : PTm n) : Γ ⊢[PRAAx] parameter (segmentData q A B S t) ≐ pairT S t := by
  unfold parameter segmentData panelData
  exact ((congrSnd (congrSnd (snd_pair _ _))).eqTrans (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem bernoulli_at (m : ℕ) (i q A B S t : PTm n) :
    Γ ⊢[PRAAx] term (bernoulliBody m) i (segmentData q A B S t) ≐ sampleAt m S (t+i) := by
  let d := segmentData q A B S t
  have h := tail_read (Γ := Γ) q A B S t
  simp only [term,bernoulliBody,parameter,inst2,subst_sampleAt,subst_fstT,subst_sndT,PTm.subst_add,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [parameter,subst_sampleAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (Prf.eqCongr (Γ := Γ) (sampleAt m (var 0) (var 1) : PTm 2)
      (σ := ![fstT (parameter d),sndT (parameter d)+i]) (σ' := ![S,t+i]) (fun r => by
        fin_cases r
        · exact (congrFst h).eqTrans (fst_pair _ _)
        · exact congrAdd ((congrSnd h).eqTrans (snd_pair _ _)) (.eqRefl i)))

theorem reflected_at (i q A B S t : PTm n) :
    Γ ⊢[PRAAx] term reflectedBody i (segmentData q A B S t) ≐ weightAt q A B S (t+i) := by
  let d := segmentData q A B S t
  have h := tail_read (Γ := Γ) q A B S t
  simp only [term,reflectedBody,parameter,inst2,subst_weightAt,subst_fstT,subst_sndT,PTm.subst_add,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [parameter,subst_weightAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    (Prf.eqCongr (Γ := Γ) (weightAt (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![fstT d,fstT (sndT d),fstT (sndT (sndT d)),fstT (parameter d),sndT (parameter d)+i])
      (σ' := ![q,A,B,S,t+i]) (fun r => by
        fin_cases r
        · exact fst_pair _ _
        · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
        · exact ((congrFst (congrSnd (snd_pair _ _))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
        · exact (congrFst h).eqTrans (fst_pair _ _)
        · exact congrAdd ((congrSnd h).eqTrans (snd_pair _ _)) (.eqRefl i)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCrossedCells
