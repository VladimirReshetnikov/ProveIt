import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderFullGridMeanRate
import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderMidpointCorrection
import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPairedWeightMass
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsOuterFold

/-!
# The first-panel covariance margin on every nonempty outer prefix

The first strict comparison supplies one fixed positive margin.
Each later panel contributes its ordinary comparison and its exact
midpoint correction, preserving that same margin at all prefix lengths.
-/

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderOuterCovariance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderFullGridCovariance (midpointCorrection doubledWeight)
open GaussianStirlingAllOrderFullGridMeanRate (correctedMean signed_mean_covariance)
open GaussianStirlingAllOrderHalfGridMean (margin normalized_margin_positive)
open GaussianStirlingAllOrderMidpointCorrection (subst_midpointCorrection)
open GaussianStirlingAllOrderPairedWeightFold (weightAverage)
open GaussianStirlingAllOrderPairedWeightMass (original_weight_average)
open GaussianStirlingAllOrderPanelPartsRecurrence (panelMass)
open GaussianStirlingAllOrderPanelPartsOuter (data)
open GaussianStirlingAllOrderPanelPartsOuterFold (massPrefix mass_succ panelPrefix panel_succ)
open GaussianStirlingAllOrderPanelTail (panel)
open RationalAlgebra (add_associative add_commutative add_congr multiply_add multiply_congr)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (add multiply add_guard multiply_guard)
open RationalFiniteSum (sum term sum_zero sum_succ)
open RationalReciprocalPowerTail (zero_fraction add_zero_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "z" => fraction zero one

noncomputable def midpointBody (m e : ℕ) : PTm 2 :=
  let x := var 1
  midpointCorrection m (num (e-1)) (fstT x) (fstT (sndT x)) (sndT (sndT x)) (var 0)

noncomputable def midpointPrefix (m e : ℕ) (A B S L : PTm n) : PTm n := sum (midpointBody m e) L (data A B S)

@[simp] theorem subst_midpointPrefix {l : ℕ} (σ : Fin n → PTm l) (m e : ℕ) (A B S L : PTm n) :
    Syn.subst σ (midpointPrefix m e A B S L) =
      midpointPrefix m e (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ S) (Syn.subst σ L) := by
  simp [midpointPrefix,GaussianStirlingAllOrderPanelPartsOuter.data]

theorem midpoint_at (m e : ℕ) (A B S k : PTm n) : Γ ⊢[PRAAx]
    term (midpointBody m e) k (data A B S) ≐ midpointCorrection m (num (e-1)) A B S k := by
  let d := data A B S
  have p : Γ ⊢[PRAAx] sndT d ≐ pairT B S := snd_pair _ _
  simpa only [term,midpointBody,inst2,subst_midpointCorrection,LeanProofs.IPRA.PTm.subst_num,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (midpointCorrection m (num (e-1)) (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT d,fstT (sndT d),sndT (sndT d),k]) (σ' := ![A,B,S,k])
      (fun i => by
        fin_cases i
        exact fst_pair _ _
        exact (congrFst p).eqTrans (fst_pair _ _)
        exact (congrSnd p).eqTrans (snd_pair _ _)
        exact .eqRefl _)

theorem midpoint_succ (m e : ℕ) (A B S L : PTm n) : Γ ⊢[PRAAx]
    midpointPrefix m e A B S (succ L) ≐
      add (midpointPrefix m e A B S L) (midpointCorrection m (num (e-1)) A B S L) := by
  unfold midpointPrefix
  exact (RationalFiniteSum.sum_succ (midpointBody m e) L (data A B S)).eqTrans
    (add_congr (.eqRefl _) (midpoint_at m e A B S L))

noncomputable def firstMargin (m e : ℕ) (A B : PTm n) : PTm n :=
  margin m (num (e-1)) (A+B*zero) B

@[simp] theorem subst_firstMargin {l : ℕ} (σ : Fin n → PTm l) (m e : ℕ) (A B : PTm n) :
    Syn.subst σ (firstMargin m e A B) = firstMargin m e (Syn.subst σ A) (Syn.subst σ B) := by
  simp [firstMargin,margin,GaussianStirlingAllOrderBoxProductGap.boxMargin,
    GaussianStirlingAllOrderBernoulliMeshMargin.margin,GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen,
    GaussianStirlingAllOrderCenteredBernoulli.denominator,BernoulliBounds.zint,
    GaussianStirlingAllOrderPairedRefinement.centerGap,GaussianStirlingAllOrderPairedWeight.gapFraction]

@[simp] theorem subst_correctedMean {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (S : PTm n) :
    Syn.subst σ (correctedMean m S) = correctedMean m (Syn.subst σ S) := by
  simp [correctedMean,GaussianStirlingAllOrderFullGridMeanRate.meanErrorNumerator,
    GaussianStirlingAllOrderFullGridMeanRate.meanErrorDenominator,GaussianStirlingAllOrderPanelDerivative.signedMean,
    GaussianStirlingAllOrderPanelDerivative.meanNumerator,BernoulliBounds.zint]

noncomputable def prefixComparison (m e : ℕ) (A B S L : PTm n) : Fm PTm n :=
  let M := S*num 8
  let P := panelPrefix m (e-1) A B M L
  let W := massPrefix e A B M L
  rationalLE
    (add (multiply (fraction two one) P) (firstMargin m e A B))
    (add (multiply (correctedMean m S) (multiply (fraction two one) W)) (midpointPrefix m e A B S L))

@[simp] theorem subst_prefixComparison {l : ℕ} (σ : Fin n → PTm l) (m e : ℕ) (A B S L : PTm n) :
    (prefixComparison m e A B S L).subst σ =
      prefixComparison m e (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ S) (Syn.subst σ L) :=
  by simp [prefixComparison,two]

theorem margin_nonnegative (m : ℕ) (q U B : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalLE z (margin m q U B) := by
  let D := num 32*GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen m*
    GaussianStirlingAllOrderBoxProductGap.weightDenominator q U B
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
  have base : Γ ⊢[PRAAx] le one (num 8*U+B) := le_trans (positive_product _ _ h8 hU) (le_add_right _ _)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _
    (positive_product _ _ (by ipra_le 31)
      (GaussianStirlingAllOrderCenteredBernoulli.denominator_positive _ _ h8))
    (GaussianStirlingAllOrderPairedWeight.gap_denominator_positive _ _ _ _ base)
  have h : Γ ⊢[PRAAx] rationalLE z (fraction one D) :=
    fraction_order _ _ _ _ (le_refl one) hD (by ipra_le 1)
  exact transitive h (normalized_margin_positive m q U B hU hB)

private theorem panel_comparison (m e : ℕ) (he : 1≤e) (A B S k : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE
      (add (multiply (fraction two one) (panel m (num (e-1)) A B (S*num 8) k)) (margin m (num (e-1)) (A+B*k) B))
      (add (multiply (correctedMean m S) (multiply (fraction two one) (panelMass e (A+B*k) B (S*num 8))))
        (midpointCorrection m (num (e-1)) A B S k)) := by
  have eW := original_weight_average (Γ := Γ) e he (A+B*k) B S
  have right := add_congr (multiply_congr (.eqRefl (correctedMean m S)) (multiply_congr (.eqRefl (fraction two one)) eW))
    (.eqRefl (midpointCorrection m (num (e-1)) A B S k))
  exact rationalLE_congr (.eqRefl _) right (signed_mean_covariance m (num (e-1)) A B S k hA hB hS)

private theorem panel_weak (m e : ℕ) (he : 1≤e) (A B S k : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE
      (multiply (fraction two one) (panel m (num (e-1)) A B (S*num 8) k))
      (add (multiply (correctedMean m S) (multiply (fraction two one) (panelMass e (A+B*k) B (S*num 8))))
        (midpointCorrection m (num (e-1)) A B S k)) := by
  let X := multiply (fraction two one) (panel m (num (e-1)) A B (S*num 8) k)
  let E := margin m (num (e-1)) (A+B*k) B
  have hU : Γ ⊢[PRAAx] le one (A+B*k) := le_trans hA (le_add_right _ _)
  have le := add_monotone X X z E (reflexive _) (margin_nonnegative m (num (e-1)) (A+B*k) B hU hB)
  exact transitive (rationalLE_congr (add_zero_right X (multiply_guard _ _)) (.eqRefl _) le)
    (panel_comparison m e he A B S k hA hB hS)

private theorem sum_one_right (f : PTm 2) (x t : PTm n)
    (h : Γ ⊢[PRAAx] term f zero x ≐ t) (ht : Γ ⊢[PRAAx] RationalNormalForm.wellFormed t) :
    Γ ⊢[PRAAx] sum f one x ≐ t := by
  have base : Γ ⊢[PRAAx] sum f one x ≐ add (sum f zero x) (term f zero x) := RationalFiniteSum.sum_succ f zero x
  have e : Γ ⊢[PRAAx] sum f zero x ≐ z := (RationalFiniteSum.sum_zero f x).eqTrans zero_fraction.eqSymm
  exact base.eqTrans ((add_congr e h).eqTrans
    ((add_commutative z t).eqTrans (add_zero_right t ht)))

private theorem prefix_base (m e : ℕ) (he : 1≤e) (A B S : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] prefixComparison m e A B S one := by
  let M := S*num 8
  have hP : Γ ⊢[PRAAx] panelPrefix m (e-1) A B M one ≐ panel m (num (e-1)) A B M zero :=
    sum_one_right _ _ _ (GaussianStirlingAllOrderPanelPartsOuterFold.panel_at m (e-1) A B M zero) (multiply_guard _ _)
  have hW : Γ ⊢[PRAAx] massPrefix e A B M one ≐ panelMass e (A+B*zero) B M :=
    sum_one_right _ _ _ (GaussianStirlingAllOrderPanelPartsOuterFold.mass_at e A B M zero) (multiply_guard _ _)
  have hT : Γ ⊢[PRAAx] midpointPrefix m e A B S one ≐ midpointCorrection m (num (e-1)) A B S zero :=
    sum_one_right _ _ _ (midpoint_at m e A B S zero) (multiply_guard _ _)
  exact rationalLE_congr (add_congr (multiply_congr (.eqRefl _) hP.eqSymm) (.eqRefl _))
    (add_congr (multiply_congr (.eqRefl _) (multiply_congr (.eqRefl _) hW.eqSymm)) hT.eqSymm)
    (panel_comparison m e he A B S zero hA hB hS)

private theorem add_shuffle (a b c d : PTm n) : Γ ⊢[PRAAx] add (add a b) (add c d) ≐ add (add a c) (add b d) := by
  exact (add_associative _ _ _).eqTrans
    ((add_congr (.eqRefl _) ((add_associative _ _ _).eqSymm.eqTrans
      ((add_congr (add_commutative b c) (.eqRefl _)).eqTrans (add_associative _ _ _)))).eqTrans
      (add_associative _ _ _).eqSymm)

private theorem prefix_step (m e : ℕ) (he : 1≤e) (A B S L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S)
    (ih : Γ ⊢[PRAAx] prefixComparison m e A B S L) :
    Γ ⊢[PRAAx] prefixComparison m e A B S (succ L) := by
  let M := S*num 8
  let c : PTm n := fraction two one
  let P := panelPrefix m (e-1) A B M L
  let W := massPrefix e A B M L
  let E := midpointPrefix m e A B S L
  let U := A+B*L
  let p := panel m (num (e-1)) A B M L
  let w := panelMass e U B M
  let t := midpointCorrection m (num (e-1)) A B S L
  let C := correctedMean m S
  let η := firstMargin m e A B
  have h : Γ ⊢[PRAAx] rationalLE (add (multiply c P) η) (add (multiply C (multiply c W)) E) := ih
  have k : Γ ⊢[PRAAx] rationalLE (multiply c p) (add (multiply C (multiply c w)) t) :=
    panel_weak m e he A B S L hA hB hS
  have joined := add_monotone _ _ _ _ h k
  have left := (add_associative (Γ := Γ) (multiply c P) η (multiply c p)).eqTrans
    ((add_congr (.eqRefl _) (add_commutative η (multiply c p))).eqTrans
      ((add_associative _ _ _).eqSymm.eqTrans
        (add_congr ((multiply_add _ _ _).eqSymm.eqTrans (multiply_congr (.eqRefl _)
          (panel_succ m (e-1) A B M L).eqSymm)) (.eqRefl _))))
  have wSum := (multiply_add (Γ := Γ) C (multiply c W) (multiply c w)).eqSymm.eqTrans
    (multiply_congr (.eqRefl _) ((multiply_add _ _ _).eqSymm.eqTrans
      (multiply_congr (.eqRefl _) (mass_succ e A B M L).eqSymm)))
  have right := (add_shuffle (Γ := Γ) (multiply C (multiply c W)) E (multiply C (multiply c w)) t).eqTrans
    (add_congr wSum (midpoint_succ m e A B S L).eqSymm)
  exact rationalLE_congr left right joined

theorem strict_outer_prefix (m e : ℕ) (he : 1≤e) (A B S L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] prefixComparison m e A B S (succ L) := by
  have hA' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hS' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift S) := by simpa [Fm.shift,Syn.shift] using hS.shift
  have all : Γ ⊢[PRAAx] .all (prefixComparison m e (Syn.shift A) (Syn.shift B) (Syn.shift S) (succ (var 0))) := by
    refine PRA.qfInd _ (by unfold prefixComparison rationalLE; exact le_QF _ _) ?_ ?_
    · simpa only [subst_prefixComparison,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        prefix_base m e he A B S hA hB hS
    · simpa only [subst_prefixComparison,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_step m e he (Syn.shift A) (Syn.shift B) (Syn.shift S) (succ (var 0)) hA'.wk hB'.wk hS'.wk Prf.hyp0
  simpa only [subst_prefixComparison,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE L

theorem actual_original_outer_prefix_covariance_closed (m e : ℕ) (he : 1≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 0) ⟶ le one (var 1) ⟶ le one (var 2) ⟶
        prefixComparison m e (var 0) (var 1) (var 2) (succ (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (strict_outer_prefix m e he _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderOuterCovariance
