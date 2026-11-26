import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartImageWeights
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartImageUniformGrid
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerPowerScalingCorrectedQuadrature

/-!
# Original Euler samples on native chart blocks

Every native lattice row is within one corrected chart cell of its left
sample. The ordinary Euler rate then compares independent refinements
and clocks using the exact chart mesh bound. No code equality between
observations at different raw rational time encodings is required.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartCorrectedImage (input imageNumerator imageDenominator imageFraction)
open GaussianEulerPositivePowerChartImageCuts (data numeratorBody denominatorBody cutF start count denominator)
open GaussianEulerPositivePowerChartImageLattice (cutData)
open GaussianEulerPositivePowerChartImageWeights (original_lattice_geometry original_cut_order original_block_width fraction_bound_mono fraction_difference)
open GaussianEulerPositivePowerChartImage (reciprocalMargin query)
open GaussianEulerPositivePowerChart (majorant)
open GaussianEulerPositivePowerChartMesh (widthNumerator cellDenominator)
open GaussianPartitionedFiniteSumDistance (blockLength blockAgreement)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (grid value sampleBody sampleData)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at)
open GaussianRationalRiemannRefinement (termsDistance constantBody)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem subst_scaled {m : ℕ} (σ : Fin n → PTm m) (z f : PTm n) :
    Syn.subst σ (scaled z f) = scaled (Syn.subst σ z) (Syn.subst σ f) := by
  simp [scaled]

def coarseData (p z B x : PTm n) : PTm n := pairT x (pairT p (pairT z B))

def coarseBody : PTm 2 :=
  ap2 GaussianEulerIntegrandName.nameF (fstT (sndT (var 1)))
    (GaussianEulerIntegrandName.data (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
      (inst2 numeratorBody (var 0) (fstT (var 1))) (inst2 denominatorBody (var 0) (fstT (var 1))))

@[simp] theorem subst_coarseData {m : ℕ} (σ : Fin n → PTm m) (p z B x : PTm n) :
    Syn.subst σ (coarseData p z B x) = coarseData (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ x) := by
  simp [coarseData]

theorem coarse_body_at (p z B k i e f d h Q S E T a C N : PTm n) :
    Γ ⊢[PRAAx] inst2 coarseBody i (coarseData p z B (data k e f d h Q S E T a C N)) ≐
      ap2 GaussianEulerIntegrandName.nameF p (GaussianEulerIntegrandName.data z B
        (imageNumerator k i e f d h Q S E T a C N) (imageDenominator k i e f d h Q S E T a C N)) := by
  let x := data k e f d h Q S E T a C N
  let v := coarseData p z B x
  have hx : Γ ⊢[PRAAx] fstT v ≐ x := fst_pair _ _
  have hp : Γ ⊢[PRAAx] fstT (sndT v) ≐ p := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have ht : Γ ⊢[PRAAx] sndT (sndT v) ≐ pairT z B := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have hz : Γ ⊢[PRAAx] fstT (sndT (sndT v)) ≐ z := (congrFst ht).eqTrans (fst_pair _ _)
  have hb : Γ ⊢[PRAAx] sndT (sndT (sndT v)) ≐ B := (congrSnd ht).eqTrans (snd_pair _ _)
  have hn := (congrInst2 numeratorBody (.eqRefl i) hx).eqTrans (GaussianEulerPositivePowerChartImageCuts.numerator_at k i e f d h Q S E T a C N)
  have hd := (congrInst2 denominatorBody (.eqRefl i) hx).eqTrans (GaussianEulerPositivePowerChartImageCuts.denominator_at k i e f d h Q S E T a C N)
  have kernel : Γ ⊢[PRAAx] GaussianEulerIntegrandName.data (fstT (sndT (sndT v))) (sndT (sndT (sndT v)))
      (inst2 numeratorBody i (fstT v)) (inst2 denominatorBody i (fstT v)) ≐ GaussianEulerIntegrandName.data z B
        (imageNumerator k i e f d h Q S E T a C N) (imageDenominator k i e f d h Q S E T a C N) := by
    simpa using Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (GaussianEulerIntegrandName.data (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT (sndT (sndT v)),sndT (sndT (sndT v)),inst2 numeratorBody i (fstT v),inst2 denominatorBody i (fstT v)])
      (σ' := ![z,B,imageNumerator k i e f d h Q S E T a C N,imageDenominator k i e f d h Q S E T a C N])
      (fun j => by fin_cases j; exact hz; exact hb; exact hn; exact hd)
  have decomp : inst2 coarseBody i v = ap2 GaussianEulerIntegrandName.nameF (fstT (sndT v))
    (GaussianEulerIntegrandName.data (fstT (sndT (sndT v))) (sndT (sndT (sndT v)))
      (inst2 numeratorBody i (fstT v)) (inst2 denominatorBody i (fstT v))) := by
    unfold coarseBody
    change Syn.subst (![i,v] : Fin 2 → PTm n) _ = _
    simp only [subst_ap2,subst_sndT,subst_fstT,subst_inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      GaussianEulerIntegrandName.subst_data]
  change Γ ⊢[PRAAx] inst2 coarseBody i v ≐ _
  rw [decomp]
  exact congrAp2 _ hp kernel

def cost (p q k R h Q S E T C N : PTm n) : PTm n :=
  rateNumerator (GaussianEulerCompactModulus.lipschitz R (reciprocalMargin h Q E T) (majorant Q S E T+one)*
    widthNumerator k h Q S E T C N) (cellDenominator k h Q E T N) q p

def errorDenominator (p q k h Q E T N : PTm n) : PTm n := rateDenominator (cellDenominator k h Q E T N) q p

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (p q k R h Q S E T C N : PTm n) :
    Syn.subst σ (cost p q k R h Q S E T C N) = cost (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ R)
      (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) (Syn.subst σ N) := by
  simp [cost]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (p q k h Q E T N : PTm n) :
    Syn.subst σ (errorDenominator p q k h Q E T N) = errorDenominator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k)
      (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ N) := by
  simp [errorDenominator]

theorem cell_denominator_positive (k e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) : Γ ⊢[PRAAx] le one (cellDenominator k h Q E T N) :=
  positive_product _ _
    (positive_product _ _ hs.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂.andE₂.andE₂) (unit_positive _)

def fineData (q z B N x J : PTm n) : PTm n :=
  sampleData q (count N x J) (start N x J) (count N x J) (denominator N x J) (fixedData z B)

@[simp] theorem subst_fineData {m : ℕ} (σ : Fin n → PTm m) (q z B N x J : PTm n) :
    Syn.subst σ (fineData q z B N x J) = fineData (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ J) := by
  simp [fineData,count,start,denominator]

theorem original_lattice_row (p q k i r z R B e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerScalingCorrectedQuadrature.source k z R B e f d h Q S E T a C N)
    (hi : Γ ⊢[PRAAx] lt i N) (hJ : Γ ⊢[PRAAx] le one J)
    (hr : Γ ⊢[PRAAx] lt r (blockLength cutF i (cutData N (data k e f d h Q S E T a C N) J))) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (sampleBody evaluatorF) (ap2 cutF i (cutData N (data k e f d h Q S E T a C N) J)+r)
        (fineData q (scaled z f) (B*e) N (data k e f d h Q S E T a C N) J))
      (inst2 coarseBody i (coarseData p (scaled z f) (B*e) (data k e f d h Q S E T a C N)))
      (cost p q k R h Q S E T C N) (errorDenominator p q k h Q E T N) := by
  let x := data k e f d h Q S E T a C N
  let y := cutData N x J
  let c := ap2 cutF i y
  let j := c+r
  let K := count N x J
  let A := start N x J
  let M := denominator N x J
  let w := blockLength cutF i y
  let t := grid j K A K M
  let G := reciprocalMargin h Q E T
  let H := majorant Q S E T+one
  let u := imageNumerator k i e f d h Q S E T a C N
  let v := imageDenominator k i e f d h Q S E T a C N
  let D := cellDenominator k h Q E T N
  let L := widthNumerator k h Q S E T C N
  let z' := scaled z f
  let B' := B*e
  have geom := original_lattice_geometry k e f d h Q S E T a C N J hs.andE₂ hJ
  have hM : Γ ⊢[PRAAx] le one M := geom.andE₁.andE₂
  have hD : Γ ⊢[PRAAx] le one D := cell_denominator_positive k e f d h Q S E T a C N hs.andE₂
  have hi' := le_of_lt hi
  have step := GaussianPartitionedFiniteSum.cut_step cutF y i
    (GaussianEulerPositivePowerChartImageCuts.original_cut_increasing k e f d h Q S E T a C N J hs.andE₂)
  have finish : Γ ⊢[PRAAx] c+w ≐ ap2 cutF (succ i) y := (eq_add_of_le step).eqSymm
  have jBlock : Γ ⊢[PRAAx] lt j (c+w) :=
    le_congr (by dsimp only [j]; ipra_ring) (add_comm w c) (add_le_add_right c hr)
  have jBound : Γ ⊢[PRAAx] lt j K :=
    lt_of_lt_of_le (lt_congr (.eqRefl _) finish jBlock)
      (original_cut_order k (succ i) N e f d h Q S E T a C N J hs.andE₂ hi (le_refl N))
  have hK : Γ ⊢[PRAAx] le one K := le_trans (zero_lt_succ _) jBound
  have rawDomain := GaussianEulerPositivePowerChartImageCompactModulus.domain_of_inside t A K M G H geom
    (GaussianCompactRiemannName.grid_inside j K A K M geom.andE₁.andE₁ hM hK (le_of_lt jBound))
  have coarseDomain := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k i e f d h Q S E T a C N hs.andE₂ hi'
  have diffNat : Γ ⊢[PRAAx] monus (A+j) (A+c) ≐ r :=
    (congrMonus (by dsimp only [j]; ipra_ring : Γ ⊢[PRAAx] A+j ≐ (A+c)+r) (.eqRefl _)).eqTrans (add_monus' r (A+c))
  have hA : Γ ⊢[PRAAx] le (A+c) (A+j) := le_congr (.eqRefl _) (by dsimp only [j]; ipra_ring) (le_add_right (A+c) r)
  have nb := fraction_bound_mono r w M L D hM hD (le_of_lt hr)
    (GaussianRationalReciprocal.bound_congr
      (original_block_width k i e f d h Q S E T a C N J hs.andE₂ hi hJ).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerPowerScalingCell.corrected_width_bound k i e f d h Q S E T a C N hs.andE₂.andE₁ hi))
  have exactDiff := (fraction_difference (A+c) (A+j) M hM hA).eqTrans
    (GaussianEulerPositivePowerChartJacobian.fraction_congr diffNat (.eqRefl _))
  have near : Γ ⊢[PRAAx] distanceBounded (value t) (fraction u v) L D := by
    have left := GaussianEulerPositivePowerChartImageUniformGrid.grid_value j K A M hK hM
    have right := GaussianEulerPositivePowerChartImageCuts.original_lattice_node k i e f d h Q S E T a C N J hs.andE₂ hi' hJ
    exact distance_congr left.eqSymm right (.eqRefl _) (.eqRefl _)
      (GaussianRationalReciprocal.bound_congr exactDiff.eqSymm (.eqRefl _) (.eqRefl _) nb)
  have hG : Γ ⊢[PRAAx] le one G := GaussianEulerPositivePowerChartImage.margin_positive h Q E T
    hs.andE₂.andE₁.andE₁.andE₂.andE₁.andE₂
  have parameter : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z' R B' G :=
    .andI hs.andE₁.andE₁ (.andI hG hs.andE₁.andE₂)
  have rate := GaussianEulerCompactModulus.original_rate z' R B' G H (fstT t) (sndT t) u v L D
    (.andI parameter (.andI rawDomain (.andI coarseDomain (.andI hD near))))
  have rows := rate_at _ _ _ _ _ _ q p rate
  have left := (GaussianCompactRiemannName.sample_body_at (Γ := Γ) evaluatorF j q K A K M (fixedData z' B')).eqTrans
    (GaussianEulerCompactModulus.evaluator_raw_at q t z' B')
  have right := coarse_body_at (Γ := Γ) p z' B' k i e f d h Q S E T a C N
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) rows

theorem original_block_rows (p q k i z R B e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerScalingCorrectedQuadrature.source k z R B e f d h Q S E T a C N)
    (hi : Γ ⊢[PRAAx] lt i N) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] termsDistance (offB (sampleBody evaluatorF)) constantBody
      (blockLength cutF i (cutData N (data k e f d h Q S E T a C N) J))
      (pairT (ap2 cutF i (cutData N (data k e f d h Q S E T a C N) J))
        (fineData q (scaled z f) (B*e) N (data k e f d h Q S E T a C N) J))
      (inst2 coarseBody i (coarseData p (scaled z f) (B*e) (data k e f d h Q S E T a C N)))
      (cost p q k R h Q S E T C N) (errorDenominator p q k h Q E T N) := by
  let s (t : PTm n) := Syn.shift t
  have ss : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerPowerScalingCorrectedQuadrature.source (s k) (s z) (s R) (s B)
      (s e) (s f) (s d) (s h) (s Q) (s S) (s E) (s T) (s a) (s C) (s N) :=
    by simpa only [Fm.shift,GaussianEulerPowerScalingCorrectedQuadrature.subst_source,Syn.shift,s] using hs.shift
  have is : Γ.map Fm.shift ⊢[PRAAx] lt (s i) (s N) := by simpa only [Fm.shift,subst_lt,Syn.shift,s] using hi.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] le one (s J) := by simpa [Fm.shift,Syn.shift,s] using hJ.shift
  refine .allI (.impI ?_)
  let x := data (s k) (s e) (s f) (s d) (s h) (s Q) (s S) (s E) (s T) (s a) (s C) (s N)
  let c := ap2 cutF (s i) (cutData (s N) x (s J))
  let y := fineData (s q) (scaled (s z) (s f)) (s B*s e) (s N) x (s J)
  simp only [Syn.shift,GaussianPartitionedFiniteSumDistance.subst_blockLength,
    GaussianEulerPositivePowerChartImageCuts.subst_data,GaussianEulerPositivePowerChartImageLattice.subst_cutData,
    subst_pairT,subst_ap2,subst_inst2,subst_fineData,subst_coarseData,subst_cost,subst_errorDenominator,
    PTm.subst_mul,subst_scaled,GaussianRationalRiemannRefinement.constant_entry]
  refine distance_congr
    (LeanProofs.IPRA.AnalyticNumberTheory.BlockDispatch.off_at (sampleBody evaluatorF) (var 0) c y).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) ?_
  exact original_lattice_row (s p) (s q) (s k) (s i) (var 0) (s z) (s R) (s B)
    (s e) (s f) (s d) (s h) (s Q) (s S) (s E) (s T) (s a) (s C) (s N) (s J)
    ss.wk is.wk js.wk Prf.hyp0

theorem original_block_agreement (p q k z R B e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerScalingCorrectedQuadrature.source k z R B e f d h Q S E T a C N)
    (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] blockAgreement cutF (sampleBody evaluatorF) coarseBody N (cutData N (data k e f d h Q S E T a C N) J)
      (fineData q (scaled z f) (B*e) N (data k e f d h Q S E T a C N) J)
      (coarseData p (scaled z f) (B*e) (data k e f d h Q S E T a C N))
      (cost p q k R h Q S E T C N) (errorDenominator p q k h Q E T N) := by
  let s (t : PTm n) := Syn.shift t
  have ss : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerPowerScalingCorrectedQuadrature.source (s k) (s z) (s R) (s B)
      (s e) (s f) (s d) (s h) (s Q) (s S) (s E) (s T) (s a) (s C) (s N) :=
    by simpa only [Fm.shift,GaussianEulerPowerScalingCorrectedQuadrature.subst_source,Syn.shift,s] using hs.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] le one (s J) := by simpa [Fm.shift,Syn.shift,s] using hJ.shift
  refine .allI (.impI ?_)
  simpa only [blockAgreement,Syn.shift,GaussianEulerPositivePowerChartImageCuts.subst_data,
    GaussianEulerPositivePowerChartImageLattice.subst_cutData,subst_fineData,subst_coarseData,subst_cost,
    subst_errorDenominator,PTm.subst_mul,subst_scaled,s] using
    original_block_rows (s p) (s q) (s k) (var 0) (s z) (s R) (s B) (s e) (s f) (s d) (s h)
      (s Q) (s S) (s E) (s T) (s a) (s C) (s N) (s J) ss.wk Prf.hyp0 js.wk

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageRows
