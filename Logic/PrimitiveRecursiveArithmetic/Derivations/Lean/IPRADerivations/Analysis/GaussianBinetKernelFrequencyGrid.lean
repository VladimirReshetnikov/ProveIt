import IPRADerivations.Analysis.GaussianBinetKernelFrozenIndependent
import IPRADerivations.Analysis.GaussianBinetOscillatoryColumns

/-!
# Binet kernel observations on the original frequency grid

The finite sine transform and the original compact Laplace integral
use the same left tags and the same mesh weights. A suffix discards
early rows by retaining their original indices in the full grid.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelFrequencyGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelFrozenIndependent (dampedNumerator errorDenominator)
open GaussianBinetLaplaceIntegrand (cofinalData cofinalF subst_cofinalData)
open GaussianBinetLaplaceStrip (evaluatorF evaluator_at fixedData tagNumerator)
open GaussianBinetOscillatoryColumns (damping)
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (grid sampleBody sampleData sample_body_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul)
open GaussianRationalRiemannRefinement (weight subst_weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "domain" => GaussianLogGammaEulerResidualDomain.source

abbrev cofinalBody : PTm 2 := sampleBody (evaluatorF .cofinal)
abbrev originalData (q N X Y D sign R T C : PTm n) : PTm n :=
  sampleData q N (one+zero) C one (fixedData X Y D sign R T zero)

private theorem physical_data_congr (X Y D sign R T a a' b b' : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] cofinalData X Y D sign R T a b ≐ cofinalData X Y D sign R T a' b' := by
  have ea : Γ ⊢[PRAAx] cofinalData X Y D sign R T a b ≐ cofinalData X Y D sign R T a' b := by
    simpa only [subst_cofinalData,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (cofinalData (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign)
        (Syn.shift R) (Syn.shift T) (var 0) (Syn.shift b)) ha
  have eb : Γ ⊢[PRAAx] cofinalData X Y D sign R T a' b ≐ cofinalData X Y D sign R T a' b' := by
    simpa only [subst_cofinalData,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (cofinalData (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign)
        (Syn.shift R) (Syn.shift T) (Syn.shift a') (var 0)) hb
  exact ea.eqTrans eb

theorem physical_tag (j N C W : PTm n) (hw : Γ ⊢[PRAAx] C ≐ W) :
    Γ ⊢[PRAAx] (tagNumerator (grid j N (one+zero) C one) ≐ W*j) ⋏
      (sndT (grid j N (one+zero) C one) ≐ N) := by
  have tag := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Γ) j N zero C one
  exact .andI (tag.andE₁.eqTrans ((by ipra_ring : Γ ⊢[PRAAx] zero*N+C*j ≐ C*j).eqTrans
    (congrMul hw (.eqRefl j)))) (tag.andE₂.eqTrans (one_mul N))

theorem physical_row_at (j q N X Y D sign R T C W : PTm n) (hw : Γ ⊢[PRAAx] C ≐ W) :
    Γ ⊢[PRAAx] inst2 cofinalBody j (originalData q N X Y D sign R T C) ≐
      ap2 cofinalF q (cofinalData X Y D sign R T (W*j) N) := by
  let t := grid j N (one+zero) C one
  have tag := physical_tag j N C W hw
  exact (sample_body_at (evaluatorF .cofinal) j q N (one+zero) C one (fixedData X Y D sign R T zero)).eqTrans
    ((evaluator_at .cofinal q t X Y D sign R T zero).eqTrans
      (congrAp2 cofinalF (.eqRefl q)
        (physical_data_congr X Y D sign R T (tagNumerator t) (W*j) (sndT t) N tag.andE₁ tag.andE₂)))

theorem physical_weight (N C W : PTm n) (hw : Γ ⊢[PRAAx] C ≐ W) :
    Γ ⊢[PRAAx] weight C one N ≐ weight W one N := by
  simpa only [subst_weight,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    Prf.eqCongr1 (weight (var 0) one (Syn.shift N)) hw

theorem late_physical_row_error (j r p q k I N X Y D sign R T C W : PTm n)
    (h : Γ ⊢[PRAAx] domain X Y D sign R) (hN : Γ ⊢[PRAAx] le one N)
    (hj : Γ ⊢[PRAAx] le j N) (hI : Γ ⊢[PRAAx] le one I)
    (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k)) (hC : Γ ⊢[PRAAx] le W T)
    (hw : Γ ⊢[PRAAx] C ≐ W) (hr : Γ ⊢[PRAAx] le p r) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetKernelFrozenStrip.rowValue r k I X Y D sign R T (W*j) N)
      (inst2 cofinalBody j (originalData q N X Y D sign R T C))
      (dampedNumerator p q I) (errorDenominator p q I) := by
  have rise : Γ ⊢[PRAAx] le (W*j) (W*N) :=
    le_congr (mul_comm j W) (mul_comm N W) (mul_le_mul_right W hj)
  have guard := le_trans rise (mul_le_mul_right N hC)
  exact distance_congr (.eqRefl _) (physical_row_at j q N X Y D sign R T C W hw).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBinetKernelFrozenIndependent.late_damped_error r p q k I X Y D sign R T (W*j) N
      (.andI h (.andI hN guard)) hI hk hr)

theorem physical_row_error (j p q k I N X Y D sign R T C W : PTm n)
    (h : Γ ⊢[PRAAx] domain X Y D sign R) (hN : Γ ⊢[PRAAx] le one N)
    (hj : Γ ⊢[PRAAx] le j N) (hI : Γ ⊢[PRAAx] le one I)
    (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k)) (hC : Γ ⊢[PRAAx] le W T)
    (hw : Γ ⊢[PRAAx] C ≐ W) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetKernelFrozenStrip.rowValue p k I X Y D sign R T (W*j) N)
      (inst2 cofinalBody j (originalData q N X Y D sign R T C))
      (dampedNumerator p q I) (errorDenominator p q I) :=
  late_physical_row_error j p p q k I N X Y D sign R T C W h hN hj hI hk hC hw (le_refl p)

theorem physical_suffix_row_error (j J p q k I N X Y D sign R T C W : PTm n)
    (h : Γ ⊢[PRAAx] domain X Y D sign R) (hN : Γ ⊢[PRAAx] le one N)
    (hj : Γ ⊢[PRAAx] le (J+j) N) (hI : Γ ⊢[PRAAx] le one I)
    (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k)) (hC : Γ ⊢[PRAAx] le W T)
    (hw : Γ ⊢[PRAAx] C ≐ W) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetKernelFrozenStrip.rowValue p k I X Y D sign R T (W*(J+j)) N)
      (inst2 (offB cofinalBody) j (pairT J (originalData q N X Y D sign R T C)))
      (dampedNumerator p q I) (errorDenominator p q I) :=
  distance_congr (.eqRefl _) (offset_at cofinalBody J j (originalData q N X Y D sign R T C)).eqSymm
    (.eqRefl _) (.eqRefl _) (physical_row_error (J+j) p q k I N X Y D sign R T C W h hN hj hI hk hC hw)

/-- Retain the literal damping sample returned by the sine transpose. -/
theorem damping_suffix_error (j J s p q k I N X Y D sign R T C W : PTm n)
    (h : Γ ⊢[PRAAx] domain X Y D sign R) (hN : Γ ⊢[PRAAx] le one N)
    (hj : Γ ⊢[PRAAx] le (J+j) N) (hI : Γ ⊢[PRAAx] le one I)
    (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k))
    (hw : Γ ⊢[PRAAx] C ≐ W) (ht : Γ ⊢[PRAAx] T ≐ W) (hs : Γ ⊢[PRAAx] le p (s+N)) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (damping s X Y D sign W (J+j) N R) (GaussianBinetKernelFrozenPrefix.value k I (W*(J+j)) N))
      (inst2 (offB cofinalBody) j (pairT J (originalData q N X Y D sign R T C)))
      (dampedNumerator p q I) (errorDenominator p q I) := by
  let A := W*(J+j)
  let data := GaussianBinetLaplaceExponential.data (n := n)
  let Exp := GaussianBinetLaplaceExponential.nameF
  have hd : Γ ⊢[PRAAx] data X Y D sign R T A N ≐ data X Y D sign R W A N := by
    simpa only [data,GaussianBinetLaplaceExponential.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var]
      using Prf.eqCongr1 (GaussianBinetLaplaceExponential.data (Syn.shift X) (Syn.shift Y) (Syn.shift D)
        (Syn.shift sign) (Syn.shift R) (var 0) (Syn.shift A) (Syn.shift N)) ht
  have e : Γ ⊢[PRAAx] ap2 Exp (s+N) (data X Y D sign R T A N) ≐ damping s X Y D sign W (J+j) N R :=
    congrAp2 Exp (.eqRefl (s+N)) hd
  have hwT : Γ ⊢[PRAAx] le W T := le_congr (.eqRefl W) ht.eqSymm (le_refl W)
  exact distance_congr (qmul_congr e (.eqRefl _))
    (offset_at cofinalBody J j (originalData q N X Y D sign R T C)).eqSymm (.eqRefl _) (.eqRefl _)
    (late_physical_row_error (J+j) (s+N) p q k I N X Y D sign R T C W h hN hj hI hk hwT hw hs)

end LeanProofs.IPRA.Analysis.GaussianBinetKernelFrequencyGrid
