import IPRADerivations.Analysis.Gamma.Digamma.GaussianDigammaFirstBernoulliPanelSum
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderHarmonicIntegral
import IPRADerivations.Analysis.RationalArithmetic.RationalSumSegments

/-!
# Exact harmonic mass correction on the original digamma panel

On the same mesh BQ, the left first-power mass and the original
factorial-harmonic interval differ by the two reciprocal endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliHarmonic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open GaussianStirlingAllOrderHarmonicIntegral (sum_at_original)
open GaussianStirlingAllOrderPanelPartsFinite (weightBody weight_at weightAt parameters)
open GaussianStirlingAllOrderPanelPartsRecurrence (panelMass fullMass)
open GaussianStirlingAllOrderPanelRotation (nextBody next_term rotate)
open GaussianStirlingAllOrderReciprocalGridError (gridDen)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalAlgebra (add_congr multiply_congr)
open RationalArithmetic (add multiply)
open RationalFiniteSum (sum term termwiseEq sum_ext canonical_equal)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalNormalForm (normalize_well_formed)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def harmonicBody : PTm 2 := scaledBody (weightBody 1)

def harmonicData (U B Q : PTm n) : PTm n := pairT (fraction one (B*Q)) (parameters U B (B*Q))

private theorem row_at (U B Q r : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] term harmonicBody r (harmonicData U B Q) ≐ fraction one (Q*U+r) := by
  let M := B*Q
  let D := gridDen U B M r
  let K := Q*U+r
  have hM := positive_product _ _ hB hQ
  have hK := le_trans (positive_product _ _ hQ hU) (le_add_right (Q*U) r)
  have hD := le_trans (positive_product _ _ hU hM) (le_add_right (U*M) (B*r))
  have weight : Γ ⊢[PRAAx] weightAt 1 U B M r ≐ fraction (B*M) D :=
    fraction_congr (pw_one _) (pw_one _)
  have atRow := (scaled_term (Γ := Γ) (weightBody 1) r (fraction one M) (parameters U B M)).eqTrans
    (multiply_congr (.eqRefl _) ((weight_at 1 U B M r).eqTrans weight))
  refine atRow.eqTrans ((fraction_multiply _ _ _ _ hM hD).eqTrans ?_)
  have hE := positive_product _ _ hM hD
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hE) (normalize_well_formed _ _ hK)
    (fraction_represents _ _ hE) (fraction_represents _ _ hK) hE hK
  apply ZT.derive
  have eq : Γ ⊢[PRAAx] (one*(B*M))*K ≐ one*(M*D) := by dsimp [D,K,M,gridDen]; ipra_ring
  simpa only [ZT.toZ_mul,ZT.toZ_ofNat,D,M,K,gridDen,IPRA.Q.mk_mul,map_mul] using natEq eq

private theorem right_sum (U B Q : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] sum (nextBody harmonicBody) (B*Q) (harmonicData U B Q) ≐
      RationalReciprocalPowerTail.tail one (Q*U) (B*Q) := by
  apply sum_ext
  refine .allI (.impI ?_)
  let i : PTm (n+1) := var 0
  let sh (v : PTm n) := Syn.shift v
  let Δ := lt i (Syn.shift (B*Q)) :: Γ.map Fm.shift
  have lift (v : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Δ ⊢[PRAAx] le one (sh v) := by
    simpa [Δ,sh,Fm.shift,Syn.shift,one] using hv.shift.wk
  have l := row_at (sh U) (sh B) (sh Q) (succ i) (lift _ hU) (lift _ hB) (lift _ hQ)
  have r := RationalReciprocalPowerTail.term_at (Γ := Δ) one (sh Q*sh U) i
  have e : Δ ⊢[PRAAx] sh Q*sh U+succ i ≐ pw (succ (sh Q*sh U+i)) one :=
    (add_succ _ _).eqTrans (pw_one _).eqSymm
  have h : Δ ⊢[PRAAx] term (nextBody harmonicBody) i (harmonicData (sh U) (sh B) (sh Q)) ≐
      term RationalReciprocalPowerTail.body i (RationalReciprocalPowerTail.data one (sh Q*sh U)) := by
    rw [next_term]
    exact l.eqTrans ((fraction_congr (.eqRefl _) e).eqTrans r.eqSymm)
  simpa [Δ,sh,i,termwiseEq,Syn.shift,harmonicData,RationalReciprocalPowerTail.data,one] using
    RationalArgmin.rationalEq_congr h.eqSymm (.eqRefl _) (.eqRefl _)

theorem exact_harmonic_mass (U B Q : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] add (panelMass 1 U B (B*Q)) (fraction one (Q*(U+B))) ≐
      add (fraction one (Q*U)) (RationalHarmonicInterval.interval (U+B) U Q) := by
  let M := B*Q
  let x := harmonicData U B Q
  have before : Γ ⊢[PRAAx] sum harmonicBody M x ≐ panelMass 1 U B M := sum_homogeneous _ _ _ _
  have right := (right_sum U B Q hU hB hQ).eqTrans
    ((RationalSumSegments.sum_congr RationalReciprocalPowerTail.body (mul_comm B Q) (.eqRefl _)).eqTrans
      (sum_at_original U B Q))
  have first := (row_at U B Q zero hU hB hQ).eqTrans (fraction_congr (.eqRefl _) (LeanProofs.IPRA.add_zero _))
  have last : Γ ⊢[PRAAx] term harmonicBody M x ≐ fraction one (Q*(U+B)) :=
    (row_at U B Q M hU hB hQ).eqTrans (fraction_congr (.eqRefl _) (by dsimp [M]; ipra_ring))
  exact (add_congr before.eqSymm last.eqSymm).eqTrans
    ((rotate harmonicBody M x).eqTrans (add_congr first right))

theorem actual_first_digamma_harmonic_mesh_correction_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 2))) ⟶
      add (panelMass 1 (var 0) (var 1) (var 1*var 2)) (fraction one (var 2*(var 0+var 1))) ≐
        add (fraction one (var 2*var 0)) (RationalHarmonicInterval.interval (var 0+var 1) (var 0) (var 2))) :=
  closeUniv 3 (.impI (exact_harmonic_mass _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliHarmonic
