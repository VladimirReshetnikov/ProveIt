import IPRADerivations.Analysis.GaussianBinetLaplaceRealFloor
import IPRADerivations.Analysis.GaussianBinetLaplaceStrip
import IPRADerivations.Analysis.GaussianCompactRiemannLower

/-!
# Positive mass of the original real Binet Laplace quadrature

The pointwise lower floor survives the actual affine quadrature and its
canonical observation clock. The original panel on [1,2] has an exact
positive rational margin at every sufficiently late observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceCompactRealFloor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceRealFloor (floor floorDenominator floor_denominator_positive sample_floor)
open GaussianBinetLaplaceStrip (Kernel evaluatorF nameF data source fixedData evaluator_at tagNumerator tag_inside)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName
  (quadrature grid grid_inside sampleBody sampleData sample_body_at precision mesh)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open PolynomialBisection (slack zle_scale_cancel)
open RationalArgmin (rationalLE)
open RationalGaussianRealPart (realBody)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper upper_congr upper_mono)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "F" => evaluatorF Kernel.cofinal
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "eight" => num 8

private theorem scalar_entry (p M X D R T A C E i : PTm n) :
    let t := grid i M (E+A) C E
    Γ ⊢[PRAAx] RationalFiniteSum.term (realBody (sampleBody F)) i
      (sampleData p M (E+A) C E (fixedData X zero D zero R T zero)) ≐
      fstT (ap2 GaussianBinetLaplaceIntegrand.cofinalF p
        (GaussianBinetLaplaceIntegrand.cofinalData X zero D zero R T (tagNumerator t) (sndT t))) := by
  dsimp only
  have row := (sample_body_at (Γ := Γ) F i p M (E+A) C E (fixedData X zero D zero R T zero)).eqTrans
    (evaluator_at Kernel.cofinal p (grid i M (E+A) C E) X zero D zero R T zero)
  simpa only [RationalFiniteSum.term,realBody,inst2,subst_fstT,
    GaussianBinetLaplaceStrip.integrandF,GaussianBinetLaplaceStrip.integrandData] using congrFst row

private theorem rows_floor (p M X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] GaussianCompactRiemannLower.rows (realBody (sampleBody F)) M
      (sampleData p M (E+A) C E (fixedData X zero D zero R T zero))
      two (floorDenominator X T) eight (unit p) := by
  let sh := fun q : PTm n => Syn.shift q
  let Δ := (lt (var 0 : PTm (n+1)) (sh M)) :: Γ.map Fm.shift
  have shifted : Γ.map Fm.shift ⊢[PRAAx] source (sh X) zero (sh D) zero (sh R) (sh T) (sh A) (sh C) (sh E) := by
    simpa [Fm.shift,sh,Syn.shift] using h.shift
  have meshPos : Γ.map Fm.shift ⊢[PRAAx] le one (sh M) := by
    simpa [Fm.shift,sh,Syn.shift,one] using hM.shift
  have hs : Δ ⊢[PRAAx] source (sh X) zero (sh D) zero (sh R) (sh T) (sh A) (sh C) (sh E) := shifted.wk
  let t := grid (var 0) (sh M) (sh E+sh A) (sh C) (sh E)
  have ht : Δ ⊢[PRAAx] GaussianCompactRiemannName.inside (sh E+sh A) (sh C) (sh E) t :=
    grid_inside _ _ _ _ _ (le_trans hs.andE₂.andE₁ (le_add_right _ _)) hs.andE₂.andE₁ meshPos.wk
      (le_of_lt Prf.hyp0)
  have time := tag_inside t (sh A) (sh C) (sh E) (sh T) hs.andE₂.andE₁ hs.andE₂.andE₂ ht
  have bound := sample_floor (sh p) (sh X) (sh D) (sh R) (sh T) (tagNumerator t) (sndT t)
    (.andI hs.andE₁ (.andI ht.andE₂.andE₁ time.andE₂))
  have out := upper_congr (.eqRefl _) (scalar_entry (sh p) (sh M) (sh X) (sh D) (sh R) (sh T)
    (sh A) (sh C) (sh E) (var 0)).eqSymm (.eqRefl _) (.eqRefl _) bound
  refine .allI (.impI ?_)
  simpa only [GaussianCompactRiemannName.subst_sampleData,GaussianCoefficientNameBounds.subst_unit,
    GaussianBinetLaplaceRealFloor.subst_floorDenominator,Syn.shift,sh,Δ,subst_pairT,
    PTm.subst_add,LeanProofs.IPRA.PTm.subst_num,two,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,floor] using out

theorem compact_floor (p X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) :
    Γ ⊢[PRAAx] upper (fraction (C*two) (E*floorDenominator X T))
      (fstT (ap2 (nameF Kernel.cofinal) p (data X zero D zero R T zero A C E)))
      (C*eight) (E*unit (precision p T)) := by
  let L := GaussianBinetLaplaceIntegrand.meshGain R T
  let M := mesh p L T
  let x := fixedData X zero D zero R T zero
  have hM := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have raw := GaussianCompactRiemannLower.left_sum_lower (sampleBody F) M
    (sampleData (precision p T) M (E+A) C E x) C E two (floorDenominator X T) eight
    (unit (precision p T)) h.andE₂.andE₁ hM (floor_denominator_positive X T)
    (rows_floor (precision p T) M X D R T A C E h hM)
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) F p (E+A) C E L T x
  exact upper_congr (.eqRefl _) (congrFst read).eqSymm (.eqRefl _) (.eqRefl _) raw

def unitPanelData (X D R : PTm n) : PTm n :=
  data X zero D zero R two zero one one one

@[simp] theorem subst_unitPanelData {m : ℕ} (σ : Fin n → PTm m) (X D R : PTm n) :
    Syn.subst σ (unitPanelData X D R) =
      unitPanelData (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ R) := by
  simp [unitPanelData,one,two]

theorem unit_panel_floor (p X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] upper (floor X two) (fstT (ap2 (nameF Kernel.cofinal) p (unitPanelData X D R))) eight (unit p) := by
  have src : Γ ⊢[PRAAx] source X zero D zero R two one one one :=
    .andI h (.andI (le_refl one) (le_of_eq_add (d := zero) (by ipra_ring)))
  have raw := compact_floor p X D R two one one one src
  have f : Γ ⊢[PRAAx] fraction (one*two) (one*floorDenominator X two) ≐ floor X two := by
    simpa only [floor,GaussianEuclideanDistanceName.subst_fraction,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (fraction (var 0) (var 1) : PTm 2)
        (σ := ![one*two,one*floorDenominator X two]) (σ' := ![two,floorDenominator X two])
        (fun i => by fin_cases i <;> apply one_mul)
  have canon := upper_congr f (.eqRefl _) (one_mul _) (one_mul _) raw
  exact upper_mono _ _ _ _ _ _ (unit_positive _) canon
    (le_mul_mono (le_refl eight) (GaussianExponentialReference.unit_monotone
      (le_trans (le_add_right p two) (le_add_right (p+two) (num 6)))))

theorem late_unit_panel_floor (p X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hp : Γ ⊢[PRAAx] le (eight*floorDenominator X two) (unit p)) :
    Γ ⊢[PRAAx] rationalLE (fraction one (floorDenominator X two))
      (fstT (ap2 (nameF Kernel.cofinal) p (unitPanelData X D R))) := by
  let B := floorDenominator X two
  let U := unit p
  let c := fstT (ap2 (nameF Kernel.cofinal) p (unitPanelData X D R))
  let E := denominatorOf c
  let v := numeratorOf c
  let l := RationalRepresentedUpper.left (ZT.ofNat two) E U
  let r := RationalRepresentedUpper.right v B E eight U
  have hB := floor_denominator_positive (Γ := Γ) X two
  have hu := RationalRepresentedUpper.to_signed _ c (ZT.ofNat two) v B E eight U
    (fraction_represents two B hB) (RationalRepresentations.represents_self c) (unit_panel_floor p X D R h)
  have el := zle_toZ hu
  have er := natEq (eq_add_of_le hp)
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _ (fraction_represents one B hB)
    (RationalRepresentations.represents_self c) hB (RationalArgmin.denominator_positive c)
  apply zle_scale_cancel (c := U) (unit_positive p)
  apply zle_of_toZ (slack l r+monus U (eight*B)*E)
  dsimp only [l,r] at *
  simp only [PolynomialBisection.slack,RationalRepresentedUpper.left,RationalRepresentedUpper.right,
    ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,Q.mk_add,map_mul,map_add] at el er ⊢
  ipra_simps
  linear_combination el - 𝔞(E)*er

theorem actual_real_Binet_unit_panel_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (realSource (var 1) zero (var 2) zero (var 3) ⟶
      le (eight*floorDenominator (var 1) two) (unit (var 0)) ⟶
      rationalLE (fraction one (floorDenominator (var 1) two))
        (fstT (ap2 (nameF Kernel.cofinal) (var 0) (unitPanelData (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (.impI (late_unit_panel_floor _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceCompactRealFloor
