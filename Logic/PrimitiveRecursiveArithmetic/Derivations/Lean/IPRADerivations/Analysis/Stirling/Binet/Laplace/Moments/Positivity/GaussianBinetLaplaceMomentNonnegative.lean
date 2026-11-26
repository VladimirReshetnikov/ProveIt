import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.FiniteRows.GaussianBinetLaplaceMomentCompact
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# Nonnegative real part of every actual weighted Binet panel

The original real integrand's lower estimate and the nonnegative exact
time power give a one-sided dyadic bound, including at time zero. It
survives compact quadrature on arbitrary physical panels.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNonnegative

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData input)
open GaussianBinetLaplaceMomentCompact (data)
open GaussianBinetLaplaceMomentFloor (weight clock observation gain fixedData evaluatorF evaluator_at nameF)
open GaussianBinetLaplaceRealFloor (floor floorDenominator floor_denominator_positive sample_floor)
open GaussianBinetLaplaceStrip (source tagNumerator tag_inside)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid inside grid_inside sampleBody sampleData sample_body_at precision mesh)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product qmul)
open PolynomialBisection (slack)
open RationalGaussianRealPart (realBody)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper upper_congr upper_mono upper_order_left)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "eight" => num 8

private theorem weight_nonnegative (q A B W U : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hhi : Γ ⊢[PRAAx] le A (W*B)) (h : Γ ⊢[PRAAx] upper (fraction zero one) (fstT q) eight U) :
    Γ ⊢[PRAAx] upper (fraction zero one) (fstT (qmul q (radiusPoint A B))) (eight*W) U := by
  let v := numeratorOf (fstT q)
  let E := denominatorOf (fstT q)
  let w := radiusPoint A B
  let l := RationalRepresentedUpper.left (ZT.ofNat zero) E U
  let r := RationalRepresentedUpper.right v one E eight U
  have h1 : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl one
  have rep := RationalRepresentations.represents_self (Γ := Γ) (fstT q)
  have wrep := GaussianPositiveExponentialOrder.radius_real_representation A B hB
  have product := RationalRepresentations.represents_multiply _ _ _ _ _ _ rep wrep
  have re := GaussianPositiveExponentialProduct.real_product q w
    (GaussianPositiveExponentialTermBound.actual_positive_fraction A B hB).andE₁
  have scaled := GaussianRationalHorner.scalar_congr re.eqSymm (.eqRefl _) (.eqRefl _) product
  have original := RationalRepresentedUpper.to_signed _ _ _ _ _ _ _ _ (fraction_represents zero one h1) rep h
  have eq := zle_toZ original
  have hi := natEq (eq_add_of_le hhi)
  apply RationalRepresentedUpper.from_signed _ _ (ZT.ofNat zero) (v*ZT.ofNat A) one (E*B) (eight*W) U
    h1 (positive_product _ _ (RationalArgmin.denominator_positive _) hB) (fraction_represents zero one h1) scaled
  apply zle_of_toZ (A*slack l r+eight*E*monus (W*B) A)
  dsimp only [l,r] at *
  simp only [PolynomialBisection.slack,RationalRepresentedUpper.left,RationalRepresentedUpper.right,
    ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,Q.mk_add,map_mul,map_add] at eq hi ⊢
  ipra_simps
  linear_combination 𝔞(A)*eq - 8*𝔞(E)*hi

theorem observation_nonnegative (p j X D R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) :
    Γ ⊢[PRAAx] upper (fraction zero one) (fstT (observation p j X D R T A B)) eight (unit p) := by
  let W := pw T j
  let q := ap2 cofinalF (clock p j T) (cofinalData X zero D zero R T A B)
  have hB := GaussianPolynomialPerturbation.power_positive B j h.andE₂.andE₁
  have hi := le_congr (.eqRefl _) (pw_mul_base T B j) (pw_le_pw j h.andE₂.andE₂)
  have floorPos : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fraction zero one) (floor X T) :=
    GaussianEuclideanDistanceName.fraction_order zero one two (floorDenominator X T) (le_refl one)
      (floor_denominator_positive X T) (by ipra_le 2)
  have base := upper_order_left _ _ _ _ _ floorPos (sample_floor (clock p j T) X D R T A B h)
  have raw := weight_nonnegative q (pw A j) (pw B j) W (unit (clock p j T)) hB hi base
  have budget := GaussianFastValueCut.query_budget (Γ := Γ) W p
  exact upper_mono _ _ _ _ _ _ (unit_positive _) raw
    (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl eight) budget))

private theorem zero_fraction (C E : PTm n) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] fraction (C*zero) (E*one) ≐ fraction zero one := by
  have hD := positive_product _ _ hE (le_refl one)
  have h1 : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl one
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hD) (RationalNormalForm.normalize_well_formed _ _ h1)
    (fraction_represents _ _ hD) (fraction_represents _ _ h1) hD h1
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem lower_rows (p M j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] GaussianCompactRiemannLower.rows (realBody (sampleBody evaluatorF)) M
      (sampleData p M (E+A) C E (fixedData j X D R T)) zero one eight (unit p) := by
  let s (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (s M)::Γ.map Fm.shift
  let t := grid (var 0) (s M) (s E+s A) (s C) (s E)
  let x := fixedData (s j) (s X) (s D) (s R) (s T)
  have hs : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift.wk
  have hm : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hM.shift.wk
  have e := hs.andE₂.andE₁
  have ht : Δ ⊢[PRAAx] inside (s E+s A) (s C) (s E) t :=
    grid_inside _ _ _ _ _ (le_trans e (le_add_right _ _)) e hm (le_of_lt Prf.hyp0)
  have time := tag_inside t (s A) (s C) (s E) (s T) e hs.andE₂.andE₂ ht
  have raw := observation_nonnegative (s p) (s j) (s X) (s D) (s R) (s T) (tagNumerator t) (sndT t)
    (.andI hs.andE₁ (.andI ht.andE₂.andE₁ time.andE₂))
  have val := (sample_body_at (Γ := Δ) evaluatorF (var 0) (s p) (s M) (s E+s A) (s C) (s E) x).eqTrans
    (evaluator_at (s p) t (s j) (s X) (s D) (s R) (s T))
  have eq : Δ ⊢[PRAAx] RationalFiniteSum.term (realBody (sampleBody evaluatorF)) (var 0)
      (sampleData (s p) (s M) (s E+s A) (s C) (s E) x) ≐
      fstT (observation (s p) (s j) (s X) (s D) (s R) (s T) (tagNumerator t) (sndT t)) := by
    simpa only [RationalFiniteSum.term,realBody,inst2,subst_fstT] using congrFst val
  refine .allI (.impI ?_)
  simpa only [GaussianCompactRiemannName.subst_sampleData,GaussianCoefficientNameBounds.subst_unit,
    GaussianBinetLaplaceMomentFloor.subst_fixedData,Syn.shift,s,Δ,x,PTm.subst_add,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,LeanProofs.IPRA.PTm.subst_num]
    using upper_congr (.eqRefl _) eq.eqSymm (.eqRefl _) (.eqRefl _) raw

theorem panel_nonnegative (p j X D R T A C E : PTm n) (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) :
    Γ ⊢[PRAAx] upper (fraction zero one) (fstT (ap2 nameF p (data j X D R T A C E))) one (unit p) := by
  let L := gain j R T
  let M := mesh p L T
  let q := precision p T
  let x := fixedData j X D R T
  have hM := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have e := h.andE₂.andE₁
  have raw := GaussianCompactRiemannLower.left_sum_lower (sampleBody evaluatorF) M
    (sampleData q M (E+A) C E x) C E zero one eight (unit q) e hM (le_refl one)
    (lower_rows q M j X D R T A C E h hM)
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF p (E+A) C E L T x
  have next := upper_congr (zero_fraction C E e) (congrFst read).eqSymm (.eqRefl _) (.eqRefl _) raw
  have six : Γ ⊢[PRAAx] unit (num 6) ≐ num 64 := LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 6
  have eightLe : Γ ⊢[PRAAx] le (eight : PTm n) (unit (num 6)) :=
    le_congr (.eqRefl _) six.eqSymm (by ipra_le 56)
  have power : Γ ⊢[PRAAx] le (eight*unit p) (unit (p+num 6)) :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two p (num 6)).eqSymm)
      (mul_le_mul_right (unit p) eightLe)
  have width : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left C A) h.andE₂.andE₂
  have pad : Γ ⊢[PRAAx] le ((C*eight)*unit p) (E*unit q) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono width power))
      (le_mul_mono (le_refl _) (GaussianCompactRiemannName.precision_lower p T))
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ e (unit_positive q)) next
    (le_congr (.eqRefl _) (one_mul _).eqSymm pad)

theorem actual_weighted_Binet_panel_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) zero (var 3) zero (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      upper (fraction zero one) (fstT (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)
        (var 5) (var 6) (var 7) (var 8)))) one (unit (var 0))) :=
  closeUniv 9 (.impI (panel_nonnegative _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNonnegative
