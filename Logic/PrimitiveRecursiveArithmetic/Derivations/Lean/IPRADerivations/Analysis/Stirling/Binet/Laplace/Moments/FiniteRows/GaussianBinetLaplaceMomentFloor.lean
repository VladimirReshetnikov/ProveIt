import IPRADerivations.Analysis.Stirling.Binet.Laplace.Integrands.GaussianBinetLaplaceCompactRealFloor
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripCutoff

/-!
# Positive mass for every natural moment of the real Binet integrand

The time weight is the exact natural rational power. A single clock
depending on the horizon pays for amplification by that weight. On
[1,2] every weight is at least one, so the original lower floor again
survives the canonical compact quadrature.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentFloor

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceRealFloor (floor floorDenominator floor_denominator_positive sample_floor_with_cap numerator_cap)
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData input meshGain)
open GaussianBinetLaplaceStrip (Kernel tagNumerator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid sampleBody sampleData sample_body_at precision mesh)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product qmul)
open PolynomialBisection (slack zle_scale_cancel)
open RationalArgmin (rationalLE)
open RationalGaussianRealPart (realBody)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper upper_congr upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "baseF" => GaussianBinetLaplaceStrip.evaluatorF Kernel.cofinal
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "eight" => num 8

def weight (j A B : PTm n) : PTm n := radiusPoint (pw A j) (pw B j)
def clock (p j T : PTm n) : PTm n := GaussianFastValueCut.exponent (pw T j) p
def observation (p j X D R T A B : PTm n) : PTm n :=
  qmul (ap2 cofinalF (clock p j T) (cofinalData X zero D zero R T A B)) (weight j A B)

ipra_subst weight

ipra_subst clock

ipra_subst observation

private theorem weighted_floor (q A B W C U : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] le one C) (hlo : Γ ⊢[PRAAx] le B A) (hhi : Γ ⊢[PRAAx] le A (W*B))
    (h : Γ ⊢[PRAAx] upper (fraction two C) (fstT q) eight U) :
    Γ ⊢[PRAAx] upper (fraction two C) (fstT (qmul q (radiusPoint A B))) (eight*W) U := by
  let v := numeratorOf (fstT q)
  let E := denominatorOf (fstT q)
  let w := radiusPoint A B
  let l := RationalRepresentedUpper.left (ZT.ofNat two) E U
  let r := RationalRepresentedUpper.right v C E eight U
  have rep := RationalRepresentations.represents_self (Γ := Γ) (fstT q)
  have wrep := GaussianPositiveExponentialOrder.radius_real_representation A B hB
  have product := RationalRepresentations.represents_multiply _ _ _ _ _ _ rep wrep
  have re := GaussianPositiveExponentialProduct.real_product q w
    (GaussianPositiveExponentialTermBound.actual_positive_fraction A B hB).andE₁
  have scaled := GaussianRationalHorner.scalar_congr re.eqSymm (.eqRefl _) (.eqRefl _) product
  have original := RationalRepresentedUpper.to_signed _ _ _ _ _ _ _ _ (fraction_represents two C hC) rep h
  have eq := zle_toZ original
  have lower := natEq (eq_add_of_le hlo)
  have upper := natEq (eq_add_of_le hhi)
  apply RationalRepresentedUpper.from_signed _ _ (ZT.ofNat two) (v*ZT.ofNat A) C (E*B) (eight*W) U
    hC (positive_product _ _ (RationalArgmin.denominator_positive _) hB) (fraction_represents two C hC) scaled
  apply zle_of_toZ (A*slack l r+two*E*U*monus A B+eight*C*E*monus (W*B) A)
  dsimp only [l,r] at *
  simp only [PolynomialBisection.slack,RationalRepresentedUpper.left,RationalRepresentedUpper.right,
    ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,Q.mk_add,map_mul,map_add] at eq lower upper ⊢
  ipra_simps
  linear_combination 𝔞(A)*eq - 2*𝔞(E)*𝔞(U)*lower - 8*𝔞(C)*𝔞(E)*upper

theorem observation_floor_with_cap (p j X D R T A B S : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) (hlo : Γ ⊢[PRAAx] le B A)
    (hCap : Γ ⊢[PRAAx] le X (S*D)) :
    Γ ⊢[PRAAx] upper (floor S T) (fstT (observation p j X D R T A B)) eight (unit p) := by
  let W := pw T j
  let q := ap2 cofinalF (clock p j T) (cofinalData X zero D zero R T A B)
  have hB := GaussianPolynomialPerturbation.power_positive B j h.andE₂.andE₁
  have low := pw_le_pw j hlo
  have high := le_congr (.eqRefl _) (pw_mul_base T B j) (pw_le_pw j h.andE₂.andE₂)
  have raw := weighted_floor q (pw A j) (pw B j) W (floorDenominator S T) (unit (clock p j T))
    hB (floor_denominator_positive S T) low high (sample_floor_with_cap (clock p j T) X D R T A B S h hCap)
  have budget := GaussianFastValueCut.query_budget (Γ := Γ) W p
  exact RationalValueBounds.upper_mono_scaled (unit_positive _) budget raw

theorem observation_floor (p j X D R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) (hlo : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] upper (floor X T) (fstT (observation p j X D R T A B)) eight (unit p) :=
  observation_floor_with_cap p j X D R T A B X h hlo (numerator_cap X D h.andE₁.andE₁.andE₂)

def fixedData (j X D R T : PTm n) : PTm n :=
  pairT j (pairT T (GaussianBinetLaplaceStrip.fixedData X zero D zero R T zero))

def evaluatorTerm (p t x : PTm n) : PTm n :=
  qmul (ap3 baseF (clock p (fstT x) (fstT (sndT x))) t (sndT (sndT x)))
    (weight (fstT x) (tagNumerator t) (sndT t))

def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF
def gain (j R T : PTm n) : PTm n := pw T j*meshGain R T+j*pw T (pred j)

def unitPanelData (j X D R : PTm n) : PTm n :=
  GaussianCompactRiemannName.data (one+one) one one (gain j R two) two (fixedData j X D R two)

ipra_subst fixedData

ipra_subst evaluatorTerm [GaussianBinetLaplaceStrip.tagNumerator]

ipra_subst gain

ipra_subst unitPanelData [one, two]

theorem evaluator_at (p t j X D R T : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (fixedData j X D R T) ≐
      observation p j X D R T (tagNumerator t) (sndT t) := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 2)
    (qmul (ap3 baseF (clock (var 0) (var 2) (var 3)) (var 1) (var 4))
        (weight (var 2) (tagNumerator (var 1)) (sndT (var 1)))) p t ![j, T, GaussianBinetLaplaceStrip.fixedData X zero D zero R T zero]
  simp only [GaussianRationalHorner.subst_qmul, subst_ap3, subst_clock, subst_weight,
    GaussianBinetLaplaceStrip.subst_tagNumerator, subst_sndT, Syn.subst_var] at read
  exact read.eqTrans (GaussianRationalSyntheticDivision.qmul_congr
    (GaussianBinetLaplaceStrip.evaluator_at Kernel.cofinal (clock p j T) t X zero D zero R T zero)
    (.eqRefl _))

private theorem unit_rows (p M j X D R S : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hM : Γ ⊢[PRAAx] le one M) (hCap : Γ ⊢[PRAAx] le X (S*D)) : Γ ⊢[PRAAx]
    GaussianCompactRiemannLower.rows (realBody (sampleBody evaluatorF)) M
      (sampleData p M (one+one) one one (fixedData j X D R two)) two (floorDenominator S two) eight (unit p) := by
  let sh := fun q : PTm n => Syn.shift q
  let Δ := (lt (var 0 : PTm (n+1)) (sh M)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (sh X) zero (sh D) zero (sh R) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] realSource (sh X) zero (sh D) zero (sh R) := by
      simpa [Fm.shift,Syn.shift,sh] using h.shift
    exact e.wk
  have meshPos : Δ ⊢[PRAAx] le one (sh M) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh M) := by simpa [Fm.shift,Syn.shift,sh,one] using hM.shift
    exact e.wk
  have cap : Δ ⊢[PRAAx] le (sh X) (sh S*sh D) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_le,PTm.subst_mul] using hCap.shift.wk
  let t := grid (var 0) (sh M) (one+one) one one
  have fields := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Δ) (var 0) (sh M) one one one
  have hi : Δ ⊢[PRAAx] le (var 0) (sh M) := le_of_lt Prf.hyp0
  have hb : Δ ⊢[PRAAx] le one (sndT t) := le_congr (.eqRefl _) ((one_mul _).eqSymm.eqTrans fields.andE₂.eqSymm) meshPos
  have hlo : Δ ⊢[PRAAx] le (sndT t) (tagNumerator t) := le_congr fields.andE₂.eqSymm fields.andE₁.eqSymm (le_add_right _ _)
  have first : Δ ⊢[PRAAx] sh M+var 0 ≐ tagNumerator t :=
    (by ipra_ring : Δ ⊢[PRAAx] sh M+var 0 ≐ one*sh M+one*var 0).eqTrans fields.andE₁.eqSymm
  have hhi : Δ ⊢[PRAAx] le (tagNumerator t) (two*sndT t) :=
    le_congr first
      ((by ipra_ring : Δ ⊢[PRAAx] sh M+sh M ≐ two*(one*sh M)).eqTrans
        (congrMul (.eqRefl _) fields.andE₂.eqSymm))
      (add_le_add₂ (le_refl (sh M)) hi)
  have bound := observation_floor_with_cap (sh p) (sh j) (sh X) (sh D) (sh R) two (tagNumerator t) (sndT t) (sh S)
    (.andI hs (.andI hb hhi)) hlo cap
  let x := fixedData (sh j) (sh X) (sh D) (sh R) two
  have val := (sample_body_at (Γ := Δ) evaluatorF (var 0) (sh p) (sh M) (one+one) one one x).eqTrans
    (evaluator_at (sh p) t (sh j) (sh X) (sh D) (sh R) two)
  have eq : Δ ⊢[PRAAx] RationalFiniteSum.term (realBody (sampleBody evaluatorF)) (var 0)
      (sampleData (sh p) (sh M) (one+one) one one x) ≐
      fstT (observation (sh p) (sh j) (sh X) (sh D) (sh R) two (tagNumerator t) (sndT t)) := by
    simpa only [RationalFiniteSum.term,realBody,inst2,subst_fstT] using congrFst val
  have out := upper_congr (.eqRefl _) eq.eqSymm (.eqRefl _) (.eqRefl _) bound
  refine .allI (.impI ?_)
  simpa only [GaussianCompactRiemannName.subst_sampleData,GaussianCoefficientNameBounds.subst_unit,
    GaussianBinetLaplaceRealFloor.subst_floorDenominator,subst_fixedData,Syn.shift,sh,Δ,x,PTm.subst_add,
    LeanProofs.IPRA.PTm.subst_num,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,floor] using out

theorem unit_panel_floor_with_cap (p j X D R S : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hCap : Γ ⊢[PRAAx] le X (S*D)) :
    Γ ⊢[PRAAx] upper (floor S two) (fstT (ap2 nameF p (unitPanelData j X D R))) eight (unit p) := by
  let L := gain j R two
  let M := mesh p L two
  let q := precision p two
  let x := fixedData j X D R two
  have hM := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L two
  have raw := GaussianCompactRiemannLower.left_sum_lower (sampleBody evaluatorF) M
    (sampleData q M (one+one) one one x) one one two (floorDenominator S two) eight (unit q)
    (le_refl one) hM (floor_denominator_positive S two) (unit_rows q M j X D R S h hM hCap)
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF p (one+one) one one L two x
  have f : Γ ⊢[PRAAx] fraction (one*two) (one*floorDenominator S two) ≐ floor S two :=
    RationalNonnegativePowers.fraction_congr (one_mul _) (one_mul _)
  have canon := upper_congr f (congrFst read).eqSymm (one_mul _) (one_mul _) raw
  exact RationalValueBounds.upper_mono_den (unit_positive _)
    (GaussianExponentialReference.unit_monotone (le_trans (le_add_right p two) (le_add_right (p+two) (num 6)))) canon

theorem unit_panel_floor (p j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] upper (floor X two) (fstT (ap2 nameF p (unitPanelData j X D R))) eight (unit p) :=
  unit_panel_floor_with_cap p j X D R X h (numerator_cap X D h.andE₁.andE₂)

/-- A sufficiently late scalar observation keeps at least half of its
certified positive rational floor. -/
theorem fraction_half_lower_at (p c A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hp : Γ ⊢[PRAAx] le (A*B) (unit p)) (h : Γ ⊢[PRAAx] upper (fraction two B) c A (unit p)) :
    Γ ⊢[PRAAx] rationalLE (fraction one B) c := by
  let U := unit p
  let E := denominatorOf c
  let v := numeratorOf c
  let l := RationalRepresentedUpper.left (ZT.ofNat two) E U
  let r := RationalRepresentedUpper.right v B E A U
  have hu := RationalRepresentedUpper.to_signed _ c (ZT.ofNat two) v B E A U
    (fraction_represents two B hB) (RationalRepresentations.represents_self c) h
  have el := zle_toZ hu
  have er := natEq (eq_add_of_le hp)
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _ (fraction_represents one B hB)
    (RationalRepresentations.represents_self c) hB (RationalArgmin.denominator_positive c)
  apply zle_scale_cancel (c := U) (unit_positive p)
  apply zle_of_toZ (slack l r+monus U (A*B)*E)
  dsimp only [l,r] at *
  simp only [PolynomialBisection.slack,RationalRepresentedUpper.left,RationalRepresentedUpper.right,
    ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,Q.mk_add,map_mul,map_add] at el er ⊢
  ipra_simps
  linear_combination el - 𝔞(E)*er

theorem late_unit_panel_floor_with_cap (p j X D R S : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hCap : Γ ⊢[PRAAx] le X (S*D))
    (hp : Γ ⊢[PRAAx] le (eight*floorDenominator S two) (unit p)) :
    Γ ⊢[PRAAx] rationalLE (fraction one (floorDenominator S two))
      (fstT (ap2 nameF p (unitPanelData j X D R))) := by
  exact fraction_half_lower_at p _ eight _ (floor_denominator_positive S two) hp
    (unit_panel_floor_with_cap p j X D R S h hCap)

theorem late_unit_panel_floor (p j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hp : Γ ⊢[PRAAx] le (eight*floorDenominator X two) (unit p)) :
    Γ ⊢[PRAAx] rationalLE (fraction one (floorDenominator X two))
      (fstT (ap2 nameF p (unitPanelData j X D R))) :=
  late_unit_panel_floor_with_cap p j X D R X h (numerator_cap X D h.andE₁.andE₂) hp

theorem actual_real_Binet_natural_moment_unit_panel_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (realSource (var 2) zero (var 3) zero (var 4) ⟶
      le (eight*floorDenominator (var 2) two) (unit (var 0)) ⟶
      rationalLE (fraction one (floorDenominator (var 2) two))
        (fstT (ap2 nameF (var 0) (unitPanelData (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (.impI (late_unit_panel_floor _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentFloor
