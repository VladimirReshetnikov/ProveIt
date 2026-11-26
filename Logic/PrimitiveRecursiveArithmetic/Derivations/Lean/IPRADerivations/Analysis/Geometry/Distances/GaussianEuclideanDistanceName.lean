import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanPointDistance

/-!
# Actual Euclidean distance names and their finite cuts

The point evaluator is a fixed PR2 schema. The list, persistent data,
precisions and rational bounds remain numerical object-theory inputs.
Distance samples use the actual Euclidean minimum/square-root program at
point precision m+2 and square-root precision m+2. Point regularity is the
original Euclidean comparison, rather than a sup-metric substitution.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName

open_ipra
open LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalCover (hit hit_intro)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_radius_mono)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def fraction (A B : PTm n) : PTm n := normalize (ZT.ofNat A) B
def shifted (m : PTm n) : PTm n := m+two
def pointCN (point : PR 2) (x : PTm n) : Fm PTm n := .all (.all
  (distanceBounded (ap2 point (var 1) (Syn.shift (Syn.shift x)))
    (ap2 point (var 0) (Syn.shift (Syn.shift x))) (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))
def distanceSample (point : PR 2) (T x m : PTm n) : PTm n :=
  GaussianEuclideanPointDistance.lower (ap2 point (shifted m) x) T (shifted m)
def cutRadius (A B m : PTm n) : PTm n := RationalArithmetic.add (fraction A B) (fraction one (unit m))
def distanceLE (point : PR 2) (T x A B : PTm n) : Fm PTm n := .all
  (rationalLE (distanceSample point (Syn.shift T) (Syn.shift x) (var 0))
    (cutRadius (Syn.shift A) (Syn.shift B) (var 0)))
def fastScalar (point : PR 2) (T x : PTm n) : Fm PTm n := .all (.all
  (RationalValueBounds.radius (distanceSample point (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift x)) (var 1))
    (distanceSample point (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift x)) (var 0))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

ipra_subst fraction
ipra_subst shifted
ipra_subst pointCN [Syn.subst_shift, Syn.shift_subst]
ipra_subst distanceSample
ipra_subst cutRadius
ipra_subst distanceLE [Syn.subst_shift, Syn.shift_subst]
ipra_subst fastScalar [Syn.subst_shift, Syn.shift_subst]

ipra_subst hit [Fm.subst_ex, Fm.subst_and, subst_lt, subst_length, GaussianRationalMetric.subst_distanceBounded,
    subst_entry, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

/-- Preserve regularity under the addition of a fresh variable to the context. -/
theorem shift_pointCN {f : PR 2} {x : PTm n} (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
  simpa only [Fm.shift, subst_pointCN, Syn.shift] using h.shift

theorem fraction_represents (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fraction A B) (ZT.ofNat A) B := normalize_preserves_value _ _ hB

theorem fraction_order (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] le (D*A) (C*B)) : Γ ⊢[PRAAx] rationalLE (fraction A B) (fraction C D) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hB hD (fraction_represents _ _ hB) (fraction_represents _ _ hD) h

theorem cut_represents (A B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (cutRadius A B m) (ZT.ofNat (A*unit m+B)) (B*unit m) := by
  have h := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _
    (fraction_represents A B hB) (fraction_represents one (unit m) (unit_positive m))
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  ipra_lc

theorem cut_fraction (A B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    cutRadius A B m ≐ fraction (A*unit m+B) (B*unit m) := by
  have positive := positive_product (Γ := Γ) _ _ hB (unit_positive m)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ positive) (cut_represents A B m hB)
    (fraction_represents _ _ positive) positive positive
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]

theorem point_cn_at (point : PR 2) (x s t : PTm n) (h : Γ ⊢[PRAAx] pointCN point x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 point s x) (ap2 point t x) (unit s+unit t) (unit s*unit t) := by
  have pair : Γ ⊢[PRAAx] .all (distanceBounded (ap2 point (Syn.shift s) (Syn.shift x))
      (ap2 point (var 0) (Syn.shift x)) (unit (Syn.shift s)+unit (var 0)) (unit (Syn.shift s)*unit (var 0))) := by
    simpa only [pointCN,Fm.subst_all,GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_unit,
      PTm.subst_add,PTm.subst_mul,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
      Foundations.BoundedFormulas.subst_up_shift',Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE s
  simpa only [GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_unit,PTm.subst_add,PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using pair.allE t

theorem hit_radius_mono (z T A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hrad : Γ ⊢[PRAAx] le (A*D) (C*B)) (h : Γ ⊢[PRAAx] hit z T A B) : Γ ⊢[PRAAx] hit z T C D := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift T)) ⋏
    distanceBounded (Syn.shift z) (entry (Syn.shift T) (var 0)) (Syn.shift A) (Syn.shift B)
  have b : E :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift.wk
  have d : E :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hD.shift.wk
  have budget : E :: Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A*Syn.shift D) (Syn.shift C*Syn.shift B) := by
    simpa only [Fm.shift,subst_le,PTm.subst_mul,Syn.shift] using hrad.shift.wk
  have result := hit_intro (Syn.shift z) (Syn.shift T) (Syn.shift C) (Syn.shift D) (var 0)
    (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
    (distance_radius_mono _ _ _ _ _ _ b d budget (Prf.andE₂ Prf.hyp0))
  simpa only [E,Fm.shift,subst_hit,Syn.shift] using result

theorem hit_triangle (z y T A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hzy : Γ ⊢[PRAAx] distanceBounded z y A B) (h : Γ ⊢[PRAAx] hit y T C D) :
    Γ ⊢[PRAAx] hit z T (A*D+C*B) (B*D) := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift T)) ⋏
    distanceBounded (Syn.shift y) (entry (Syn.shift T) (var 0)) (Syn.shift C) (Syn.shift D)
  have b : E :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift.wk
  have d : E :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hD.shift.wk
  have distance : E :: Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift z) (Syn.shift y) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_distanceBounded,Syn.shift] using hzy.shift.wk
  have result := hit_intro (Syn.shift z) (Syn.shift T) _ _ (var 0)
    (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ b d distance (Prf.andE₂ Prf.hyp0))
  simpa only [E,Fm.shift,subst_hit,PTm.subst_add,PTm.subst_mul,Syn.shift] using result

theorem upper_of_representations (u v L E M F A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hF : Γ ⊢[PRAAx] le one F)
    (hu : Γ ⊢[PRAAx] RationalArithmetic.represents u (ZT.ofNat L) E)
    (hv : Γ ⊢[PRAAx] RationalArithmetic.represents v (ZT.ofNat M) F)
    (h : Γ ⊢[PRAAx] le (B*F*L) (B*M*E+A*E*F)) : Γ ⊢[PRAAx] RationalValueBounds.upper u v A B := by
  apply RationalValueBounds.positive_cancel (positive_product _ _ hE hF)
  refine le_of_eq_add (d := denominatorOf u*denominatorOf v*PTm.monus (B*M*E+A*E*F) (B*F*L)) ?_
  have eu := ZT.toZ_eq hu
  have ev := ZT.toZ_eq hv
  have gap := natEq (eq_add_of_le h)
  apply deriveNat
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at eu ev
  simp only [ZT.toZ] at eu ev
  unfold RationalValueBounds.crossLeft
  ipra_simps
  linear_combination 𝔞(B)*𝔞(F)*𝔞(denominatorOf v)*eu-
    𝔞(B)*𝔞(E)*𝔞(denominatorOf u)*ev+𝔞(denominatorOf u)*𝔞(denominatorOf v)*gap

/-- Actual finite Euclidean minima and their actual square-root samples
give this one-sided distance variation; no distance-name bound is supplied. -/
theorem lower_variation (z w T k l A B : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hB : Γ ⊢[PRAAx] le one B)
    (hzw : Γ ⊢[PRAAx] distanceBounded z w A B) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (GaussianEuclideanPointDistance.lower z T k)
      (GaussianEuclideanPointDistance.lower w T l) (A*unit l+B) (B*unit l) := by
  let L := GaussianEuclideanPointDistance.root w T l
  let E := GaussianEuclideanPointDistance.denominator w T*unit l
  have epos : Γ ⊢[PRAAx] le one E := positive_product _ _ (GaussianEuclideanPointDistance.denominator_positive w T) (unit_positive l)
  have actualHit := GaussianEuclideanPointDistance.lower_bound_to_hit w T l L E hT epos (RationalArgmin.reflexive _)
  have transported := hit_triangle z w T A B (L*unit l+E) (E*unit l) hB
    (positive_product _ _ epos (unit_positive l)) hzw actualHit
  have bound := GaussianEuclideanPointDistance.hit_to_lower_bound z T k _ _
    (positive_product _ _ hB (positive_product _ _ epos (unit_positive l))) transported
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianEuclideanPointDistance.lower_represents (Γ := Γ) z T k)
    (fraction_represents _ _ (positive_product _ _ hB (positive_product _ _ epos (unit_positive l)))) bound
  exact upper_of_representations _ _ _ _ L E _ _
    (positive_product _ _ (GaussianEuclideanPointDistance.denominator_positive z T) (unit_positive k)) epos
    (GaussianEuclideanPointDistance.lower_represents z T k) (GaussianEuclideanPointDistance.lower_represents w T l)
    (le_congr (by ipra_ring) (by ipra_ring) raw)

theorem unit_le_shift (m : PTm n) : Γ ⊢[PRAAx] le (unit m) (unit (shifted m)) :=
  GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (le_add_right m two)

theorem unit_shift (m : PTm n) : Γ ⊢[PRAAx] unit (shifted m) ≐ two*(two*unit m) := by
  have e : Γ ⊢[PRAAx] shifted m ≐ succ (succ m) := by unfold shifted; ipra_ring
  exact (congrAp2 powF e (.eqRefl _)).eqTrans
    ((pw_succ two (succ m)).eqTrans ((congrMul (pw_succ two m) (.eqRefl _)).eqTrans (by unfold unit; ipra_ring)))

theorem two_units_le_shift (m : PTm n) : Γ ⊢[PRAAx] le (two*unit m) (unit (shifted m)) :=
  le_congr (.eqRefl _) (unit_shift m).eqSymm (le_of_eq_add (d := two*unit m) (by ipra_ring))

theorem variation_budget (m l : PTm n) : Γ ⊢[PRAAx]
    le (((unit (shifted m)+unit (shifted l))*unit (shifted l)+unit (shifted m)*unit (shifted l))*(unit m*unit l))
      ((unit m+unit l)*((unit (shifted m)*unit (shifted l))*unit (shifted l))) := by
  have first := mul_le_mul_right (unit m*unit (shifted m)) (two_units_le_shift (Γ := Γ) l)
  have second := mul_le_mul_right (unit l*unit (shifted l)) (unit_le_shift (Γ := Γ) m)
  exact le_congr (by ipra_ring) (by ipra_ring)
    (mul_le_mul_right (unit (shifted l)) (add_le_add₂ first second))

theorem sample_upper (point : PR 2) (T x m l : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hT : Γ ⊢[PRAAx] le one (length T)) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (distanceSample point T x m) (distanceSample point T x l)
      (unit m+unit l) (unit m*unit l) :=
  RationalValueBounds.upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _))
    (lower_variation _ _ _ _ _ _ _ hT (positive_product _ _ (unit_positive _) (unit_positive _))
      (point_cn_at point x (shifted m) (shifted l) hCN)) (variation_budget m l)

theorem sample_radius (point : PR 2) (T x m l : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hT : Γ ⊢[PRAAx] le one (length T)) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (distanceSample point T x m) (distanceSample point T x l)
      (unit m+unit l) (unit m*unit l) :=
  RationalValueBounds.radius_of_upper _ _ _ _ (sample_upper _ _ _ _ _ hCN hT)
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
      (sample_upper _ _ _ _ _ hCN hT))

theorem sample_nonnegative (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx]
    le (numeratorOf (distanceSample point T x m)).neg (numeratorOf (distanceSample point T x m)).pos :=
  GaussianEuclideanPointDistance.lower_nonnegative _ _ _

theorem fast_scalar (point : PR 2) (T x : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hT : Γ ⊢[PRAAx] le one (length T)) : Γ ⊢[PRAAx] fastScalar point T x := by
  refine .allI (.allI ?_)
  have cn := shift_pointCN (shift_pointCN hCN)
  have nonempty : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (length (Syn.shift (Syn.shift T))) := by
    simpa only [Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hT.shift.shift
  exact sample_radius point _ _ (var 1) (var 0) cn nonempty

theorem distance_le_at (point : PR 2) (T x A B m : PTm n) (h : Γ ⊢[PRAAx] distanceLE point T x A B) : Γ ⊢[PRAAx]
    rationalLE (distanceSample point T x m) (cutRadius A B m) := by
  simpa only [distanceLE,RationalArgmin.subst_rationalLE,subst_distanceSample,subst_cutRadius,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE m

theorem cut_to_hit (point : PR 2) (T x A B m : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceLE point T x A B) : Γ ⊢[PRAAx]
    hit (ap2 point (shifted m) x) T (A*unit m+two*B) (B*unit m) := by
  have bpos := positive_product (Γ := Γ) _ _ hB (unit_positive m)
  have cut := RationalArgmin.rationalLE_congr (.eqRefl _) (cut_fraction A B m hB) (distance_le_at point T x A B m h)
  have actual := GaussianEuclideanPointDistance.lower_bound_to_hit (ap2 point (shifted m) x) T (shifted m)
    (A*unit m+B) (B*unit m) hT bpos cut
  have raw := mul_le_mul_right (B*B*unit m) (unit_le_shift (Γ := Γ) m)
  have budget : Γ ⊢[PRAAx] le
      (((A*unit m+B)*unit (shifted m)+B*unit m)*(B*unit m))
      ((A*unit m+two*B)*((B*unit m)*unit (shifted m))) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (A*B*unit m*unit m*unit (shifted m)+B*B*unit m*unit (shifted m)) raw)
  exact hit_radius_mono _ _ _ _ _ _ (positive_product _ _ bpos (unit_positive _)) bpos budget actual

theorem finite_hit_sample_bound (point : PR 2) (T x s a b A B m : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hb : Γ ⊢[PRAAx] le one b) (hB : Γ ⊢[PRAAx] le one B)
    (hHit : Γ ⊢[PRAAx] hit (ap2 point s x) T a b)
    (hBudget : Γ ⊢[PRAAx] le ((a*unit s+b)*B) (A*(b*unit s))) : Γ ⊢[PRAAx]
    rationalLE (distanceSample point T x m) (cutRadius A B m) := by
  have cn := point_cn_at point x (shifted m) s hCN
  have transferred := hit_triangle _ _ _ _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) hb cn hHit
  have first := mul_le_mul_right (unit (shifted m)*unit m) hBudget
  have second := mul_le_mul_right (B*b*unit s) (unit_le_shift (Γ := Γ) m)
  have budget : Γ ⊢[PRAAx] le
      (((unit (shifted m)+unit s)*b+a*(unit (shifted m)*unit s))*(B*unit m))
      ((A*unit m+B)*((unit (shifted m)*unit s)*b)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first second)
  have changed := hit_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) hb)
    (positive_product _ _ hB (unit_positive _)) budget transferred
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (cut_fraction A B m hB).eqSymm
    (GaussianEuclideanPointDistance.hit_to_lower_bound _ _ _ _ _ (positive_product _ _ hB (unit_positive _)) changed)

theorem finite_hit_to_cut (point : PR 2) (T x s a b A B : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hb : Γ ⊢[PRAAx] le one b) (hB : Γ ⊢[PRAAx] le one B)
    (hHit : Γ ⊢[PRAAx] hit (ap2 point s x) T a b)
    (hBudget : Γ ⊢[PRAAx] le ((a*unit s+b)*B) (A*(b*unit s))) : Γ ⊢[PRAAx] distanceLE point T x A B := by
  refine .allI ?_
  have cn := shift_pointCN hCN
  have bpos : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hb.shift
  have Bpos : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift
  have actual : Γ.map Fm.shift ⊢[PRAAx] hit (ap2 point (Syn.shift s) (Syn.shift x)) (Syn.shift T) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,subst_hit,subst_ap2,Syn.shift] using hHit.shift
  have budget : Γ.map Fm.shift ⊢[PRAAx] le
      ((Syn.shift a*unit (Syn.shift s)+Syn.shift b)*Syn.shift B)
      (Syn.shift A*(Syn.shift b*unit (Syn.shift s))) := by
    simpa only [Fm.shift,subst_le,PTm.subst_add,PTm.subst_mul,subst_unit,Syn.shift] using hBudget.shift
  exact finite_hit_sample_bound point (Syn.shift T) (Syn.shift x) (Syn.shift s) (Syn.shift a) (Syn.shift b)
    (Syn.shift A) (Syn.shift B) (var 0) cn bpos Bpos actual budget

theorem sample_zero_lower (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fraction zero one) (distanceSample point T x m) :=
  GaussianCoefficientNormOrder.zero_lower_of_nonnegative _ (sample_nonnegative point T x m)

theorem nonnegative_name (point : PR 2) (T x : PTm n) : Γ ⊢[PRAAx]
    .all (rationalLE (fraction zero one) (distanceSample point (Syn.shift T) (Syn.shift x) (var 0))) :=
  .allI (sample_zero_lower _ _ _ _)

/-- Reification retains the actual finite Euclidean argmin/square-root
program and both internal precision shifts. -/
def distanceSampleF (point : PR 2) : PR 3 := PTm.toPR (distanceSample point (var 0) (var 1) (var 2))
theorem sample_program (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx]
    ap3 (distanceSampleF point) T x m ≐ distanceSample point T x m := by
  simpa [distanceSampleF,ap3] using
    toPR_eq (Γ := Γ) (distanceSample point (var 0) (var 1) (var 2) : PTm 3) ![T,x,m]

theorem euclidean_distance_name_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN point (var 1) ⟶ le one (length (var 0)) ⟶
      (fastScalar point (var 0) (var 1) ⋏
        .all (rationalLE (fraction zero one)
          (distanceSample point (Syn.shift (var 0)) (Syn.shift (var 1)) (var 0))))) :=
  closeUniv 2 (.impI (.impI (.andI (fast_scalar _ _ _ Prf.hyp1 Prf.hyp0) (nonnegative_name _ _ _))))

theorem euclidean_distance_cut_to_hit_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 0)) ⟶ le one (var 3) ⟶ distanceLE point (var 0) (var 1) (var 2) (var 3) ⟶
      hit (ap2 point (shifted (var 4)) (var 1)) (var 0)
        (var 2*unit (var 4)+two*var 3) (var 3*unit (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (cut_to_hit _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem finite_hit_to_euclidean_cut_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (pointCN point (var 1) ⟶ le one (var 4) ⟶ le one (var 6) ⟶
      hit (ap2 point (var 2) (var 1)) (var 0) (var 3) (var 4) ⟶
        le ((var 3*unit (var 2)+var 4)*var 6) (var 5*(var 4*unit (var 2))) ⟶
          distanceLE point (var 0) (var 1) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (finite_hit_to_cut _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem finite_euclidean_distance_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (length (var 2)) ⟶ le one (var 6) ⟶ distanceBounded (var 0) (var 1) (var 5) (var 6) ⟶
      RationalValueBounds.upper (GaussianEuclideanPointDistance.lower (var 0) (var 2) (var 3))
        (GaussianEuclideanPointDistance.lower (var 1) (var 2) (var 4))
        (var 5*unit (var 4)+var 6) (var 6*unit (var 4))) :=
  closeUniv 7 (.impI (.impI (.impI (lower_variation _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem euclidean_distance_name_program_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (distanceSampleF point) (var 0) (var 1) (var 2) ≐ distanceSample point (var 0) (var 1) (var 2)) :=
  closeUniv 3 (sample_program _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName
