import IPRADerivations.Analysis.Integration.GaussianOddMomentWholeLine
import IPRADerivations.Analysis.Integration.GaussianOddMomentAbsoluteGrid

/-!
# Whole-line absolute convergence and cancellation for odd Gaussian moments

Both whole-line samples use the same reflected cofinal cut and affine
mesh. The absolute sample sums the literal absolute values of the
previous signed rows. Comparison with twice the original quadratic
positive-half name includes its checked lower and upper omitted tails.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianOddMomentWholeAbsolute

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianOddMomentIntegrand (argument radius)
open GaussianOddMomentSignedGrid (evaluatorF)
open GaussianOddMomentAbsoluteGrid (absF)
open GaussianOddMomentWholeLine (clock lowerDenominator upperEndpoint span query count gridWith halfData)
open GaussianOddSymmetricQuadrature (fixedData)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_trans cross_symm point_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def finiteSample (p N c d : PTm n) : PTm n := qadd (gridWith (absF false) p N c d) (gridWith (absF true) p N c d)
def sample (p N c d : PTm n) : PTm n := finiteSample (clock p) N c d
def data (N c d : PTm n) : PTm n := fixedData N c d
private def body : PTm 2 := sample (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def nameF : PR 2 := PTm.toPR body

abbrev positiveHalfF : PR 2 := GaussianOddMomentWholeLine.halfF
abbrev doubledF : PR 2 := addF positiveHalfF positiveHalfF
def doubledData (N c d : PTm n) : PTm n := addData (halfData N c d) (halfData N c d)
abbrev valueF : PR 2 := addF GaussianOddMomentWholeLine.referenceF GaussianOddMomentWholeLine.referenceF
def valueData (N c d : PTm n) : PTm n :=
  addData (GaussianOddMomentWholeLine.referenceData N c d) (GaussianOddMomentWholeLine.referenceData N c d)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N c d : PTm n) :
    Syn.subst σ (data N c d) = data (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ d) := by simp [data]
@[simp] theorem subst_doubledData {m : ℕ} (σ : Fin n → PTm m) (N c d : PTm n) :
    Syn.subst σ (doubledData N c d) = doubledData (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [doubledData,halfData]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p N c d : PTm n) :
    Syn.subst σ (sample p N c d) = sample (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [sample,finiteSample,clock,GaussianEvenMomentWholeLine.clock,gridWith,query,count,span,lowerDenominator,upperEndpoint,
    GaussianOddMomentWholeLine.cutoff,GaussianEulerQuadraticImproperKernel.invBound,GaussianEulerQuadraticCutoffGeometry.width,
    GaussianEulerQuadraticUpperEndpoint.preimage,GaussianGammaIntegralCutoffs.etaDen,GaussianGammaIntegralCutoffs.height,
    GaussianGammaIntegralCutoffs.top,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem sample_at (p N c d : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data N c d) ≐ sample p N c d := by
  let x := data N c d
  have e : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p (fstT x) (fstT (sndT x)) (sndT (sndT x)) := by
    simpa only [nameF,body,ap2,subst_sample,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
      using toPR_eq (Γ := Γ) body ![p,x]
  have r : Γ ⊢[PRAAx] sndT x ≐ pairT c d := snd_pair N (pairT c d)
  let template : PTm 4 := sample (var 0) (var 1) (var 2) (var 3)
  let left : Fin 4 → PTm n := ![p,fstT x,fstT (sndT x),sndT (sndT x)]
  let right : Fin 4 → PTm n := ![p,N,c,d]
  have bodyAt (σ : Fin 4 → PTm n) : Syn.subst σ template = sample (σ 0) (σ 1) (σ 2) (σ 3) := by
    simp only [template,subst_sample,Syn.subst_var]
  have h : Γ ⊢[PRAAx] Syn.subst left template ≐ Syn.subst right template :=
    Prf.eqCongr template (σ := left) (σ' := right) (fun i => by
      fin_cases i
      · exact .eqRefl p
      · exact fst_pair N (pairT c d)
      · exact (congrFst r).eqTrans (fst_pair c d)
      · exact (congrSnd r).eqTrans (snd_pair c d))
  rw [bodyAt left,bodyAt right] at h
  exact e.eqTrans h

private theorem unit_succ_succ (p : PTm n) : Γ ⊢[PRAAx] unit (succ (succ p)) ≐ num 4*unit p := by
  unfold unit
  exact (pw_succ two (succ p)).eqTrans ((congrMul (pw_succ two p) (.eqRefl _)).eqTrans (by ipra_ring))

theorem finite_absolute_half_error (p N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] distanceBounded (gridWith (evaluatorF false) p N c d) (gridWith (absF false) p N c d) one (unit p) := by
  let E := lowerDenominator p N c d
  let W := span p N c d
  let T := upperEndpoint p N c d
  let q := query p N c d
  let U := unit q
  let V := unit p
  have geometry := GaussianOddMomentWholeLine.grid_source p N c d hc hd
  have e := GaussianOddMomentAbsoluteGrid.absolute_grid_distance q (count p N c d) one W E N c d (le_refl one)
    geometry.andE₁.andE₁ (GaussianOddMomentWholeLine.count_positive p N c d) hd
  have h : Γ ⊢[PRAAx] le (succ (succ p)) (succ p+num 6) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_add_right (succ (succ p)) (num 5))
  have budget := GaussianOddMomentWholeLine.query_budget p N c d (num 4*V)
    (le_congr (unit_succ_succ p) (.eqRefl _) (GaussianCompactRiemannName.dyadic_monotone _ _ h))
  have widthBound := le_trans (le_add_left W one) geometry.andE₁.andE₂.andE₂
  have compare : Γ ⊢[PRAAx] le ((num 4*W)*V) (one*(E*U)) := by
    ipra_le 4*𝔞 V*sl widthBound+𝔞 E*sl budget
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ geometry.andE₁.andE₁ (unit_positive q))
    (unit_positive p) compare e

theorem finite_absolute_error (p N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] distanceBounded (finiteSample p N c d)
      (qadd (ap2 positiveHalfF p (halfData N c d)) (ap2 positiveHalfF p (halfData N c d))) (num 4) (unit p) := by
  let A := ap2 positiveHalfF p (halfData N c d)
  let B := gridWith (evaluatorF false) p N c d
  let C := gridWith (absF false) p N c d
  let V := unit p
  have hV : Γ ⊢[PRAAx] le one V := unit_positive p
  have e := distance_triangle_same A B C one one V hV (GaussianOddMomentWholeLine.finite_half_error p N c d hc hd)
    (finite_absolute_half_error p N c d hc hd)
  have sum := sum_distance A C A C (one+one) (one+one) V hV e e
  have reflected : Γ ⊢[PRAAx] finiteSample p N c d ≐ qadd C C :=
    qadd_congr (.eqRefl _) (GaussianOddMomentAbsoluteGrid.absolute_grid_reflected _ _ _ _ _ _)
  exact distance_congr reflected.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) (distance_symmetric _ _ _ _ hV sum)

private theorem unit_clock (p : PTm n) : Γ ⊢[PRAAx] unit (clock p) ≐ num 8*unit p := by
  change Γ ⊢[PRAAx] unit (succ (succ (succ p))) ≐ num 8*unit p
  exact (pw_succ two (succ (succ p))).eqTrans
    ((congrMul (unit_succ_succ p) (.eqRefl _)).eqTrans (by ipra_ring))

theorem half_regular (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] pointCN positiveHalfF (halfData N c d) :=
  GaussianEulerQuadraticImproperKernel.name_regular (argument N) (radius N) one one c d
    (GaussianOddMomentIntegrand.quadratic_source N c d hc hd)

theorem absolute_at (p q N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data N c d)) (ap2 doubledF q (doubledData N c d))
      (unit p+unit q) (unit p*unit q) := by
  let s := clock p
  let U := unit s
  let P := unit p
  let Q := unit q
  let H := halfData N c d
  let A := sample p N c d
  let B := qadd (ap2 positiveHalfF s H) (ap2 positiveHalfF s H)
  let C := ap2 doubledF s (doubledData N c d)
  let D := ap2 doubledF q (doubledData N c d)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive s
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive q
  have hUQ := positive_product (Γ := Γ) _ _ hU hQ
  have reg := half_regular N c d hc hd
  have full : Γ ⊢[PRAAx] pointCN doubledF (doubledData N c d) := add_fast _ _ _ _ reg reg
  have first : Γ ⊢[PRAAx] distanceBounded A B (num 4) U := finite_absolute_error s N c d hc hd
  have middle : Γ ⊢[PRAAx] distanceBounded B C (num 3) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
      (distance_symmetric _ _ _ _ hU (GaussianNameRingLaws.add_sample_error positiveHalfF positiveHalfF H H s reg reg))
  have initial : Γ ⊢[PRAAx] distanceBounded A C (num 7) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same A B C (num 4) (num 3) U hU first middle)
  have corrected : Γ ⊢[PRAAx] distanceBounded A C (num 7*Q) (U*Q) :=
    distance_radius_mono _ _ _ _ _ _ hU hUQ (by ipra_le 0) initial
  have distance : Γ ⊢[PRAAx] distanceBounded C D (U+Q) (U*Q) :=
    point_at doubledF (doubledData N c d) s q full
  have total := distance_triangle_same A C D (num 7*Q) (U+Q) (U*Q) hUQ corrected distance
  have scale := natEq (unit_clock (Γ := Γ) p)
  have final : Γ ⊢[PRAAx] distanceBounded A D (P+Q) (P*Q) :=
    distance_radius_mono _ _ _ _ _ _ hUQ (positive_product _ _ hP hQ)
      (by ipra_le 0 with (𝔞 Q)^2*scale) total
  exact distance_congr (sample_at p N c d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) final

theorem whole_absolute (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent nameF doubledF (data N c d) (doubledData N c d) := by
  refine .allI (.allI ?_)
  have hc' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift c)) := by
    simpa [Fm.shift,Syn.shift,one] using hc.shift.shift
  have hd' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift d)) := by
    simpa [Fm.shift,Syn.shift,one] using hd.shift.shift
  simpa only [crossEquivalent,Syn.shift,subst_data,subst_doubledData] using
    absolute_at (var 1) (var 0) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) hc' hd'

theorem absolute_value (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent nameF valueF (data N c d) (valueData N c d) := by
  let H := halfData N c d
  let F := GaussianOddMomentWholeLine.referenceF
  let Y := GaussianOddMomentWholeLine.referenceData N c d
  have hH := half_regular N c d hc hd
  have h := GaussianEulerQuadraticImproperKernel.original_Euler_cross (argument N) (radius N) one one c d
    (GaussianOddMomentIntegrand.quadratic_source N c d hc hd)
  have hY : Γ ⊢[PRAAx] pointCN F Y := cross_trans F positiveHalfF F Y H Y (cross_symm _ _ _ _ h) h
  have replacement := GaussianNameArithmetic.add_equivalent positiveHalfF F positiveHalfF F H Y H Y
    hH hY hH hY (cross_to_diagonal _ _ _ _ h) (cross_to_diagonal _ _ _ _ h)
  exact cross_trans _ _ _ _ _ _ (whole_absolute N c d hc hd) replacement

theorem actual_original_whole_line_Gaussian_odd_absolute_convergence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 1) ⟶ le one (var 2) ⟶
        crossEquivalent nameF valueF (data (var 0) (var 1) (var 2)) (valueData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (absolute_value _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_whole_line_Gaussian_odd_zero_with_absolute_convergence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 2) ⟶ le one (var 3) ⟶
        (GaussianOddMomentWholeLine.sample (var 0) (var 1) (var 2) (var 3) ≐ qzero) ⋏
        crossEquivalent nameF valueF (data (var 1) (var 2) (var 3)) (valueData (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.andI (GaussianOddMomentWholeLine.signed_sample_exact_zero _ _ _ _)
    (absolute_value _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianOddMomentWholeAbsolute
