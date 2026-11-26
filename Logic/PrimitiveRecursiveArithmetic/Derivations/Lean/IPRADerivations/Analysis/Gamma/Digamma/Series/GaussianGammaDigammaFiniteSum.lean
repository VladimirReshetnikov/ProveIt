import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaRecurrence
import IPRADerivations.Analysis.Series.Telescoping.GaussianRationalParameterTelescope

/-!
# Finite reciprocal sums for the original digamma name

Summing the actual adjacent differences yields the finite identity
ψ(x+N) − ψ(x) = Σ_{0≤j<N} 1/(x+j). The local error is 5/2^p and
the finite sum uses the original Gaussian rational arithmetic.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaFiniteSum

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaRecurrence (digamma_shift)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNameRingLaws (three)
open GaussianNamedDifference (difference_distance)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (canonical qadd ofGaussian_canonical positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalParameterTelescope (forward forward_at forward_sum)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalSyntheticDivision (qadd_congr qadd_sub_cancel)
open GaussianStirlingGammaLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "SF" => GaussianNamedDifference.nameF DF DF

def index (a b j : PTm n) : PTm n := a+j*b
def sampleBody : PTm 2 :=
  ap2 DF (fstT (var 1)) (dd (index (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0))
    (sndT (sndT (var 1))))
def reciprocalBody : PTm 2 :=
  fraction (sndT (var 1)) (index (fstT (var 1)) (sndT (var 1)) (var 0))
def reciprocalSum (a b N : PTm n) : PTm n := sum reciprocalBody N (pairT a b)
def differenceData (a b N : PTm n) : PTm n := GaussianNamedDifference.data (dd (index a b N) b) (dd a b)
def budget (N : PTm n) : PTm n := num 6+N*num 5

ipra_subst index
ipra_subst reciprocalSum
ipra_subst differenceData
ipra_subst budget

theorem row_source (a b j : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] source (index a b j) b :=
  .andI (le_trans hs.andE₁ (le_add_right _ _)) hs.andE₂

private theorem index_congr {a a' b b' j j' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') (hj : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] index a b j ≐ index a' b' j' :=
  congrAdd ha (congrMul hj hb)

private theorem datum_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] dd a b ≐ dd a' b' := by
  simpa only [GaussianGammaDigammaNative.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (dd (var 0) (var 1) : PTm 2) (σ := ![a,b]) (σ' := ![a',b'])
      (fun j => by fin_cases j; exact ha; exact hb)

theorem reciprocal_entry (a b j : PTm n) : Γ ⊢[PRAAx]
    inst2 reciprocalBody j (pairT a b) ≐ fraction b (index a b j) := by
  change Γ ⊢[PRAAx] Syn.subst ![j,pairT a b] reciprocalBody ≐ _
  simp only [reciprocalBody,GaussianPositiveRationalLogarithm.subst_fraction,subst_index,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,subst_fstT,subst_sndT]
  exact GaussianCompactRiemannName.fraction_congr _ _ _ _ (snd_pair _ _)
    (index_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _))

theorem sample_entry (p a b j : PTm n) : Γ ⊢[PRAAx]
    inst2 sampleBody j (pairT p (pairT a b)) ≐ ap2 DF p (dd (index a b j) b) := by
  let y := pairT p (pairT a b)
  change Γ ⊢[PRAAx] Syn.subst ![j,y] sampleBody ≐ _
  simp only [sampleBody,subst_ap2,GaussianGammaDigammaNative.subst_data,subst_index,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,subst_fstT,subst_sndT]
  have hb := (congrSnd (snd_pair (Γ := Γ) p (pairT a b))).eqTrans (snd_pair a b)
  have ha := (congrFst (snd_pair (Γ := Γ) p (pairT a b))).eqTrans (fst_pair a b)
  exact congrAp2 DF (fst_pair _ _) (datum_congr (index_congr ha hb (.eqRefl _)) hb)

theorem step_error (p a b j : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded
      (qsub (ap2 DF p (dd (index a b (succ j)) b)) (ap2 DF p (dd (index a b j) b)))
      (fraction b (index a b j)) (num 5) (unit p) := by
  let c := index a b j
  let d := index a b (succ j)
  let X := ap2 DF p (dd c b)
  let Y := ap2 DF p (dd d b)
  let M := GaussianGammaDigammaRecurrence.nameF
  let v := GaussianGammaDigammaRecurrence.data c b
  let r := fraction b c
  have h := row_source a b j hs
  have hp := unit_positive (Γ := Γ) p
  have hd : Γ ⊢[PRAAx] c+b ≐ d := by unfold c d index; ipra_ring
  have step := distance_congr (congrAp2 DF (.eqRefl _) (datum_congr hd (.eqRefl _))) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (cross_at _ _ _ _ p p (digamma_shift c b h))
  have step' : Γ ⊢[PRAAx] distanceBounded Y (ap2 M p v) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp (le_of_eq_add (d := zero) (by ipra_ring)) step
  have raw := distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p r)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.add_sample_error DF constantF (dd c b) r p
      (GaussianGammaDigammaNative.name_regular c b h) (constant_regular r))
  have joined := distance_triangle_same _ _ _ _ _ _ hp step' raw
  have cancel := difference_distance _ _ _ _ _ _ _ hp joined
    (GaussianRationalPowerDifference.distance_refl_zero X (unit p) hp)
  have cr : Γ ⊢[PRAAx] canonical r := ofGaussian_canonical _ _ h.andE₁
  exact distance_congr (.eqRefl _) (qadd_sub_cancel X r cr) (by unfold three; ipra_ring) (.eqRefl _) cancel

theorem finite_sample_error (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded
      (qsub (ap2 DF p (dd (index a b N) b)) (ap2 DF p (dd a b)))
      (reciprocalSum a b N) (N*num 5) (unit p) := by
  let x := pairT p (pairT a b)
  let y := pairT a b
  have cols : Γ ⊢[PRAAx] termsDistance (forward sampleBody) reciprocalBody N x y (num 5) (unit p) := by
    refine .allI (.impI ?_)
    have shifted : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
      simpa only [Fm.shift,Syn.shift,GaussianStirlingGammaLogarithm.subst_source] using hs.shift
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let k : PTm (n+1) := var 0
    have row := step_error (Γ := Δ) (Syn.shift p) (Syn.shift a) (Syn.shift b) k shifted.wk
    have actual := distance_congr
      (GaussianRationalSyntheticDivision.qsub_congr (sample_entry (Syn.shift p) (Syn.shift a) (Syn.shift b) (succ k))
        (sample_entry (Syn.shift p) (Syn.shift a) (Syn.shift b) k)).eqSymm
      (reciprocal_entry (Syn.shift a) (Syn.shift b) k).eqSymm (.eqRefl _) (.eqRefl _) row
    simpa only [termsDistance,Syn.shift,subst_pairT,PTm.subst_num,GaussianCoefficientNameBounds.subst_unit,
      x,y,Δ,k,forward_at] using actual
  have raw := sum_distance (forward sampleBody) reciprocalBody N x y (num 5) (unit p) (unit_positive p) cols
  have start : Γ ⊢[PRAAx] index a b zero ≐ a := by unfold index; ipra_ring
  have namedStart := (sample_entry (Γ := Γ) p a b zero).eqTrans (congrAp2 DF (.eqRefl _) (datum_congr start (.eqRefl _)))
  exact distance_congr ((forward_sum sampleBody N x).eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr (sample_entry p a b N) namedStart)) (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

set_option maxHeartbeats 800000 in
theorem finite_reciprocal_sum (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent SF constantF (differenceData a b N) (reciprocalSum a b N) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (budget N)
    (GaussianNamedDifference.name_regular DF DF _ _ (GaussianGammaDigammaNative.name_regular _ _ (row_source a b N hs))
      (GaussianGammaDigammaNative.name_regular a b hs)) (constant_regular _) (.allI ?_)
  let a' := Syn.shift a
  let b' := Syn.shift b
  let N' := Syn.shift N
  let p : PTm (n+1) := var 0
  have h : Γ.map Fm.shift ⊢[PRAAx] source a' b' := by
    simpa only [Fm.shift,Syn.shift,a',b',GaussianStirlingGammaLogarithm.subst_source] using hs.shift
  have finite := finite_sample_error p a' b' N' h
  have norm := GaussianNamedDifference.sample_error DF DF (dd (index a' b' N') b') (dd a' b') p
    (GaussianGammaDigammaNative.name_regular _ _ (row_source a' b' N' h)) (GaussianGammaDigammaNative.name_regular a' b' h)
  have combined := distance_triangle_same _ _ _ _ _ _ (unit_positive p) norm finite
  have result : Γ.map Fm.shift ⊢[PRAAx] distanceBounded
      (ap2 SF p (differenceData a' b' N')) (ap2 constantF p (reciprocalSum a' b' N')) (budget N') (unit p) :=
    distance_congr (.eqRefl _) (constant_at p (reciprocalSum a' b' N')).eqSymm
      (.eqRefl _) (.eqRefl _) combined
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_differenceData,subst_reciprocalSum,
    subst_budget,a',b',N',p] using result

theorem actual_original_finite_digamma_reciprocal_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ crossEquivalent SF constantF
      (differenceData (var 0) (var 1) (var 2)) (reciprocalSum (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (finite_reciprocal_sum _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaFiniteSum
